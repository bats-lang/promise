#!/bin/sh
# Static tests: code that must not type-check, and code that must. A
# fixture is a snippet put into a copy of this checkout, in the file
# named in its `file`, before the line equal to its `before`. Each under accept/ must pass
# `bats check`; each under reject/ must fail it with the message in its
# `expect`.
# usage: tests/static/run.sh <repository-dir>
set -eu
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
fail=0
check() {
  n=$(basename "$1"); w="$TMP/w-$n"; mkdir -p "$w"
  (cd "$ROOT" && tar cf - --exclude=./dist .) | (cd "$w" && tar xf -)
  f="$w/$(cat "$1/file")"; before=$(cat "$1/before")
  grep -qxF -- "$before" "$f" || { echo "no line \"$before\" in $(cat "$1/file")" > "$TMP/$n.log"; return 2; }
  awk -v before="$before" -v snip="$1/snippet.bats" '
    $0 == before && !done { while ((getline l < snip) > 0) print l; print ""; done = 1 }
    { print }' "$f" > "$f.new" && mv "$f.new" "$f"
  (cd "$w" && bats check --repository "$2") > "$TMP/$n.log" 2>&1
}
for d in "$ROOT"/tests/static/accept/*/; do
  [ -d "$d" ] || continue; n=$(basename "$d")
  if check "$d" "$1"; then echo "ok   accept/$n"
  else echo "FAIL accept/$n: should type-check"; grep -E 'error|no line' "$TMP/$n.log" | head -5; fail=1; fi
done
for d in "$ROOT"/tests/static/reject/*/; do
  [ -d "$d" ] || continue; n=$(basename "$d")
  if check "$d" "$1"; then echo "FAIL reject/$n: should be rejected"; fail=1
  elif grep -qF -- "$(cat "$d/expect")" "$TMP/$n.log"; then echo "ok   reject/$n ($(cat "$d/expect"))"
  else echo "FAIL reject/$n: rejected, but not with: $(cat "$d/expect")"; grep -E 'error' "$TMP/$n.log" | head -8; fail=1; fi
done
exit $fail
