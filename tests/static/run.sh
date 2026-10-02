#!/bin/sh
# Static tests: code that must not type-check, and code that must. A
# fixture is a snippet put into a copy of this checkout, in the file
# named in its `file`, before the line equal to its `before`. Each under accept/ must pass
# `bats check`; each under reject/ must fail it with the message in its
# `expect`.
# Last, every match in the source and the fixtures must be case+.
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
# Every match is `case+`: a plain `case` (or `case-`) is not checked
# for exhaustiveness, so a choice could lose a case unseen. Comments,
# strings and inline C (%{ ... %}, whose switch has its own `case`) are
# skipped.
plain_cases=$(python3 - "$ROOT" <<'PY'
import pathlib, re, sys
root = pathlib.Path(sys.argv[1])
for path in sorted(root.glob("src/**/*.bats")) + sorted(root.glob("tests/**/*.bats")):
    text = path.read_text()
    kept, i, depth, line = [], 0, 0, 1
    while i < len(text):
        two = text[i:i + 2]
        if depth == 0 and two == "%{":
            end = text.find("%}", i + 2)
            end = len(text) if end < 0 else end + 2
            kept.append("\n" * text.count("\n", i, end)); i = end; continue
        if two == "(*":
            depth += 1; i += 2; continue
        if depth and two == "*)":
            depth -= 1; i += 2; continue
        if depth:
            kept.append("\n" if text[i] == "\n" else " "); i += 1; continue
        if two == "//":
            end = text.find("\n", i)
            i = len(text) if end < 0 else end; continue
        if text[i] == '"':
            end = i + 1
            while end < len(text) and text[end] != '"':
                end += 2 if text[end] == "\\" else 1
            kept.append("\n" * text.count("\n", i, end)); i = end + 1; continue
        kept.append(text[i]); i += 1
    for number, source in enumerate("".join(kept).split("\n"), 1):
        if re.search(r"(?<![\w$])case(?![\w+])", source):
            print(f"{path.relative_to(root)}:{number}: {source.strip()}")
PY
)
if [ -n "$plain_cases" ]; then
  echo "FAIL case+: a match without + is not checked for exhaustiveness:"
  echo "$plain_cases"; fail=1
else echo "ok   every match is case+"; fi
exit $fail
