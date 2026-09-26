(* promise -- linear async promises for bats *)
(* Each promise must be consumed exactly once. *)
(* State machine: Pending -> Resolved -> Chained *)

#include "share/atspre_staload.hats"

(* ============================================================
   States (int-indexed to avoid datasort export issues)
   ============================================================ *)

#pub stadef Pending = 0
#pub stadef Resolved = 1
#pub stadef Chained = 2

(* ============================================================
   Types
   ============================================================ *)

#pub absvtype promise(a:t@ype, s:int)

#pub vtypedef promise_pending(a:t@ype) = promise(a, Pending)
#pub vtypedef promise_resolved(a:t@ype) = promise(a, Resolved)

#pub absvtype resolver(a:t@ype)

(* ============================================================
   Creation
   ============================================================ *)

#pub fun{a:t@ype}
create
  (): @(promise(a, Pending), resolver(a))

#pub fun{a:t@ype}
resolved
  (v: a): promise(a, Resolved)

#pub fun{a:t@ype}
ret
  (v: a): promise(a, Chained)

(* ============================================================
   Resolution -- consumes the resolver
   ============================================================ *)

#pub fun{a:t@ype}
resolve
  (r: resolver(a), v: a): void

(* ============================================================
   Consumption
   ============================================================ *)

#pub fun{a:t@ype}
extract
  (p: promise(a, Resolved)): a

#pub fun{a:t@ype} {s:int}
discard
  (p: promise(a, s)): void

(* Monadic bind *)
#pub fun{a:t@ype}{b:t@ype}
and_then
  {s:int}
  (p: promise(a, s),
   f: (a) -<cloptr1> promise(b, Chained)
  ): promise(b, Chained)

(* Pending -> Chained. The identity: a promise's state is only in its
   type (promise(a, s) is one representation for every s). *)
#pub fn vow {a:t@ype}
  (p: promise(a, Pending)): promise(a, Chained)

(* ============================================================
   Resolver stash -- stores resolver in table, returns int ID.
   A stashed resolver is fired from JS, which can send any int, so
   its value is Int ([v:int] int v): the receiver's own checks then
   bound it statically, with no cast.
   ============================================================ *)

#pub fun stash
  (r: resolver(Int)): int

#pub fun fire
  (id: int, value: Int): void

(* ============================================================
   C runtime -- the stash table JS fires resolvers through
   ============================================================ *)

$UNSAFE begin
%{#
#ifndef _PROMISE_RUNTIME_DEFINED
#define _PROMISE_RUNTIME_DEFINED
/* Resolver stash: slot i holds a stashed resolver until it is fired.
   The table doubles when full, so stash always returns a live id. */
static void **_promise_resolver_table = 0;
static int _promise_resolver_cap = 0;

static int _promise_resolver_stash(void *resolver) {
  int i;
  for (i = 0; i < _promise_resolver_cap; i++) {
    if (!_promise_resolver_table[i]) {
      _promise_resolver_table[i] = resolver;
      return i;
    }
  }
  {
    int cap = _promise_resolver_cap ? 2 * _promise_resolver_cap : 16;
    void **t = (void **)malloc(cap * (int)sizeof(void *));
    memset(t, 0, cap * sizeof(void *));
    if (_promise_resolver_cap) {
      memcpy(t, _promise_resolver_table, _promise_resolver_cap * sizeof(void *));
      free(_promise_resolver_table);
    }
    _promise_resolver_table = t;
    i = _promise_resolver_cap;
    _promise_resolver_cap = cap;
    _promise_resolver_table[i] = resolver;
    return i;
  }
}

static void *_promise_resolver_unstash(int id) {
  void *r;
  if (id < 0 || id >= _promise_resolver_cap) return (void*)0;
  r = _promise_resolver_table[id];
  _promise_resolver_table[id] = (void*)0;
  return r;
}
#endif
%}
end

(* ============================================================
   Implementation
   ============================================================ *)

local

(* What runs when a pending promise's value arrives. *)
vtypedef cont(a:t@ype) = (a) -<lincloptr1> void

(* The cell a pending promise shares with its resolver. refs counts the
   live handles (2 from create: the promise and the resolver); the last
   one to let go frees it. value is set by resolve when no continuation
   waits; cont is set by and_then when no value has arrived. *)
datavtype cell(a:t@ype) =
  | CELL of (int, Option_vt(a), Option_vt(cont(a)))

(* A promise either holds its value outright or shares a cell with a
   resolver. A Pending promise always has a resolver; a Resolved one
   never does. *)
datavtype pro(a:t@ype, int) =
  | {s:int | s != Pending} PVAL(a, s) of (a)
  | {s:int | s != Resolved} PCELL(a, s) of (cell(a))

$UNSAFE begin
  assume promise(a, s) = pro(a, s)
  assume resolver(a) = cell(a)
end

(* Call a continuation once, then free its closure. *)
fn{a:t@ype} run_cont(k: cont(a), v: a): void = let
  val () = k(v)
in
  cloptr_free($UNSAFE begin $UNSAFE.castvwtp0{cloptr0}(k) end)
end

fn{a:t@ype} drop_cont(k: Option_vt(cont(a))): void =
  case+ k of
  | ~Some_vt(f) => cloptr_free($UNSAFE begin $UNSAFE.castvwtp0{cloptr0}(f) end)
  | ~None_vt() => ()

fn{a:t@ype} drop_value(v: Option_vt(a)): void =
  case+ v of
  | ~Some_vt(_) => ()
  | ~None_vt() => ()

(* Let go of one handle on a cell: free it if it was the last one. *)
fn{a:t@ype} release(c: cell(a)): void = let
  val+ @CELL(refs, _, _) = c
in
  if refs <= 1 then let
    prval () = fold@(c)
    val+ ~CELL(_, v, k) = c
    val () = drop_value<a>(v)
  in drop_cont<a>(k) end
  else let
    val () = refs := refs - 1
    prval () = fold@(c)
    val _ = $UNSAFE begin $UNSAFE.castvwtp0{ptr}(c) end
  in end
end

(* Give a cell's promise handle a continuation: run it now if the value
   is already there, else leave it for resolve. Consumes the handle. *)
fn{a:t@ype} on_value(c: cell(a), k: cont(a)): void = let
  val+ @CELL(_, value, old) = c
  val v = value
  val () = value := None_vt{a}()
in
  case+ v of
  | ~Some_vt(x) => let
      prval () = fold@(c)
      val () = release<a>(c)
    in run_cont<a>(k, x) end
  | ~None_vt() => let
      val o = old
      val () = old := Some_vt{cont(a)}(k)
      prval () = fold@(c)
      val () = drop_cont<a>(o)
    in release<a>(c) end
end

(* Resolve r with whatever q settles to. *)
fn{b:t@ype} forward(q: pro(b, Chained), r: cell(b)): void =
  case+ q of
  | ~PVAL(v) => resolve<b>(r, v)
  | ~PCELL(c) => on_value<b>(c, llam (y: b): void =<lincloptr1> resolve<b>(r, y))

in

(* --- Creation --- *)

implement{a}
create() = let
  val c = CELL{a}(2, None_vt{a}(), None_vt{cont(a)}())
  val r = $UNSAFE begin $UNSAFE.castvwtp1{cell(a)}(c) end
in @(PCELL(c), r) end

implement{a}
resolved(v) = PVAL(v)

implement{a}
ret(v) = PVAL(v)

(* --- Resolution --- *)

implement{a}
resolve(r, v) = let
  val+ @CELL(_, value, k) = r
  val kk = k
  val () = k := None_vt{cont(a)}()
in
  case+ kk of
  | ~Some_vt(f) => let
      prval () = fold@(r)
      val () = release<a>(r)
    in run_cont<a>(f, v) end
  | ~None_vt() => let
      val old = value
      val () = value := Some_vt{a}(v)
      prval () = fold@(r)
      val () = drop_value<a>(old)
    in release<a>(r) end
end

(* --- Consumption --- *)

implement{a}
extract(p) = let
  val+ ~PVAL(v) = p
in v end

implement{a}{s}
discard(p) =
  case+ p of
  | ~PVAL(_) => ()
  | ~PCELL(c) => release<a>(c)

(* --- State coercion --- *)

implement vow{a}(p) = let
  val+ ~PCELL(c) = p
in PCELL(c) end

(* --- Monadic bind --- *)

implement{a}{b}
and_then{s}(p, f) =
  case+ p of
  | ~PVAL(v) => let
      val q = f(v)
      val () = cloptr_free($UNSAFE begin $UNSAFE.castvwtp0{cloptr0}(f) end)
    in q end
  | ~PCELL(c) => let
      val @(q, r) = create<b>()
      val () = on_value<a>(c, llam (x: a): void =<lincloptr1> let
          val inner = f(x)
          val () = cloptr_free($UNSAFE begin $UNSAFE.castvwtp0{cloptr0}(f) end)
        in forward<b>(inner, r) end)
    in vow(q) end

(* --- Stash --- *)

implement
stash(r) = $UNSAFE begin
  $extfcall(int, "_promise_resolver_stash", $UNSAFE.castvwtp0{ptr}(r))
end

implement
fire(id, value) = let
  val r = $UNSAFE begin $extfcall(ptr, "_promise_resolver_unstash", id) end
in
  if ptr_isnot_null(r) then
    resolve<Int>($UNSAFE begin $UNSAFE.castvwtp0{cell(Int)}(r) end, value)
  else ()
end

end (* local *)

(* ============================================================
   Static tests -- type-system exercised by bats check
   ============================================================ *)

fn _test_create_resolve_extract(): void = let
  val @(p, r) = create<int>()
  val () = resolve<int>(r, 42)
  val () = discard<int>(p)
in () end

fn _test_resolved_extract(): void = let
  val p = resolved<int>(99)
  val v = extract<int>(p)
in () end

fn _test_create_discard(): void = let
  val @(p, r) = create<int>()
  val () = discard<int>(p)
  val () = resolve<int>(r, 0)
in () end

fn _test_stash_fire(): void = let
  val @(p, r) = create<Int>()
  val id = stash(r)
  val () = fire(id, 7)
  val () = discard<Int>(p)
in () end

(* A value fired from JS is bounded by the receiver's checks alone *)
fn _test_fired_value_bounded(): void = let
  val @(p, r) = create<Int>()
  val id = stash(r)
  val q = and_then<Int><int>(p, lam (n) =>
    if n <= 0 then ret<int>(0)
    else if n > 1024 then ret<int>(0)
    else let
      val m: [k:pos | k <= 1024] int k = n
    in ret<int>(m) end)
  val () = fire(id, 5)
  val () = discard<int>(q)
in () end

fn _test_vow(): void = let
  val @(p, r) = create<int>()
  val pc : promise(int, Chained) = vow(p)
  val () = discard<int>(pc)
  val () = resolve<int>(r, 0)
in () end
