(* promise -- linear async promises for bats *)
(* Each promise must be consumed exactly once, and so is its value: a
   payload is a vt@ype, so a linear value (a datavtype, a blob) rides a
   promise and is given to exactly one consumer. A value no consumer
   takes (the promise discarded before it resolved, or resolved and
   then discarded) is given to dispose, which each payload type
   implements; a non-linear payload's dispose does nothing. *)
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

#pub absvtype promise(a:vt@ype, s:int)

#pub vtypedef promise_pending(a:vt@ype) = promise(a, Pending)
#pub vtypedef promise_resolved(a:vt@ype) = promise(a, Resolved)

#pub absvtype resolver(a:vt@ype)

(* Frees a payload no consumer took. Each payload type implements it:
   nothing for a value with nothing to free (int, Int and bool here),
   a free for a linear one (a datavtype, a blob). It is read where a
   value enters a promise (create, resolved, ret) and kept with the
   promise, so a consumer in another module never needs it. A boxed
   non-linear value (a datatype with fields) is the one payload these
   types cannot keep from leaking: its dispose has nothing it may free,
   and wasm has no garbage collector. Make such a payload a datavtype. *)
#pub fun{a:vt@ype}
dispose
  (v: a): void

(* ============================================================
   Creation
   ============================================================ *)

#pub fun{a:vt@ype}
create
  (): @(promise(a, Pending), resolver(a))

#pub fun{a:vt@ype}
resolved
  (v: a): promise(a, Resolved)

#pub fun{a:vt@ype}
ret
  (v: a): promise(a, Chained)

(* ============================================================
   Resolution -- consumes the resolver
   ============================================================ *)

#pub fun{a:vt@ype}
resolve
  (r: resolver(a), v: a): void

(* ============================================================
   Consumption -- the promise is linear, so one of these is called
   ============================================================ *)

#pub fun{a:vt@ype}
extract
  (p: promise(a, Resolved)): a

(* Lets the promise go: a value already there is disposed; one that
   comes later is disposed when it comes. *)
#pub fun{a:vt@ype} {s:int}
discard
  (p: promise(a, s)): void

(* Ends a chain: f receives the value once it arrives (at once when it
   is already there), and must consume it. Ignoring a value with
   nothing to free is written out, as llam (_) => (). *)
#pub fun{a:vt@ype} {s:int}
finish
  (p: promise(a, s), f: (a) -<lincloptr1> void): void

(* Monadic bind *)
#pub fun{a:vt@ype}{b:vt@ype}
and_then
  {s:int}
  (p: promise(a, s),
   f: (a) -<lincloptr1> promise(b, Chained)
  ): promise(b, Chained)

(* Pending -> Chained. The identity: a promise's state is only in its
   type (promise(a, s) is one representation for every s). *)
#pub fn vow {a:vt@ype}
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

(* The payloads with nothing to free. A template's implementation must
   come before its first use in the file. *)
implement dispose<int>(_) = ()
implement dispose<Int>(_) = ()
implement dispose<bool>(_) = ()

(* ============================================================
   Implementation
   ============================================================ *)

local

(* What runs when a pending promise's value arrives. *)
vtypedef cont(a:vt@ype) = (a) -<lincloptr1> void

(* What frees a value nobody took: the payload type's dispose, read
   where the value enters (so no other module needs the template) *)
typedef disposer(a:vt@ype) = (a) -> void

(* The cell a pending promise shares with its resolver. refs counts the
   live handles (2 from create: the promise and the resolver); the last
   one to let go frees it. value is set by resolve when no continuation
   waits; cont is set by and_then when no value has arrived. *)
datavtype cell(a:vt@ype) =
  | CELL of (int, Option_vt(a), Option_vt(cont(a)), disposer(a))

(* A promise either holds its value outright or shares a cell with a
   resolver. A Pending promise always has a resolver; a Resolved one
   never does. *)
datavtype pro(a:vt@ype, int) =
  | {s:int | s != Pending} PVAL(a, s) of (a, disposer(a))
  | {s:int | s != Resolved} PCELL(a, s) of (cell(a))

$UNSAFE begin
  assume promise(a, s) = pro(a, s)
  assume resolver(a) = cell(a)
end

(* Call a continuation once, then free its closure. *)
fn{a:vt@ype} run_cont(k: cont(a), v: a): void = let
  val () = k(v)
in
  cloptr_free($UNSAFE begin $UNSAFE.castvwtp0{cloptr0}(k) end)
end

fn{a:vt@ype} drop_cont(k: Option_vt(cont(a))): void =
  case+ k of
  | ~Some_vt(f) => cloptr_free($UNSAFE begin $UNSAFE.castvwtp0{cloptr0}(f) end)
  | ~None_vt() => ()

(* A value nobody took, freed by its disposer *)
fn{a:vt@ype} drop_value(v: Option_vt(a), free: disposer(a)): void =
  case+ v of
  | ~Some_vt(x) => free(x)
  | ~None_vt() => ()

(* Let go of one handle on a cell: free it if it was the last one. *)
fn{a:vt@ype} release(c: cell(a)): void = let
  val+ @CELL(refs, _, _, _) = c
in
  if refs <= 1 then let
    prval () = fold@(c)
    val+ ~CELL(_, v, k, free) = c
    val () = drop_value<a>(v, free)
  in drop_cont<a>(k) end
  else let
    val () = refs := refs - 1
    prval () = fold@(c)
    val _ = $UNSAFE begin $UNSAFE.castvwtp0{ptr}(c) end
  in end
end

(* Give a cell's promise handle a continuation: run it now if the value
   is already there, else leave it for resolve. Consumes the handle. *)
fn{a:vt@ype} on_value(c: cell(a), k: cont(a)): void = let
  val+ @CELL(_, value, old, _) = c
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
fn{b:vt@ype} forward(q: pro(b, Chained), r: cell(b)): void =
  case+ q of
  | ~PVAL(v, _) => resolve<b>(r, v)
  | ~PCELL(c) => on_value<b>(c, llam (y: b): void =<lincloptr1> resolve<b>(r, y))

in

(* --- Creation --- *)

implement{a}
create() = let
  val c = CELL{a}(2, None_vt{a}(), None_vt{cont(a)}(), dispose<a>)
  val r = $UNSAFE begin $UNSAFE.castvwtp1{cell(a)}(c) end
in @(PCELL(c), r) end

implement{a}
resolved(v) = PVAL(v, dispose<a>)

implement{a}
ret(v) = PVAL(v, dispose<a>)

(* --- Resolution --- *)

implement{a}
resolve(r, v) = let
  val+ @CELL(_, value, k, free) = r
  val kk = k
  val () = k := None_vt{cont(a)}()
  val free1 = free
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
      val () = drop_value<a>(old, free1)
    in release<a>(r) end
end

(* --- Consumption --- *)

implement{a}
extract(p) = let
  val+ ~PVAL(v, _) = p
in v end

implement{a}{s}
discard(p) =
  case+ p of
  | ~PVAL(v, free) => free(v)
  | ~PCELL(c) => release<a>(c)

implement{a}{s}
finish(p, f) =
  case+ p of
  | ~PVAL(v, _) => let
      val () = f(v)
    in cloptr_free($UNSAFE begin $UNSAFE.castvwtp0{cloptr0}(f) end) end
  | ~PCELL(c) => on_value<a>(c, llam (x: a): void =<lincloptr1> let
      val () = f(x)
    in cloptr_free($UNSAFE begin $UNSAFE.castvwtp0{cloptr0}(f) end) end)

(* --- State coercion --- *)

implement vow{a}(p) = let
  val+ ~PCELL(c) = p
in PCELL(c) end

(* --- Monadic bind --- *)

implement{a}{b}
and_then{s}(p, f) =
  case+ p of
  | ~PVAL(v, _) => let
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
  val q = and_then<Int><int>(p, llam (n) =>
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

fn _test_finish(): void = let
  val @(p, r) = create<int>()
  val () = finish<int>(p, llam (_) => ())
  val () = resolve<int>(r, 3)
  val () = finish<int>(resolved<int>(4), llam (_) => ())
  val () = finish<int>(and_then<int><int>(ret<int>(1), llam (x) => ret<int>(x + 1)), llam (_) => ())
in () end
