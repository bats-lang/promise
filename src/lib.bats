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

(* Zero-cost coercion: Pending -> Chained *)
#pub castfn vow{a:t@ype}
  (p: promise(a, Pending)): promise(a, Chained)

(* ============================================================
   Resolver stash -- stores resolver in table, returns int ID
   ============================================================ *)

#pub fun stash
  (r: resolver(int)): int

#pub fun unstash
  (id: int): resolver(int)

#pub fun fire
  (id: int, value: int): void

(* ============================================================
   C runtime -- resolver table + promise helpers
   ============================================================ *)

$UNSAFE begin
%{#
/* Resolver stash -- linear: each slot consumed exactly once */
#define _PROMISE_MAX_RESOLVERS 128
static void *_promise_resolver_table[_PROMISE_MAX_RESOLVERS] = {0};

static int _promise_resolver_stash(void *resolver) {
  int i;
  for (i = 0; i < _PROMISE_MAX_RESOLVERS; i++) {
    if (!_promise_resolver_table[i]) {
      _promise_resolver_table[i] = resolver;
      return i;
    }
  }
  return -1;
}

static void *_promise_resolver_unstash(int id) {
  if (id < 0 || id >= _PROMISE_MAX_RESOLVERS) return (void*)0;
  void *r = _promise_resolver_table[id];
  _promise_resolver_table[id] = (void*)0;
  return r;
}

/* Promise cell field access helpers for _resolve_chain */
/* promise_mk(state_tag, value, cb, chain) */

static int _promise_get_state_tag(void *p) {
  int *fields = (int *)p;
  return fields[0];
}

static void *_promise_get_value(void *p) {
  void **fields = (void **)p;
  return fields[1];
}

static void *_promise_get_cb(void *p) {
  void **fields = (void **)p;
  return fields[2];
}

static void *_promise_get_chain(void *p) {
  void **fields = (void **)p;
  return fields[3];
}

static void _promise_set_resolved(void *p, void *v) {
  int *ifields = (int *)p;
  void **fields = (void **)p;
  ifields[0] = 2; /* PState_resolved */
  fields[1] = v;
}

static void _promise_set_chain(void *p, void *chain) {
  void **fields = (void **)p;
  fields[3] = chain;
}

/* Invoke a linear closure and free it */
static void *_promise_cloptr1_invoke(void *clo, void *arg) {
  typedef void *(*clo_fn)(void *, void *);
  clo_fn f = *(clo_fn *)clo;
  void *result = f(clo, arg);
  return result;
}

/* Wrap a cloptr1 for deferred invocation */
static void *_promise_cloptr1_wrap(void *clo) {
  return clo;
}
%}
end

(* ============================================================
   Forward declaration for chain resolution
   ============================================================ *)

extern fun _resolve_chain
  (p: ptr, v: ptr): void = "mac#_resolve_chain"

(* ============================================================
   Implementation
   ============================================================ *)

local

datatype promise_state_t =
  | PState_abandoned
  | PState_pending
  | PState_resolved

datavtype promise_vt =
  | promise_mk of (promise_state_t, ptr(*value*), ptr(*cb*), ptr(*chain*))

assume promise(a, s) = promise_vt
assume resolver(a) = ptr

in

(* --- Chain resolution --- *)

implement
_resolve_chain(p, v) = let
  val state_tag = $extfcall(int, "_promise_get_state_tag", p)
  val cb_val = $extfcall(ptr, "_promise_get_cb", p)
  val chain_val = $extfcall(ptr, "_promise_get_chain", p)
in
  if state_tag = 0 then
    $extfcall(void, "free", p)
  else if ptr_isnot_null(cb_val) then let
    val () = $extfcall(void, "_promise_set_resolved", p, v)
    val () = $extfcall(void, "free", p)
    val inner_ptr = $extfcall(ptr, "_promise_cloptr1_invoke", cb_val, v)
    val inner_state = $extfcall(int, "_promise_get_state_tag", inner_ptr)
  in
    if inner_state = 2 then let
      val iv = $extfcall(ptr, "_promise_get_value", inner_ptr)
      val () = $extfcall(void, "free", inner_ptr)
    in _resolve_chain(chain_val, iv) end
    else let
      val () = $extfcall(void, "_promise_set_chain", inner_ptr, chain_val)
    in end
  end
  else if ptr_isnot_null(chain_val) then let
    val () = $extfcall(void, "_promise_set_resolved", p, v)
    val () = $extfcall(void, "free", p)
  in _resolve_chain(chain_val, v) end
  else
    $extfcall(void, "_promise_set_resolved", p, v)
end

(* --- Creation --- *)

implement{a}
create() = let
  val pv = promise_mk(PState_pending(), the_null_ptr, the_null_ptr, the_null_ptr)
  val rp = $UNSAFE begin $UNSAFE.castvwtp1{ptr}(pv) end
in @(pv, rp) end

implement{a}
resolved(v) =
  promise_mk(PState_resolved(),
    $UNSAFE begin $UNSAFE.castvwtp0{ptr}(v) end,
    the_null_ptr, the_null_ptr)

implement{a}
ret(v) =
  promise_mk(PState_resolved(),
    $UNSAFE begin $UNSAFE.castvwtp0{ptr}(v) end,
    the_null_ptr, the_null_ptr)

(* --- Resolution --- *)

implement{a}
resolve(r, v) = let
  val vp = $UNSAFE begin $UNSAFE.castvwtp0{ptr}(v) end
in
  _resolve_chain(r, vp)
end

(* --- Consumption --- *)

implement{a}
extract(p) = let
  val+ ~promise_mk(_, vp, _, _) = p
in
  $UNSAFE begin $UNSAFE.castvwtp0{a}(vp) end
end

implement{a}{s}
discard(p) = let
  val+ @promise_mk(state, value, cb, chain) = p
  val cur_state = state
in
  case+ cur_state of
  | PState_resolved() => let
      prval () = fold@(p)
      val+ ~promise_mk(_, _, _, _) = p
    in end
  | PState_pending() => let
      val () = state := PState_abandoned()
      prval () = fold@(p)
      val _ = $UNSAFE begin $UNSAFE.castvwtp0{ptr}(p) end
    in end
  | PState_abandoned() => let
      prval () = fold@(p)
      val+ ~promise_mk(_, _, _, _) = p
    in end
end

(* --- Monadic bind --- *)

implement{a}{b}
and_then{s}(p, f) = let
  val chain = promise_mk(PState_pending(), the_null_ptr, the_null_ptr, the_null_ptr)
  val+ @promise_mk(state, value, cb, chain_field) = p
  val cur_state = state
  val v = value
  val result =
    case+ cur_state of
    | PState_resolved() => let
        prval () = fold@(p)
        val+ ~promise_mk(_, _, _, _) = p
        val fp = $UNSAFE begin $UNSAFE.castvwtp0{ptr}(f) end
        val inner_ptr = $extfcall(ptr, "_promise_cloptr1_invoke", fp, v)
        val ipv = $UNSAFE begin $UNSAFE.castvwtp0{promise_vt}(inner_ptr) end
        val+ @promise_mk(inner_st, iv, _, ic) = ipv
        val inner_state = inner_st
      in
        case+ inner_state of
        | PState_resolved() => let
            val iv_val = iv
            prval () = fold@(ipv)
            val+ ~promise_mk(_, _, _, _) = ipv
            val+ @promise_mk(cs, cv, _, _) = chain
            val () = cs := PState_resolved()
            val () = cv := iv_val
            prval () = fold@(chain)
          in $UNSAFE begin $UNSAFE.castvwtp0{ptr}(chain) end end
        | PState_pending() => let
            val chain_ptr = $UNSAFE begin $UNSAFE.castvwtp1{ptr}(chain) end
            val () = ic := chain_ptr
            prval () = fold@(ipv)
            val _ = $UNSAFE begin $UNSAFE.castvwtp0{ptr}(ipv) end
            val _ = $UNSAFE begin $UNSAFE.castvwtp0{ptr}(chain) end
          in chain_ptr end
        | PState_abandoned() => let
            val chain_ptr = $UNSAFE begin $UNSAFE.castvwtp1{ptr}(chain) end
            val () = ic := chain_ptr
            prval () = fold@(ipv)
            val _ = $UNSAFE begin $UNSAFE.castvwtp0{ptr}(ipv) end
            val _ = $UNSAFE begin $UNSAFE.castvwtp0{ptr}(chain) end
          in chain_ptr end
      end
    | PState_pending() => let
        val fp = $UNSAFE begin $UNSAFE.castvwtp0{ptr}(f) end
        val wrapped = $extfcall(ptr, "_promise_cloptr1_wrap", fp)
        val chain_ptr = $UNSAFE begin $UNSAFE.castvwtp1{ptr}(chain) end
        val () = cb := wrapped
        val () = chain_field := chain_ptr
        prval () = fold@(p)
        val _ = $UNSAFE begin $UNSAFE.castvwtp0{ptr}(p) end
        val _ = $UNSAFE begin $UNSAFE.castvwtp0{ptr}(chain) end
      in chain_ptr end
    | PState_abandoned() => let
        val fp = $UNSAFE begin $UNSAFE.castvwtp0{ptr}(f) end
        val wrapped = $extfcall(ptr, "_promise_cloptr1_wrap", fp)
        val chain_ptr = $UNSAFE begin $UNSAFE.castvwtp1{ptr}(chain) end
        val () = cb := wrapped
        val () = chain_field := chain_ptr
        prval () = fold@(p)
        val _ = $UNSAFE begin $UNSAFE.castvwtp0{ptr}(p) end
        val _ = $UNSAFE begin $UNSAFE.castvwtp0{ptr}(chain) end
      in chain_ptr end
  : ptr
in
  $UNSAFE begin $UNSAFE.castvwtp0{promise_vt}(result) end
end

(* --- Stash --- *)

implement
stash(r) = $extfcall(int, "_promise_resolver_stash", r)

implement
unstash(id) = let
  val p = $extfcall(ptr, "_promise_resolver_unstash", id)
in p end

implement
fire(id, value) = let
  val r = $extfcall(ptr, "_promise_resolver_unstash", id)
in
  if ptr_isnot_null(r) then
    _resolve_chain(r, $UNSAFE begin $UNSAFE.cast{ptr}(value) end)
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
  val @(p, r) = create<int>()
  val id = stash(r)
  val () = fire(id, 7)
  val () = discard<int>(p)
in () end

fn _test_vow(): void = let
  val @(p, r) = create<int>()
  val pc : promise(int, Chained) = vow(p)
  val () = discard<int>(pc)
  val () = resolve<int>(r, 0)
in () end
