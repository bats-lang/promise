# promise

Linear async promises for bats. Each promise must be consumed exactly once — the
type system prevents double-awaits, forgotten promises, and double-resolves.

A promise moves through three states tracked at the type level:
**Pending -> Resolved -> Chained**. The `resolver` is a write-once handle
consumed by `resolve`.

## Types

```
stadef Pending = 0 / Resolved = 1 / Chained = 2

absvtype promise(a:t@ype, s:int)
absvtype resolver(a:t@ype)
```

## API

### Creation

```
#use promise as P

(* Create a pending promise and its write-end resolver *)
$P.create<a>() : @(promise(a, Pending), resolver(a))

(* Lift a value into an already-resolved promise *)
$P.resolved<a>(v: a) : promise(a, Resolved)

(* Lift a value for return inside a then-callback *)
$P.ret<a>(v: a) : promise(a, Chained)
```

### Resolution

```
(* Resolve a pending promise — consumes the resolver *)
$P.resolve<a>(r: resolver(a), v: a) : void
```

### Consumption

```
(* Extract the value from a resolved promise — consumes the promise *)
$P.extract<a>(p: promise(a, Resolved)) : a

(* Discard a promise in any state without extracting *)
$P.discard<a>{s}(p: promise(a, s)) : void

(* End a chain: f receives the value when it arrives. Ignoring it is
   written out, as lam(_) => () *)
$P.finish<a>{s}(p: promise(a, s), f: a -<cloptr1> void) : void

(* Monadic bind — chain a callback that receives the resolved value *)
$P.and_then<a><b>{s}
  (p: promise(a, s), f: a -<cloptr1> promise(b, Chained)) : promise(b, Chained)
```

### Coercion

```
(* Pending to Chained: the identity (the state lives only in the type) *)
$P.vow{a}(p: promise(a, Pending)) : promise(a, Chained)
```

### Stashing (for host boundary crossing)

The host (JS) can fire any int, so a stashed resolver carries `Int`
(`[v:int] int v`). The receiver bounds the value with its own checks,
with no cast:

```
(* Store a resolver in a table, return an integer ID *)
$P.stash(r: resolver(Int)) : int

(* Recover a resolver from its ID *)
$P.unstash(id: int) : resolver(Int)

(* Convenience: unstash + resolve in one call (no-op if ID is invalid) *)
$P.fire(id: int, value: Int) : void
```
