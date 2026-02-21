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

(* Monadic bind — chain a callback that receives the resolved value *)
$P.then<a><b>{s}
  (p: promise(a, s), f: a -<cloptr1> promise(b, Chained)) : promise(b, Chained)
```

### Coercion

```
(* Zero-cost coerce Pending to Chained *)
$P.vow{a}(p: promise(a, Pending)) : promise(a, Chained)
```

### Stashing (for host boundary crossing)

```
(* Store a resolver in a table, return an integer ID *)
$P.stash(r: resolver(int)) : int

(* Recover a resolver from its ID *)
$P.unstash(id: int) : resolver(int)

(* Convenience: unstash + resolve in one call (no-op if ID is invalid) *)
$P.fire(id: int, value: int) : void
```
