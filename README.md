# promise

Linear async promises for bats. Each promise must be consumed exactly once — the
type system prevents double-awaits, forgotten promises, and double-resolves.

A promise moves through three states tracked at the type level:
**Pending → Resolved → Chained**. The `resolver` is a write-once handle
consumed by `resolve`.

## Types

```
datasort PromiseState = Pending | Resolved | Chained

absvtype promise(a:t@ype, s:PromiseState)
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
$P.ret<a>(v: a) : promise(a, Resolved)
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
$P.discard<a>{s:PromiseState}(p: promise(a, s)) : void

(* Monadic bind — chain a callback that receives the resolved value *)
$P.then<a><b>{s:PromiseState}
  (p: promise(a, s), f: a -<cloptr1> promise(b, s2)) : promise(b, Chained)
```

### Coercion

```
(* Zero-cost coerce Pending to Chained *)
$P.vow{a:t@ype}(p: promise(a, Pending)) : promise(a, Chained)
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

## Dependencies

- **array**
