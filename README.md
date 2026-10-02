# promise

Linear async promises for bats. Each promise must be consumed exactly once — the
type system prevents double-awaits, forgotten promises, and double-resolves.

So must its value. A payload is a `vt@ype`, so a linear value (a
`datavtype`, a blob) rides a promise and the compiler makes its one
consumer take it. wasm has no garbage collector: a boxed value nobody
frees is leaked, so a payload with anything to free is a `datavtype`,
never a boxed `datatype`. A value no consumer takes (the promise let go
before or after it resolved) is given to `dispose`, which each payload
type implements.

A promise moves through three states tracked at the type level:
**Pending -> Resolved -> Chained**. The `resolver` is a write-once handle
consumed by `resolve`. The state is a datasort, not a number: code over
any state is written `{s:$P.promise_state}`.

## Types

```
datasort promise_state = Pending | Resolved | Chained

absvtype promise(a:vt@ype, s:promise_state)
vtypedef promise_pending(a:vt@ype) = promise(a, Pending)
vtypedef promise_resolved(a:vt@ype) = promise(a, Resolved)
absvtype resolver(a:vt@ype)
```

## Disposing a value nobody took

```
(* Frees a payload no consumer took *)
fun{a:vt@ype} dispose(v: a): void
```

Each payload type implements it once, beside the type, before the first
function that puts one in a promise (ATS2 resolves template instances in
file order). promise implements it for `int`, `Int` and `bool`, which
have nothing to free:

```
datavtype reading = Reading of int

implement $P.dispose<reading>(reading) = let
  val+ ~Reading(_) = reading
in () end
```

`create`, `resolved` and `ret` read `dispose<a>` where the value enters
and keep it with the promise as a function pointer, so a consumer in
another module (one that only calls `finish` or `discard`) never
instantiates it.

## API

### Creation

```
#use promise as P

(* Create a pending promise and its write-end resolver *)
$P.create<a>() : @(promise(a, Pending), resolver(a))

(* Lift a value into an already-resolved promise *)
$P.resolved<a>(v: a) : promise(a, Resolved)

(* Lift a value for return inside an and_then callback *)
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

(* Discard a promise in any state without extracting: a value already
   there is disposed, one that comes later is disposed when it comes *)
$P.discard<a>{s}(p: promise(a, s)) : void

(* End a chain: f receives the value when it arrives, and must consume
   it. Ignoring a value with nothing to free is written out, as
   llam (_) => () *)
$P.finish<a>{s}(p: promise(a, s), f: (a) -<lincloptr1> void) : void

(* Monadic bind — chain a callback that receives the resolved value *)
$P.and_then<a><b>{s}
  (p: promise(a, s), f: (a) -<lincloptr1> promise(b, Chained)) : promise(b, Chained)
```

A continuation is a linear closure (`llam`): it runs once, and promise
frees it after it runs. A `lam` closure could never be freed and does
not type-check.

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

(* Resolve the resolver stashed under id with value, and free its slot
   (no-op when nothing is stashed there) *)
$P.fire(id: int, value: Int) : void
```
