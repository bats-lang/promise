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

## Disposing a value nobody took

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

### Consumption

A continuation is a linear closure (`llam`): it runs once, and promise
frees it after it runs. A `lam` closure could never be freed and does
not type-check.

### Stashing (for host boundary crossing)

The host (JS) can fire any int, so a stashed resolver carries `Int`
(`[v:int] int v`). The receiver bounds the value with its own checks,
with no cast
