# lib

### `stadef Pending = 0`

### `stadef Resolved = 1`

### `stadef Chained = 2`

### `absvtype promise(a:t@ype, s:int)`

### `absvtype resolver(a:t@ype)`

### `fun{a:t@ype}
create
  (): @(promise(a, Pending), resolver(a))`

### `fun{a:t@ype}
resolved
  (v: a): promise(a, Resolved)`

### `fun{a:t@ype}
ret
  (v: a): promise(a, Chained)`

### `fun{a:t@ype}
resolve
  (r: resolver(a), v: a): void`

### `fun{a:t@ype}
extract
  (p: promise(a, Resolved)): a`

### `fun{a:t@ype} {s:int}
discard
  (p: promise(a, s)): void`

### `fun{a:t@ype}{b:t@ype}
and_then
  {s:int}
  (p: promise(a, s),
   f: (a) -<cloptr1> promise(b, Chained)
  ): promise(b, Chained)`

### `castfn vow{a:t@ype}
  (p: promise(a, Pending)): promise(a, Chained)`

### `fun stash
  (r: resolver(int)): int`

### `fun unstash
  (id: int): resolver(int)`

### `fun fire
  (id: int, value: int): void`
