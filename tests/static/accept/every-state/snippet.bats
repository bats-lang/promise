(* A match over every state names all four representations *)
fn{a:vt@ype} _static_every_state {s:promise_state} (p: pro(a, s)): void =
  case+ p of
  | ~ResolvedValue(v, free) => free(v)
  | ~ChainedValue(v, free) => free(v)
  | ~PendingCell(c) => release<a>(c)
  | ~ChainedCell(c) => release<a>(c)
