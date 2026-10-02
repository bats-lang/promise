(* A match over every state that leaves the chained cell out *)
fn{a:vt@ype} _static_left_out {s:promise_state} (p: pro(a, s)): void =
  case+ p of
  | ~ResolvedValue(v, free) => free(v)
  | ~ChainedValue(v, free) => free(v)
  | ~PendingCell(c) => release<a>(c)
