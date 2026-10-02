(* A state is one of three, not a number *)
fn _static_state_as_int (p: promise(int, 1)): void = discard<int>(p)
