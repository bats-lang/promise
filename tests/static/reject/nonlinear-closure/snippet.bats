(* A consumer written with lam: a closure promise could not free *)
fn _static_lam (): void =
  finish<int>(ret<int>(1), lam (_) => ())
