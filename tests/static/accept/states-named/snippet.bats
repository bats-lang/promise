(* Code over any state is indexed by the datasort *)
fn _static_any_state {s:promise_state} (p: promise(int, s)): void = discard<int>(p)
fn _static_states_named (): void = let
  val @(p, r) = create<int>()
  val () = _static_any_state(p)
  val () = resolve<int>(r, 1)
  val () = _static_any_state(resolved<int>(2))
  val () = _static_any_state(ret<int>(3))
in () end
