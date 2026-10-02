(* Only a resolved promise has a value to take *)
fn _static_extract_pending (): void = let
  val @(p, r) = create<int>()
  val v = extract<int>(p)
  val () = resolve<int>(r, v)
in () end
