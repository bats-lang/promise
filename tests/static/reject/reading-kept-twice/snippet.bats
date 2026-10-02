(* A payload taken apart, then used again *)
datavtype reading = Reading of int
implement dispose<reading>(reading) = let val+ ~Reading(_) = reading in () end
fn _static_twice (): void =
  finish<reading>(ret<reading>(Reading(1)), llam (reading) => let
    val () = (case+ reading of ~Reading(_) => ())
  in dispose<reading>(reading) end)
