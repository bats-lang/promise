(* A consumer that drops a linear payload without taking it apart *)
datavtype reading = Reading of int
implement dispose<reading>(reading) = let val+ ~Reading(_) = reading in () end
fn _static_dropped (): void =
  finish<reading>(ret<reading>(Reading(1)), llam (reading) => ())
