(* A linear payload taken apart by its one consumer, and one let go
   (dispose frees it) *)
datavtype reading = Reading of int
implement dispose<reading>(reading) = let val+ ~Reading(_) = reading in () end
fn _static_taken (): void = let
  val () = finish<reading>(ret<reading>(Reading(1)), llam (reading) => let
    val+ ~Reading(_) = reading
  in () end)
in discard<reading>(ret<reading>(Reading(2))) end
