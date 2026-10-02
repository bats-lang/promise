(* A linear payload no consumer takes is given to dispose exactly once,
   on every path a promise can be let go by; one a consumer takes never
   reaches dispose. Each line prints how many probes dispose freed. *)

#include "share/atspre_staload.hats"

#use promise as P

(* A linear payload: dispose frees it and counts it *)
datavtype probe = Probe of int

val disposed = ref<int>(0)

implement $P.dispose<probe>(probe) = let
  val+ ~Probe(_) = probe
in !disposed := !disposed + 1 end

(* A consumer that takes a probe apart, which frees it *)
fn take (probe: probe): void = let
  val+ ~Probe(_) = probe
in () end

(* How many probes dispose freed since before *)
fn report (name: string, before: int): void =
  println! (name, " ", !disposed - before)

implement main0 () = let
  (* Let go while pending, then resolved: disposed when it comes *)
  val before = !disposed
  val @(p, r) = $P.create<probe>()
  val () = $P.discard<probe>(p)
  val () = $P.resolve<probe>(r, Probe(1))
  val () = report("discarded-then-resolved", before)
  (* Resolved, then let go: disposed then *)
  val before = !disposed
  val @(p, r) = $P.create<probe>()
  val () = $P.resolve<probe>(r, Probe(2))
  val () = $P.discard<probe>(p)
  val () = report("resolved-then-discarded", before)
  (* A ready value let go, from resolved and from ret *)
  val before = !disposed
  val () = $P.discard<probe>($P.resolved<probe>(Probe(3)))
  val () = $P.discard<probe>($P.ret<probe>(Probe(4)))
  val () = report("ready-discarded", before)
  (* Taken by extract: never disposed *)
  val before = !disposed
  val () = take($P.extract<probe>($P.resolved<probe>(Probe(5))))
  val () = report("extracted", before)
  (* Taken by finish, before and after it resolves: never disposed *)
  val before = !disposed
  val @(p, r) = $P.create<probe>()
  val () = $P.finish<probe>(p, llam (probe) => take(probe))
  val () = $P.resolve<probe>(r, Probe(6))
  val () = $P.finish<probe>($P.resolved<probe>(Probe(7)), llam (probe) => take(probe))
  val () = report("finished", before)
  (* Mapped by and_then, the result let go: the mapped value disposed
     once, the original never (the continuation took it) *)
  val before = !disposed
  val @(p, r) = $P.create<probe>()
  val q = $P.and_then<probe><probe>(p, llam (probe) => let
    val+ ~Probe(n) = probe
  in $P.ret<probe>(Probe(n + 10)) end)
  val () = $P.discard<probe>(q)
  val () = $P.resolve<probe>(r, Probe(8))
  val () = report("chained-discarded", before)
  (* A continuation that returns a pending promise, the chain let go:
     the inner value disposed once it comes *)
  val before = !disposed
  val @(p, r) = $P.create<probe>()
  val @(inner, inner_resolver) = $P.create<probe>()
  val q = $P.and_then<probe><probe>(p, llam (probe) => let
    val () = take(probe)
  in $P.vow(inner) end)
  val () = $P.discard<probe>(q)
  val () = $P.resolve<probe>(r, Probe(9))
  val () = $P.resolve<probe>(inner_resolver, Probe(10))
  val () = report("inner-discarded", before)
  (* Through a chain to finish: taken, never disposed *)
  val before = !disposed
  val @(p, r) = $P.create<probe>()
  val () = $P.finish<probe>($P.and_then<probe><probe>(p, llam (probe) => let
    val+ ~Probe(n) = probe
  in $P.ret<probe>(Probe(n + 1)) end), llam (probe) => take(probe))
  val () = $P.resolve<probe>(r, Probe(11))
  val () = report("chained-finished", before)
in () end
