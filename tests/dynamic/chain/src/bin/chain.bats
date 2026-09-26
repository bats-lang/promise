(* Every path a value takes through a promise: and_then before and after
   resolve, a continuation that returns a pending promise, a discarded
   pending promise, a value wider than a pointer, and more resolvers
   stashed than the table starts with. *)

#include "share/atspre_staload.hats"

#use promise as P

fn show(tag: string, p: $P.promise(int, $P.Chained)): void =
  $P.discard<int>($P.and_then<int><int>(p, lam (v) => let
    val () = println! (tag, " ", v)
  in $P.ret<int>(v) end))

implement main0 () = let
  (* 1: and_then before resolve, two steps *)
  val @(p1, r1) = $P.create<int>()
  val q1 = $P.and_then<int><int>(p1, lam (x) => $P.ret<int>(x + 1))
  val () = show("t1", q1)
  val () = $P.resolve<int>(r1, 41)
  (* 2: resolve before and_then *)
  val @(p2, r2) = $P.create<int>()
  val () = $P.resolve<int>(r2, 7)
  val () = show("t2", $P.and_then<int><int>(p2, lam (x) => $P.ret<int>(x * 2)))
  (* 3: continuation returns a pending promise, settled later *)
  val @(p3, r3) = $P.create<int>()
  val q3 = $P.and_then<int><int>(p3, lam (x) => let
    val @(ip, ir) = $P.create<Int>()
    val id = $P.stash(ir)
    val () = println! ("t3 stashed ", id)
  in $P.and_then<Int><int>(ip, lam (n) => $P.ret<int>(n + x)) end)
  val () = show("t3", q3)
  val () = $P.resolve<int>(r3, 1)
  val () = println! ("t3 inner pending")
  val () = $P.fire(0, 99)
  (* 4: discard pending, then resolve *)
  val @(p4, r4) = $P.create<int>()
  val () = $P.discard<int>(p4)
  val () = $P.resolve<int>(r4, 5)
  val () = println! ("t4 ok")
  (* 5: doubles survive *)
  val @(p5, r5) = $P.create<double>()
  val q5 = $P.and_then<double><int>(p5, lam (d) => let
    val () = println! ("t5 ", d)
  in $P.ret<int>(0) end)
  val () = $P.discard<int>(q5)
  val () = $P.resolve<double>(r5, 2.5)
  (* 6: extract resolved *)
  val () = println! ("t6 ", $P.extract<int>($P.resolved<int>(12)))
  (* 7: 40 stashed resolvers, fired in reverse *)
  fun loop {k:nat} .<k>. (k: int k, acc: int): void =
    if k = 0 then () else let
      val @(p, r) = $P.create<Int>()
      val id = $P.stash(r)
      val () = $P.discard<Int>(p)
      val () = $P.fire(id, k)
    in loop(k - 1, acc + id) end
  val () = loop(40, 0)
  val @(p7, r7) = $P.create<Int>()
  val id7 = $P.stash(r7)
  val q7 = $P.and_then<Int><int>(p7, lam (n) => let val () = println! ("t7 ", n) in $P.ret<int>(0) end)
  val () = $P.discard<int>(q7)
  val () = $P.fire(id7, 77)
  val () = $P.fire(id7, 78)
  val () = $P.fire(~1, 0)
in () end
