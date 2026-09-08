(* Codeforces 1355/C - Count Triangles: how many non-degenerate integer triangles
   (x, y, z) satisfy A <= x <= B <= y <= C <= z <= D. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

(* 1 <= a <= b <= c <= d <= 5 * 10^5. *)
Definition Pre (a b c d : Z) : Prop :=
  (* Stated explicitly in the P057 solver Require, which therefore omits the
     Pre(...) call:
       1 <= a <= b /\ b <= c /\ c <= d /\ d <= 500000. *)
  True.

(* out = #{ (x, y, z) : a <= x <= b <= y <= c <= z <= d  and  x + y > z }, the
   triples enumerated by a single index q over the box of side ranges:
     nx = b-a+1,  ny = c-b+1,  nz = d-c+1
     x = a + (q / (ny * nz)) mod nx,  y = b + (q / nz) mod ny,  z = c + q mod nz
   Since x <= y <= z, x + y > z is the only triangle inequality that can fail. *)
Definition Spec (a b c d out : Z) : Prop :=
  let nx := b - a + 1 in let ny := c - b + 1 in let nz := d - c + 1 in
  out = #(fun q : Z => 0 <= q < nx * ny * nz /\
    let x := a + (q / (ny * nz)) mod nx in
    let y := b + (q / nz) mod ny in let z := c + q mod nz in x + y > z).
