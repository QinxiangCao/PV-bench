Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* The loop has processed exactly the triples whose first two sides have
   sum below [next].  This is a mathematical restriction of [Spec], rather
   than a model of the loop's min/max implementation. *)
Definition TrianglePrefix (a b c d next total : Z) : Prop :=
  let nx := b - a + 1 in let ny := c - b + 1 in let nz := d - c + 1 in
  total = #(fun q : Z => 0 <= q < nx * ny * nz /\
    let x := a + (q / (ny * nz)) mod nx in
    let y := b + (q / nz) mod ny in let z := c + q mod nz in
    x + y > z /\ x + y < next).
