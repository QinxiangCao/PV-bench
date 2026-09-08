Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition PrefixResidualState
    (values residuals flags : list Z) : Prop :=
  Znth 0 residuals 0 = 0 /\
  Znth 0 flags 0 = 1 /\
  (forall k,
      1 <= k < Zlength residuals ->
      Znth k residuals 0 =
        Znth (k - 1) values 0 - Znth (k - 1) residuals 0) /\
  forall k,
    0 <= k < Zlength flags ->
    (Znth k flags 0 = 0 \/ Znth k flags 0 = 1) /\
    (Znth k flags 0 = 1 <->
       forall j, 0 <= j <= k -> 0 <= Znth j residuals 0).

(* [residuals] and [flags] use indices relative to the 1-based physical
   position [start].  Under the explicit C length equation, their last cell is
   physical position n+1 and hence carries the terminal zero. *)

Definition SuffixResidualState
    (values : list Z) (start : Z) (residuals flags : list Z) : Prop :=
  Znth (Zlength residuals - 1) residuals 0 = 0 /\
  Znth (Zlength flags - 1) flags 0 = 1 /\
  (forall q,
      0 <= q < Zlength residuals - 1 ->
      Znth q residuals 0 =
        Znth (start + q - 1) values 0 - Znth (q + 1) residuals 0) /\
  forall q,
    0 <= q < Zlength flags ->
    (Znth q flags 0 = 0 \/ Znth q flags 0 = 1) /\
    (Znth q flags 0 = 1 <->
       forall j, q <= j < Zlength residuals ->
         0 <= Znth j residuals 0).

Definition DirectResidualSuccess
    (pre_values okpre_values : list Z) (n : Z) : Prop :=
  Znth n okpre_values 0 = 1 /\ Znth n pre_values 0 = 0.

(* For a 1-based adjacent swap position [i], [suf_values] is the complete
   physical segment [1,n+2), so physical cell i+2 has relative index i+1. *)

Definition SwapResidualSuccess
    (values pre_values suf_values okpre_values oksuf_values : list Z)
    (i : Z) : Prop :=
  Znth (i - 1) okpre_values 0 = 1 /\
  Znth (i + 1) oksuf_values 0 = 1 /\
  let x := Znth i values 0 - Znth (i - 1) pre_values 0 in
  let y := Znth (i - 1) values 0 - x in
  0 <= x /\ 0 <= y /\ y = Znth (i + 1) suf_values 0.

Definition CheckedSwapPrefix
    (values pre_values suf_values okpre_values oksuf_values : list Z)
    (upto : Z) : Prop :=
  ~ DirectResidualSuccess pre_values okpre_values (Zlength values) /\
  forall i,
    1 <= i < upto ->
    ~ SwapResidualSuccess
        values pre_values suf_values okpre_values oksuf_values i.
