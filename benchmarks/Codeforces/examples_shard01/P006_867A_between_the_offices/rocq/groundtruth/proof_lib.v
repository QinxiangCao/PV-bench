Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Import ListNotations.
Local Open Scope Z_scope.
Require Import Coq.micromega.Lia.
Require Import Coq.setoid_ring.Ring.
Require Export PVbench.Codeforces.examples_shard01.P006_867A_between_the_offices.rocq.spec_lib.

Lemma transition_pair_balance__endpoint_verdicts :
  forall x y,
    (x = 83 \/ x = 70) ->
    (y = 83 \/ y = 70) ->
    (if (Z.eqb x 83 && Z.eqb y 70)%bool then 1 else 0) -
    (if (Z.eqb x 70 && Z.eqb y 83)%bool then 1 else 0) =
    (if Z.eqb x 83 then 1 else 0) -
    (if Z.eqb y 83 then 1 else 0).
Proof.
  intros x y [-> | ->] [-> | ->]; reflexivity.
Qed.
Lemma endpoint_indicator_telescope__endpoint_verdicts :
  forall (f : Z -> Z) high,
    1 <= high ->
    sum (fun i => 0 <= i < high) (fun i => f i - f (i + 1)) =
    f 0 - f high.
Proof.
  intros f high Hhigh.
  rewrite sum_Z_range_sub.
  rewrite <- (sum_Z_range_shift_1 0 high f).
  change
    (sum (fun i => 0 <= i < high) f -
     sum (fun i => 1 <= i < high + 1) f = f 0 - f high).
  rewrite (sum_Z_range_cons 0 high f) by lia.
  rewrite (sum_Z_range_extend_right 1 high f) by lia.
  change
    (f 0 + sum (fun i => 1 <= i < high) f -
     (sum (fun i => 1 <= i < high) f + f high) =
     f 0 - f high).
  ring.
Qed.
Lemma transition_count_balance_by_endpoints__endpoint_verdicts :
  forall days,
    2 <= Zlength days ->
    (forall i, 0 <= i < Zlength days ->
       Znth i days 0 = 83 \/ Znth i days 0 = 70) ->
    TransitionCount days 83 70 - TransitionCount days 70 83 =
    (if Z.eqb (Znth 0 days 0) 83 then 1 else 0) -
    (if Z.eqb (Znth (Zlength days - 1) days 0) 83 then 1 else 0).
Proof.
  intros days Hlen Halphabet.
  unfold TransitionCount, sum_range.
  replace (Zlength days - 2 + 1) with (Zlength days - 1) by lia.
  rewrite <- sum_Z_range_sub.
  transitivity
    (sum (fun i => 0 <= i < Zlength days - 1)
       (fun i =>
          (if Z.eqb (Znth i days 0) 83 then 1 else 0) -
          (if Z.eqb (Znth (i + 1) days 0) 83 then 1 else 0))).
  - apply sum_Z_range_ext.
    intros i Hi.
    apply transition_pair_balance__endpoint_verdicts.
    + apply Halphabet. lia.
    + apply Halphabet. lia.
  - apply endpoint_indicator_telescope__endpoint_verdicts.
    lia.
Qed.
