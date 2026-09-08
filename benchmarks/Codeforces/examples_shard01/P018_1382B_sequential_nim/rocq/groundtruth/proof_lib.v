Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Import ListNotations.
Local Open Scope Z_scope.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Export PVbench.Codeforces.examples_shard01.P018_1382B_sequential_nim.rocq.spec_lib.

Lemma leading_ones_unique__return_semantics :
  forall piles k1 k2,
    LeadingOnes piles k1 ->
    LeadingOnes piles k2 ->
    k1 = k2.
Proof.
  intros piles k1 k2 H1 H2.
  unfold LeadingOnes in *.
  destruct H1 as [[Hk1_lo Hk1_hi] [Hprefix1 Hend1]].
  destruct H2 as [[Hk2_lo Hk2_hi] [Hprefix2 Hend2]].
  destruct (Z_lt_ge_dec k1 k2) as [Hlt | Hge].
  - specialize (Hprefix2 k1 ltac:(lia)).
    destruct Hend1 as [Hend1 | Hend1].
    + lia.
    + exfalso. apply Hend1. exact Hprefix2.
  - destruct (Z_lt_ge_dec k2 k1) as [Hgt | Hle].
    + specialize (Hprefix1 k2 ltac:(lia)).
      destruct Hend2 as [Hend2 | Hend2].
      * lia.
      * exfalso. apply Hend2. exact Hprefix1.
    + lia.
Qed.
Lemma even_of_nonnegative_rem_zero__return_semantics :
  forall n : Z, (0 <= n)%Z -> (Z.rem n 2 = 0)%Z -> Z.even n = true.
Proof.
  intros n Hn Hrem.
  apply Z.even_spec.
  rewrite Z.rem_mod_nonneg in Hrem by lia.
  apply (proj1 (Z.mod_divide n 2 ltac:(lia))) in Hrem.
  destruct Hrem as [k Hk].
  exists k. lia.
Qed.
Lemma odd_of_nonnegative_rem_nonzero__return_semantics :
  forall n : Z, (0 <= n)%Z -> (Z.rem n 2 <> 0)%Z -> Z.even n = false.
Proof.
  intros n Hn Hrem.
  destruct (Z.even n) eqn:Heven; [|reflexivity].
  apply Z.even_spec in Heven.
  destruct Heven as [k Hk].
  exfalso. apply Hrem.
  rewrite Hk, Z.mul_comm, Z.rem_mul; lia.
Qed.
Lemma even_of_nonnegative_rem_not_one__return_semantics :
  forall n : Z, (0 <= n)%Z -> (Z.rem n 2 <> 1)%Z -> Z.even n = true.
Proof.
  intros n Hn Hnotone.
  pose proof (Z.rem_bound_pos n 2 ltac:(lia) ltac:(lia)) as Hbound.
  apply even_of_nonnegative_rem_zero__return_semantics; [exact Hn | lia].
Qed.
