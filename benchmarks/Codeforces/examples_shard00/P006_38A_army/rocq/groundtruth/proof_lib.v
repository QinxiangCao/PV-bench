Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Local Open Scope Z_scope.
Require Import Coq.micromega.Lia.
Require Export PVbench.Codeforces.examples_shard00.P006_38A_army.rocq.spec_lib.

Lemma Spec_succ__loop_step :
  forall n years a i ans,
    1 <= a ->
    a <= i ->
    i <= Zlength years ->
    Spec n years a i ans ->
    Spec n years a (i + 1) (ans + Znth i (0 :: years) 0).
Proof.
  intros n years a i ans Ha Hai Hi HSpec.
  unfold Spec in *.
  change (ans = ListLib.sum (sublist (a - 1) (i - 1) years)) in HSpec.
  change (ans + Znth i (0 :: years) 0 =
    ListLib.sum (sublist (a - 1) (i + 1 - 1) years)).
  replace (i + 1 - 1) with i by lia.
  rewrite (sublist_split (a - 1) i (i - 1) years) by lia.
  rewrite ListLib.sum_app.
  pose proof (sublist_single 0 (i - 1) years ltac:(lia)) as Hsingle.
  replace (i - 1 + 1) with i in Hsingle by lia.
  rewrite Hsingle.
  simpl.
  rewrite Znth_cons by lia.
  lia.
Qed.
