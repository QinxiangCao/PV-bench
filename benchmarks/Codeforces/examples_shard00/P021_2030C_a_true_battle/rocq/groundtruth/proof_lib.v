Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Import ListNotations.
Local Open Scope Z_scope.
Require Import Coq.micromega.Lia.
Require Export PVbench.Codeforces.examples_shard00.P021_2030C_a_true_battle.rocq.spec_lib.
Require Export PVbench.Codeforces.examples_shard00.P021_2030C_a_true_battle.rocq.helper_lib.

Lemma no_adjacent_ones_before_succ__loop_transition :
  forall (values : list Z) (i : Z),
    0 <= i ->
    NoAdjacentOnesBefore values i ->
    (Znth i values 0 <> 49 \/ Znth (i + 1) values 0 <> 49) ->
    NoAdjacentOnesBefore values (i + 1).
Proof.
  unfold NoAdjacentOnesBefore.
  intros values i Hi Hold Hnew k Hk.
  destruct (Z_lt_ge_dec k i) as [Hlt | Hge].
  - apply Hold. lia.
  - assert (k = i) by lia.
    subst k.
    exact Hnew.
Qed.
Lemma spec_zero_from_completed_scan__final_results :
  forall (values : list Z) (n i : Z),
    n = Zlength values ->
    0 <= i ->
    i <= n - 1 ->
    i + 1 >= n ->
    Znth 0 values 0 <> 49 ->
    Znth (Zlength values - 1) values 0 <> 49 ->
    NoAdjacentOnesBefore values i ->
    Spec values 0.
Proof.
  intros values n i Hn Hi0 Hi_upper Hi_done Hfirst Hlast Hscan.
  assert (Hi : i = n - 1) by lia.
  unfold Spec.
  split.
  - left; reflexivity.
  - split.
    + lia.
    + intro Hwin.
      exfalso.
      unfold WinningCriterion in Hwin.
      destruct Hwin as [Hwin | [Hwin | Hwin]].
      * exact (Hfirst Hwin).
      * exact (Hlast Hwin).
      * unfold HasAdjacentOnes in Hwin.
        destruct Hwin as [j [Hj0 [Hj_bound [Hj Hjsucc]]]].
        specialize (Hscan j).
        assert (Hj_before : 0 <= j < i) by lia.
        specialize (Hscan Hj_before).
        destruct Hscan as [Hneq | Hneq].
        -- exact (Hneq Hj).
        -- exact (Hneq Hjsucc).
Qed.
