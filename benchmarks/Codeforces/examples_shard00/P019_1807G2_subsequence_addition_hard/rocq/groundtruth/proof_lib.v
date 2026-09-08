Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Operators.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Import ListNotations.
Local Open Scope Z_scope.
Require Import Coq.Sorting.Permutation.
Require Import Coq.micromega.Lia.
Require Export PVbench.Codeforces.examples_shard00.P019_1807G2_subsequence_addition_hard.rocq.spec_lib.
Require Export PVbench.Codeforces.examples_shard00.P019_1807G2_subsequence_addition_hard.rocq.helper_lib.

Lemma sorted_index_bounds_from_permutation__prefix_state :
  forall (input sorted : list Z) lo hi,
    (forall i, 0 <= i < Zlength input ->
      lo <= Znth i input 0 <= hi) ->
    Permutation input sorted ->
    forall i, 0 <= i < Zlength sorted ->
      lo <= Znth i sorted 0 <= hi.
Proof.
  intros input sorted lo hi Hbounds Hperm i Hi.
  apply (proj1 (Forall_Znth (fun x => lo <= x <= hi) 0 sorted)).
  - eapply Permutation_Forall.
    + exact Hperm.
    + apply (proj2 (Forall_Znth (fun x => lo <= x <= hi) 0 input)).
      exact Hbounds.
  - exact Hi.
Qed.
Lemma sum_sublist_succ__prefix_state :
  forall (xs : list Z) i,
    0 <= i < Zlength xs ->
    ListLib.sum (sublist 0 (i + 1) xs) =
      ListLib.sum (sublist 0 i xs) + Znth i xs 0.
Proof.
  intros xs i Hi.
  rewrite (sublist_split 0 (i + 1) i xs) by lia.
  rewrite (sublist_single 0 i xs) by lia.
  rewrite ListLib.sum_app.
  simpl.
  lia.
Qed.
Lemma prefix_state_at_end_sorted_acceptance__decision_results :
  forall sorted processed total,
    Zlength sorted <= processed ->
    PrefixAdditionState sorted processed total ->
    SortedAcceptance sorted.
Proof.
  intros sorted processed total Hend Hstate.
  unfold PrefixAdditionState in Hstate.
  unfold SortedAcceptance.
  destruct Hstate as [[Hprocessed_pos Hprocessed_bound]
    [Htotal [Hhead Hprefix]]].
  repeat split.
  - lia.
  - exact Hhead.
  - intros j Hj.
    apply Hprefix.
    lia.
Qed.
Lemma prefix_state_violation_not_sorted_acceptance__decision_results :
  forall sorted processed total,
    processed < Zlength sorted ->
    PrefixAdditionState sorted processed total ->
    Znth processed sorted 0 > total ->
    ~ SortedAcceptance sorted.
Proof.
  intros sorted processed total Hprocessed_lt Hstate Hviolation Haccept.
  unfold PrefixAdditionState in Hstate.
  unfold SortedAcceptance in Haccept.
  destruct Hstate as [[Hprocessed_pos Hprocessed_bound]
    [Htotal [Hhead Hprefix]]].
  destruct Haccept as [Hlength [Haccepted_head Haccepted_prefix]].
  specialize (Haccepted_prefix processed).
  rewrite Htotal in Hviolation.
  lia.
Qed.
