Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Local Open Scope Z_scope.
Require Import Coq.micromega.Lia.
Require Export PVbench.Codeforces.examples_shard00.P036_1705C_mark_and_his_unfinished_essay.rocq.spec_lib.
Require Export PVbench.Codeforces.examples_shard00.P036_1705C_mark_and_his_unfinished_essay.rocq.helper_lib.

Lemma copy_paste_states_length_pow_bound__copy_state_transition :
  forall text ops states k,
    CopyPasteStates text ops states ->
    Zlength text <= 200000 ->
    0 <= k <= Zlength ops ->
    Zlength (Znth k states nil) <= 200000 * 2 ^ k.
Proof.
  intros text ops states k Hstates Htext Hk.
  destruct Hstates as [Hstates_len [Hinitial Hstep]].
  assert (Hk_nat : k = Z.of_nat (Z.to_nat k)) by lia.
  remember (Z.to_nat k) as n eqn:Hn.
  subst k.
  clear Hn.
  revert Hk.
  induction n as [|n IH]; intros Hk.
  - change (Zlength (Znth 0 states nil) <= 200000 * 2 ^ 0).
    rewrite Z.pow_0_r, Hinitial.
    nia.
  - rewrite Nat2Z.inj_succ in *.
    specialize (IH ltac:(lia)).
    specialize (Hstep (Z.of_nat n) ltac:(lia)).
    destruct Hstep as [[Hleft Hright] [Hright_bound Hnext]].
    replace (Z.succ (Z.of_nat n)) with (Z.of_nat n + 1) by lia.
    rewrite Hnext.
    unfold CopyPasteStep.
    rewrite Zlength_app, Zlength_sublist by lia.
    replace (Z.of_nat n + 1) with (Z.succ (Z.of_nat n)) by lia.
    rewrite Z.pow_succ_r by lia.
    nia.
Qed.
Lemma Znth_app_left__copy_state_transition :
  forall (l1 l2 : list Z) (d j : Z),
    0 <= j < Zlength l1 ->
    Znth j (l1 ++ l2) d = Znth j l1 d.
Proof.
  intros l1 l2 d j Hj.
  unfold Znth.
  rewrite app_nth1; [reflexivity |].
  rewrite Zlength_correct in Hj.
  lia.
Qed.
Lemma Znth_app_last__copy_state_transition :
  forall (l : list Z) (d x : Z),
    Znth (Zlength l) (l ++ x :: nil) d = x.
Proof.
  intros l d x.
  unfold Znth.
  rewrite app_nth2.
  - rewrite Zlength_correct.
    replace (Z.to_nat (Z.of_nat (Datatypes.length l)) - Datatypes.length l)%nat
      with 0%nat by lia.
    reflexivity.
  - rewrite Zlength_correct.
    lia.
Qed.
Lemma CopyPasteStates_prefix_fold__backtrack_transitions :
  forall s ops states i,
    CopyPasteStates s ops states ->
    0 <= i <= Zlength ops ->
    Znth i states nil =
      fold_left CopyPasteStep (sublist 0 i ops) s.
Proof.
  intros s ops states i Hstates [Hi0 Hiupper].
  destruct Hstates as [Hlen [Hzero Hstep]].
  assert (Hbase : 0 <= i) by exact Hi0.
  revert Hi0 Hiupper.
  pattern i.
  apply Z_lt_induction.
  intros x IH Hxnonneg Hxupper.
  destruct (Z.eq_dec x 0) as [-> | Hx0].
  - rewrite Hzero.
    reflexivity.
  - specialize (Hstep (x - 1) ltac:(lia)).
    destruct Hstep as [_ [_ Hstep]].
    replace (x - 1 + 1) with x in Hstep by lia.
    rewrite Hstep.
    rewrite (IH (x - 1)) by lia.
    rewrite (sublist_split 0 x (x - 1) ops) by lia.
    assert (Hsingle : sublist (x - 1) x ops =
                      (Znth (x - 1) ops (0, 0) :: nil)%list).
    { replace x with (x - 1 + 1) by lia.
      replace (x - 1 + 1 - 1) with (x - 1) by lia.
      apply sublist_single.
      lia. }
    rewrite Hsingle.
    rewrite fold_left_app.
    simpl.
    reflexivity.
  - exact Hbase.
Qed.
Lemma Forall_Znth_in_range__backtrack_transitions :
  forall (A : Type) (P : A -> Prop) l d i,
    Forall P l ->
    0 <= i < Zlength l ->
    P (Znth i l d).
Proof.
  intros A P l d i Hforall Hi.
  apply (proj1 (Forall_forall P l) Hforall).
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hi.
  lia.
Qed.
Lemma CopyPasteStates_final_fold__backtrack_transitions :
  forall s ops states,
    CopyPasteStates s ops states ->
    Znth (Zlength ops) states nil = fold_left CopyPasteStep ops s.
Proof.
  intros s ops states Hstates.
  rewrite (CopyPasteStates_prefix_fold__backtrack_transitions s ops states
             (Zlength ops) Hstates)
    by (pose proof (Zlength_nonneg ops); lia).
  rewrite (sublist_self ops (Zlength ops)) by reflexivity.
  reflexivity.
Qed.
Lemma CopyPasteStates_length_at__backtrack_transitions :
  forall s ops states i,
    CopyPasteStates s ops states ->
    0 <= i <= Zlength ops ->
    Zlength (Znth i states nil) <= Zlength s * 2 ^ i.
Proof.
  intros s ops states i Hstates [Hi0 Hiupper].
  destruct Hstates as [Hstates_len [Hstates_zero Hstates_step]].
  assert (Hbase : 0 <= i) by exact Hi0.
  revert Hi0 Hiupper.
  pattern i.
  apply Z_lt_induction.
  - intros x IH Hxnonneg Hxupper.
    destruct (Z.eq_dec x 0) as [-> | Hx0].
    + rewrite Hstates_zero.
      simpl.
      nia.
    + specialize (Hstates_step (x - 1) ltac:(lia)).
      destruct Hstates_step as [Hop_lr [Hop_r Htransition]].
      replace (x - 1 + 1) with x in Htransition by lia.
      rewrite Htransition.
      unfold CopyPasteStep.
      rewrite Zlength_app.
      rewrite Zlength_sublist by lia.
      pose proof (IH (x - 1) ltac:(lia) ltac:(lia) ltac:(lia)) as Hprev.
      replace x with (Z.succ (x - 1)) by lia.
      rewrite Z.pow_succ_r by lia.
      replace (Z.succ (x - 1) - 1) with (x - 1) by lia.
      nia.
  - exact Hbase.
Qed.
Lemma CopyPasteStates_final_length_bound__backtrack_transitions :
  forall s ops states,
    Zlength s <= 200000 ->
    Zlength ops <= 40 ->
    CopyPasteStates s ops states ->
    Zlength (Znth (Zlength ops) states nil) <= 219902325555200000.
Proof.
  intros s ops states Hs Hops Hstates.
  pose proof (CopyPasteStates_length_at__backtrack_transitions
                s ops states (Zlength ops) Hstates
                ltac:(pose proof (Zlength_nonneg ops); lia)) as Hlength.
  assert (Hpow : 2 ^ Zlength ops <= 2 ^ 40).
  { apply Z.pow_le_mono_r; lia. }
  change (2 ^ Zlength ops <= 1099511627776) in Hpow.
  pose proof (Zlength_nonneg s).
  nia.
Qed.
