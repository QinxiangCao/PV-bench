Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Require Import Coq.micromega.Lia.
Require Export PVbench.Algorithms.sliding_window_maximum.rocq.spec_lib.
Require Export PVbench.Algorithms.sliding_window_maximum.rocq.helper_lib.

Lemma replace_Znth_append_bounds__value_loop_exit_and_append :
  forall q_l head tail i n,
    Zlength q_l = n ->
    0 <= head <= tail ->
    tail <= i < n ->
    (forall pos, head <= pos < tail -> 0 <= Znth pos q_l 0 < n) ->
    forall pos, head <= pos < tail + 1 ->
      0 <= Znth pos (replace_Znth tail i q_l) 0 < n.
Proof.
  intros q_l head tail i n Hlen Hht Hit Hold pos Hpos.
  assert (Htail : 0 <= tail < Zlength q_l) by lia.
  destruct (Z.eq_dec pos tail) as [-> | Hne].
  - rewrite Znth_replace_Znth_Same by exact Htail. lia.
  - rewrite Znth_replace_Znth_Diff; try lia.
    apply Hold. lia.
Qed.
Lemma queue_append_state__value_loop_exit_and_append :
  forall l q_l head tail i k,
    Zlength l = Zlength q_l ->
    1 <= k ->
    0 <= i < Zlength l ->
    0 <= head <= tail ->
    tail <= i ->
    SWMQueuePendingState l q_l head tail i k ->
    (head < tail ->
      Znth (Znth (tail - 1) q_l 0) l 0 > Znth i l 0) ->
    SWMQueueState l (replace_Znth tail i q_l) head (tail + 1) (i + 1) k.
Proof.
  intros l q_l head tail i k Hlen Hkpos Hi Hht Hti
    [Hentries [Hinc [Hdec Hcovers]]] Hlast.
  assert (Htail : 0 <= tail < Zlength q_l) by lia.
  assert (Hsame : Znth tail (replace_Znth tail i q_l) 0 = i).
  { apply Znth_replace_Znth_Same. lia. }
  assert (Hdiff : forall p, head <= p < tail ->
      Znth p (replace_Znth tail i q_l) 0 = Znth p q_l 0).
  { intros p Hp. apply Znth_replace_Znth_Diff; lia. }
  unfold SWMQueueState.
  split.
  - unfold SWMQueueEntriesInWindow.
    intros p Hp.
    destruct (Z.eq_dec p tail) as [-> | Hne].
    + rewrite Hsame. lia.
    + rewrite Hdiff by lia.
      specialize (Hentries p ltac:(lia)).
      lia.
  - split.
    + unfold SWMQueueIndexIncreasing.
      intros p q [Hhp [Hpq Hqt]].
      destruct (Z.eq_dec q tail) as [-> | Hqne].
      * rewrite Hsame, Hdiff by lia.
        specialize (Hentries p ltac:(lia)). lia.
      * rewrite Hdiff by lia. rewrite Hdiff by lia.
        apply Hinc. lia.
    + split.
      * unfold SWMQueueValueDecreasing.
        intros p q [Hhp [Hpq Hqt]].
        destruct (Z.eq_dec q tail) as [-> | Hqne].
        -- rewrite Hsame, Hdiff by lia.
           destruct (Z.eq_dec p (tail - 1)) as [-> | Hpne].
           ++ apply Hlast. lia.
           ++ pose proof (Hdec p (tail - 1) ltac:(lia)) as Hp_last.
              pose proof (Hlast ltac:(lia)) as Hlast_i.
              lia.
        -- rewrite Hdiff by lia. rewrite Hdiff by lia.
           apply Hdec. lia.
      * split.
        -- unfold SWMQueueCoversWindow.
           intros idx Hidx Hwin.
           destruct (Z.eq_dec idx i) as [-> | Hidxne].
           ++ exists tail. rewrite Hsame. repeat split; lia.
           ++ specialize (Hcovers idx Hidx ltac:(lia)).
              destruct Hcovers as [[p [Hp [Hip Hval]]] | Hval].
              ** exists p. split; [lia|].
                 split.
                 --- rewrite Hdiff by lia. lia.
                 --- rewrite Hdiff by lia. exact Hval.
              ** exists tail. rewrite Hsame. repeat split; lia.
        -- intros [Hnonempty Hk].
           unfold WindowMaxValue.
           exists (Znth head (replace_Znth tail i q_l) 0).
           assert (Hheadpos : head <= head < tail + 1) by lia.
           assert (Hheadwin := Hentries).
           unfold SWMQueueEntriesInOpenWindow in Hheadwin.
           destruct (Z.eq_dec head tail) as [Heq | Hneq].
           ++ subst head. rewrite Hsame. repeat split; try lia.
              intros idx Hidx.
              destruct (Z.eq_dec idx i) as [-> | Hidxne]; try lia.
              specialize (Hcovers idx ltac:(lia) ltac:(lia)).
              destruct Hcovers as [[p [Hp [Hip Hval]]] | Hval]; try lia.
           ++ rewrite Hdiff by lia.
              split.
              ** specialize (Hheadwin head ltac:(lia)). lia.
              ** split; [reflexivity|].
                 intros idx Hidx.
                 destruct (Z.eq_dec idx i) as [-> | Hidxne].
                 --- destruct (Z.eq_dec head (tail - 1)) as [Heqhead | Hnehead].
                     +++ subst head. pose proof (Hlast ltac:(lia)). lia.
                     +++ pose proof (Hdec head (tail - 1) ltac:(lia)) as Hheadlast.
                         pose proof (Hlast ltac:(lia)) as Hlasti.
                         lia.
                 --- specialize (Hcovers idx ltac:(lia) ltac:(lia)).
                     destruct Hcovers as [[p [Hp [Hip Hval]]] | Hval].
                      +++ destruct (Z.eq_dec p head) as [-> | Hpne]; try exact Hval.
                          eapply Z.le_trans; [exact Hval|].
                          pose proof (Hdec head p ltac:(lia)) as Hheadp.
                          lia.
                      +++ eapply Z.le_trans; [exact Hval|].
                          destruct (Z.eq_dec head (tail - 1)) as [Heqhead | Hnehead].
                          *** subst head. pose proof (Hlast ltac:(lia)) as Hlasti. lia.
                          *** pose proof (Hdec head (tail - 1) ltac:(lia)) as Hheadlast.
                              pose proof (Hlast ltac:(lia)) as Hlasti.
                              lia.
Qed.
Lemma queue_append_storage__value_loop_exit_and_append :
  forall l q_l head tail i,
    Zlength q_l = Zlength l ->
    0 <= i < Zlength l ->
    0 <= head <= tail ->
    tail <= i ->
    (forall pos, head <= pos < tail ->
      0 <= Znth pos q_l 0 < Zlength l) ->
    SWMQueueStorageSafe l (replace_Znth tail i q_l)
      head (tail + 1) (i + 1).
Proof.
  intros l q_l head tail i Hlen Hi Hht Hti Hb.
  unfold SWMQueueStorageSafe.
  split.
  - rewrite Zlength_replace_Znth. exact Hlen.
  - split; [lia|].
    split; [lia|].
    split; [lia|].
    intros pos Hpos.
    eapply replace_Znth_append_bounds__value_loop_exit_and_append;
      try eassumption; lia.
Qed.
Lemma Znth_app_left__window_output_append :
  forall (l1 l2 : list Z) (d i : Z),
    0 <= i < Zlength l1 ->
    Znth i (l1 ++ l2) d = Znth i l1 d.
Proof.
  intros l1 l2 d i Hi.
  unfold Znth.
  rewrite app_nth1; [reflexivity |].
  rewrite Zlength_correct in Hi.
  lia.
Qed.
Lemma Znth_app_last__window_output_append :
  forall (l : list Z) (d x : Z),
    Znth (Zlength l) (l ++ [x]) d = x.
Proof.
  intros l d x.
  unfold Znth.
  rewrite app_nth2.
  - rewrite Zlength_correct.
    replace (Z.to_nat (Z.of_nat (length l)) - length l)%nat with 0%nat by lia.
    reflexivity.
  - rewrite Zlength_correct.
    lia.
Qed.
Lemma SWMOutputPrefix_app_single__window_output_append :
  forall l k out_idx out value,
    SWMOutputPrefixShape l k out_idx out ->
    SWMOutputPrefix l k out_idx out ->
    WindowMaxValue l out_idx (out_idx + k) value ->
    SWMOutputPrefix l k (out_idx + 1) (out ++ [value]).
Proof.
  intros l k out_idx out value Hshape Hprefix Hvalue.
  destruct Hshape as [_ [_ [_ Hlen]]].
  unfold SWMOutputPrefix in *.
  intros idx Hidx.
  destruct (Z_lt_ge_dec idx out_idx) as [Hlt | Hge].
  - rewrite Znth_app_left__window_output_append by (rewrite Hlen; lia).
    apply Hprefix. lia.
  - assert (idx = out_idx) by lia.
    subst idx.
    assert (HZ : Znth out_idx (out ++ [value]) 0 = value).
    { rewrite <- Hlen. apply Znth_app_last__window_output_append. }
    rewrite HZ.
    exact Hvalue.
Qed.
Lemma SWMOutputPrefixShape_app_single__window_output_append :
  forall l k out_idx out value,
    SWMOutputPrefixShape l k out_idx out ->
    out_idx < Zlength l - k + 1 ->
    SWMOutputPrefixShape l k (out_idx + 1) (out ++ [value]).
Proof.
  intros l k out_idx out value [Hk [Hkl [Hidx Hlen]]] Hroom.
  unfold SWMOutputPrefixShape.
  split; [exact Hk |].
  split; [exact Hkl |].
  split; [lia |].
  rewrite Zlength_app_cons. lia.
Qed.

Lemma drop_loop_remove_expired_head__head_drop_transitions :
  forall l q_l head tail i k,
    head < tail ->
    Znth head q_l 0 <= i - k ->
    SWMQueueDropLoopState l q_l head tail i k ->
    SWMQueueDropLoopState l q_l (head + 1) tail i k.
Proof.
  intros l q_l head tail i k Hnonempty Hexpired
    [Hentries [Hindices [Hvalues Hcovers]]].
  unfold SWMQueueDropLoopState.
  split.
  - unfold SWMQueueEntriesInWindow in *.
    intros pos0 Hpos0. apply Hentries. lia.
  - split.
    + unfold SWMQueueIndexIncreasing in *.
      intros p0 q0 Hp0. apply Hindices. lia.
    + split.
      * unfold SWMQueueValueDecreasing in *.
        intros p0 q0 Hp0. apply Hvalues. lia.
      * unfold SWMQueueCoversOpenWindow in *.
        intros idx Hidx Hwindow.
        destruct (Hcovers idx Hidx Hwindow)
          as [cover_pos [Hcover_pos [Hidx_pos Hvalue]]].
        destruct (Z.eq_dec cover_pos head) as [Heq | Hneq].
        -- subst cover_pos. lia.
        -- exists cover_pos. split; [lia |].
           split; assumption.
Qed.
Lemma drop_loop_exit_nonexpired__head_drop_transitions :
  forall l q_l head tail i k,
    head < tail ->
    i - k < Znth head q_l 0 ->
    SWMQueueDropLoopState l q_l head tail i k ->
    SWMQueueAfterDrop l q_l head tail i k.
Proof.
  intros l q_l head tail i k Hnonempty Hhead_open
    [Hentries [Hindices [Hvalues Hcovers]]].
  unfold SWMQueueAfterDrop.
  split.
  - unfold SWMQueueEntriesInWindow in Hentries.
    unfold SWMQueueEntriesInOpenWindow.
    intros pos0 Hpos0.
    pose proof (Hentries pos0 Hpos0) as Hentry.
    destruct (Z.eq_dec pos0 head) as [-> | Hneq].
    + lia.
    + unfold SWMQueueIndexIncreasing in Hindices.
      pose proof (Hindices head pos0 ltac:(lia)) as Hafter_head.
      lia.
  - split; [exact Hindices |].
    split; [exact Hvalues | exact Hcovers].
Qed.
Lemma SWMQueuePendingState_drop_tail__pending_and_tail_drop :
  forall l q_l head tail i k,
    head < tail ->
    Znth (Znth (tail - 1) q_l 0) l 0 <= Znth i l 0 ->
    SWMQueuePendingState l q_l head tail i k ->
    SWMQueuePendingState l q_l head (tail - 1) i k.
Proof.
  intros l q_l head tail i k Hnonempty Hdom
    [Hentries [Hindices [Hvalues Hcovers]]].
  unfold SWMQueuePendingState.
  split.
  - intros pos Hpos. apply Hentries. lia.
  - split.
    + intros p q Hpq. apply Hindices. lia.
    + split.
      * intros p q Hpq. apply Hvalues. lia.
      * intros idx Hidx Hwindow.
        specialize (Hcovers idx Hidx Hwindow).
        destruct Hcovers as [[candidate [Hpos [Hidxpos Hvalue]]] | Hpending].
        -- destruct (Z_lt_ge_dec candidate (tail - 1)) as [Hkept | Hdropped].
           ++ left. exists candidate.
              split; [lia |].
              split; [lia | exact Hvalue].
           ++ right.
              assert (candidate = tail - 1) by lia.
              subst candidate.
              lia.
        -- right. exact Hpending.
Qed.
