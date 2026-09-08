Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Import ListNotations.
Local Open Scope Z_scope.
Require Import Coq.micromega.Lia.
Require Export PVbench.Codeforces.examples_shard00.P014_1784A_monsters_easy_version.rocq.spec_lib.
Require Export PVbench.Codeforces.examples_shard00.P014_1784A_monsters_easy_version.rocq.helper_lib.

Lemma Forall_Znth_bounds__greedy_transitions :
  forall (xs : list Z) lo hi,
    (forall i, 0 <= i < Zlength xs -> lo <= Znth i xs 0 <= hi) ->
    Forall (fun x => lo <= x <= hi) xs.
Proof.
  intros xs lo hi H.
  apply (proj2 (Forall_Znth (fun x => lo <= x <= hi) 0 xs)).
  exact H.
Qed.
Lemma Forall_Znth_elim__greedy_transitions :
  forall (xs : list Z) lo hi i,
    Forall (fun x => lo <= x <= hi) xs ->
    0 <= i < Zlength xs ->
    lo <= Znth i xs 0 <= hi.
Proof.
  intros xs lo hi i H Hrange.
  apply (proj1 (Forall_Znth (fun x => lo <= x <= hi) 0 xs) H i Hrange).
Qed.
Lemma last_app_singleton__greedy_transitions :
  forall (xs : list Z) d x,
    last (xs ++ [x]) d = x.
Proof.
  induction xs as [| a xs IH]; intros d x; simpl; auto.
  destruct xs; simpl in *; auto.
Qed.
Lemma ZListSum_app__greedy_transitions :
  forall xs ys,
    ZListSum (xs ++ ys) = ZListSum xs + ZListSum ys.
Proof.
  induction xs as [| x xs IH]; intros ys; simpl.
  - reflexivity.
  - rewrite IH. lia.
Qed.
Lemma last_as_Znth__greedy_transitions :
  forall (xs : list Z) d,
    0 < Zlength xs ->
    last xs d = Znth (Zlength xs - 1) xs d.
Proof.
  induction xs as [| a xs IH]; intros d Hlen.
  - rewrite Zlength_nil in Hlen. lia.
  - destruct xs as [| b xs].
    + reflexivity.
    + change (last (b :: xs) d =
        Znth (Zlength (a :: b :: xs) - 1) (a :: b :: xs) d).
      assert (Htailpos : 0 < Zlength (b :: xs)).
      { rewrite Zlength_cons. pose proof (Zlength_nonneg xs). lia. }
      assert (Hidxpos : Zlength (a :: b :: xs) - 1 > 0).
      { rewrite !Zlength_cons. pose proof (Zlength_nonneg xs). lia. }
      rewrite Znth_cons by exact Hidxpos.
      replace (Zlength (a :: b :: xs) - 1 - 1) with
          (Zlength (b :: xs) - 1) by (rewrite !Zlength_cons; lia).
      apply IH.
      exact Htailpos.
Qed.
Lemma maximal_cascade_preparation_app_step__greedy_transitions :
  forall health prepared hp,
    MaximalCascadePreparation health prepared ->
    1 <= hp ->
    MaximalCascadePreparation
      (health ++ [hp])
      (prepared ++ [Z.min (last prepared 0 + 1) hp]).
Proof.
  intros health prepared hp [Hprep Hmax] Hhp.
  destruct Hprep as [Hlen [Hbounds [Hfirst Hadj]]].
  set (cap := Z.min (last prepared 0 + 1) hp).
  assert (Hlast_nonneg : 0 <= last prepared 0).
  { destruct prepared as [| p ps].
    - reflexivity.
    - assert (Hidx : 0 <= Zlength (p :: ps) - 1 < Zlength (p :: ps)).
      { rewrite Zlength_cons. pose proof (Zlength_nonneg ps). lia. }
      specialize (Hbounds (Zlength (p :: ps) - 1) ltac:(lia)).
      rewrite <- (last_as_Znth__greedy_transitions (p :: ps) 0) in Hbounds.
      + lia.
      + rewrite Zlength_cons. pose proof (Zlength_nonneg ps). lia. }
  assert (Hcap_low : 1 <= cap).
  { unfold cap. apply Z.min_glb; lia. }
  assert (Hcap_hp : cap <= hp).
  { unfold cap. apply Z.le_min_r. }
  assert (Hcap_last : cap <= last prepared 0 + 1).
  { unfold cap. apply Z.le_min_l. }
  split.
  - unfold CascadePreparation.
    split.
    + rewrite !Zlength_app_cons. lia.
    + split.
      * intros j Hj.
        rewrite Zlength_app_cons in Hj.
        destruct (Z_lt_ge_dec j (Zlength prepared)).
        -- rewrite !app_Znth1 by lia. apply Hbounds. lia.
        -- assert (j = Zlength prepared) by lia. subst j.
           rewrite !app_Znth2 by lia.
           rewrite Hlen.
           replace (Zlength health - Zlength health) with 0 by lia.
           simpl. exact (conj Hcap_low Hcap_hp).
      * split.
        -- intros _.
           destruct prepared as [| p ps].
           ++ change (cap <= 1). unfold cap. simpl.
              rewrite Z.min_l by lia. lia.
           ++ rewrite app_Znth1 by (rewrite Zlength_cons; pose proof (Zlength_nonneg ps); lia).
              apply Hfirst. rewrite Zlength_cons. pose proof (Zlength_nonneg ps). lia.
        -- intros j Hj.
           rewrite Zlength_app_cons in Hj.
           destruct (Z_lt_ge_dec j (Zlength prepared - 1)).
           ++ rewrite !app_Znth1 by lia. apply Hadj. lia.
           ++ assert (j = Zlength prepared - 1) by lia. subst j.
              assert (0 < Zlength prepared) by lia.
              rewrite app_Znth2 by lia.
              rewrite app_Znth1 by lia.
              replace (Zlength prepared - 1 + 1 - Zlength prepared) with 0 by lia.
              simpl.
              rewrite <- (last_as_Znth__greedy_transitions prepared 0 H).
              exact Hcap_last.
  - intros alternative Halt j Hj.
    destruct Halt as [Haltlen [Haltbounds [Haltfirst Haltadj]]].
    assert (Haltlen' : Zlength alternative = Zlength health + 1).
    { rewrite Haltlen, Zlength_app_cons. reflexivity. }
    rewrite Zlength_app_cons in Hj.
    destruct (Z_lt_ge_dec j (Zlength prepared)).
    + rewrite app_Znth1 by lia.
      assert (Hhealthlen : Zlength health = Zlength prepared) by lia.
      assert (Haltprefix :
        CascadePreparation health (sublist 0 (Zlength health) alternative)).
      { unfold CascadePreparation.
        split.
        - rewrite Zlength_sublist0; lia.
        - split.
          + intros k Hk.
            rewrite Znth_sublist0 by lia.
            specialize (Haltbounds k).
            rewrite Zlength_app_cons in Haltbounds.
            rewrite app_Znth1 in Haltbounds by lia.
            apply Haltbounds. lia.
          + split.
            * intros Hpositive.
              rewrite Znth_sublist0 by lia.
              apply Haltfirst. rewrite Haltlen, Zlength_app_cons. lia.
            * intros k Hk.
              rewrite Zlength_sublist0 in Hk by lia.
              rewrite !Znth_sublist0 by lia.
              apply Haltadj.
              rewrite Haltlen, Zlength_app_cons. lia. }
      specialize (Hmax (sublist 0 (Zlength health) alternative) Haltprefix j).
      rewrite Znth_sublist0 in Hmax by lia.
      apply Hmax. lia.
    + assert (j = Zlength prepared) by lia. subst j.
      rewrite app_Znth2 by lia.
      replace (Zlength prepared - Zlength prepared) with 0 by lia.
      simpl.
      assert (Hhealthlen : Zlength health = Zlength prepared) by lia.
      assert (Haltfinal_bounds := Haltbounds (Zlength prepared)).
      rewrite Zlength_app_cons in Haltfinal_bounds.
      rewrite app_Znth2 in Haltfinal_bounds by lia.
      rewrite Hhealthlen in Haltfinal_bounds.
      replace (Zlength prepared - Zlength prepared) with 0 in Haltfinal_bounds by lia.
      simpl in Haltfinal_bounds.
      specialize (Haltfinal_bounds ltac:(lia)).
      destruct (Z.eq_dec (Zlength prepared) 0) as [Hzero | Hnonzero].
      * assert (Zlength prepared = 0) by lia.
        assert (Zlength alternative = 1) by
          (rewrite Haltlen, Zlength_app_cons; lia).
        specialize (Haltfirst ltac:(lia)).
        apply Zlength_nil_inv in H. subst prepared.
        unfold cap. simpl. rewrite Z.min_l by exact Hhp.
        exact Haltfirst.
      * assert (Hpos : 0 < Zlength prepared) by
          (pose proof (Zlength_nonneg prepared); lia).
        assert (Haltprev :
          Znth (Zlength prepared - 1) alternative 0 <= last prepared 0).
        { assert (Haltprefix :
            CascadePreparation health (sublist 0 (Zlength health) alternative)).
          { unfold CascadePreparation.
            split.
            - rewrite Zlength_sublist0; lia.
            - split.
              + intros k Hk.
                rewrite Znth_sublist0 by lia.
                specialize (Haltbounds k).
                rewrite Zlength_app_cons in Haltbounds.
                rewrite app_Znth1 in Haltbounds by lia.
                apply Haltbounds. lia.
              + split.
                * intros Hpositive.
                  rewrite Znth_sublist0 by lia.
                  apply Haltfirst. rewrite Haltlen, Zlength_app_cons. lia.
                * intros k Hk.
                  rewrite Zlength_sublist0 in Hk by lia.
                  rewrite !Znth_sublist0 by lia.
                  apply Haltadj.
                  rewrite Haltlen, Zlength_app_cons. lia. }
          specialize (Hmax (sublist 0 (Zlength health) alternative)
                            Haltprefix (Zlength prepared - 1)).
          rewrite Znth_sublist0 in Hmax by lia.
          specialize (Hmax ltac:(lia)).
          rewrite <- (last_as_Znth__greedy_transitions prepared 0 Hpos) in Hmax.
          exact Hmax. }
        specialize (Haltadj (Zlength prepared - 1)).
        specialize (Haltadj ltac:(rewrite Haltlen, Zlength_app_cons; lia)).
        replace (Zlength prepared - 1 + 1) with (Zlength prepared) in Haltadj by lia.
        unfold cap. apply Z.min_glb.
        -- lia.
        -- exact (proj2 Haltfinal_bounds).
Qed.
Lemma prefix_greedy_step__greedy_transitions :
  forall original sorted processed kept spent next,
    0 <= processed < Zlength sorted ->
    1 <= Znth processed sorted 0 ->
    FullPreparationSpecBridge original sorted ->
    PrefixGreedyState original sorted processed kept spent ->
    next = Z.min (kept + 1) (Znth processed sorted 0) ->
    PrefixGreedyState original sorted (processed + 1) next
      (spent + (Znth processed sorted 0 - next)).
Proof.
  intros original sorted processed kept spent next Hindex Hhp Hbridge
         [Hprocessed [prepared [Hmax [Hkept [Hspent Hterminal]]]]] Hnext.
  assert (Hprefix :
    sublist 0 (processed + 1) sorted =
    sublist 0 processed sorted ++ [Znth processed sorted 0]).
  { rewrite (sublist_split 0 (processed + 1) processed sorted) by lia.
    rewrite (sublist_single 0 processed sorted) by lia. reflexivity. }
  subst kept.
  assert (Hmax_next :
    MaximalCascadePreparation
      (sublist 0 (processed + 1) sorted) (prepared ++ [next])).
  { rewrite Hprefix.
    rewrite Hnext.
    apply maximal_cascade_preparation_app_step__greedy_transitions; assumption. }
  unfold PrefixGreedyState.
  split; [lia |].
  exists (prepared ++ [next]).
  split; [exact Hmax_next |].
  split.
  - symmetry. apply last_app_singleton__greedy_transitions.
  - split.
    + rewrite Hprefix.
      rewrite !ZListSum_app__greedy_transitions. simpl.
      lia.
    + intros Hfull.
      assert (Hmax_full :
        MaximalCascadePreparation sorted (prepared ++ [next])).
      { rewrite <- (sublist_self sorted (processed + 1)) by exact Hfull.
        exact Hmax_next. }
      specialize (Hbridge (prepared ++ [next]) Hmax_full).
      replace (spent + (Znth processed sorted 0 - next)) with
          (ZListSum sorted - ZListSum (prepared ++ [next])).
      * exact Hbridge.
      * rewrite <- (sublist_self sorted (processed + 1)) by exact Hfull.
        rewrite Hprefix.
        rewrite !ZListSum_app__greedy_transitions. simpl.
        rewrite Hspent.
        rewrite app_Znth2 by (rewrite Zlength_sublist0; lia).
        rewrite Zlength_sublist0 by lia.
        replace (processed - processed) with 0 by lia.
        rewrite Znth0_cons. lia.
Qed.
