Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Import ListNotations.
Local Open Scope Z_scope.
Require Import Coq.micromega.Lia.
Require Export PVbench.Codeforces.examples_shard00.P011_765A_neverending_competitions.rocq.spec_lib.

Lemma itinerary_endpoint_parity__return_parity :
  forall (home : list Z) (flights : list (list Z * list Z))
         (current : list Z),
    Forall (fun f =>
      (fst f = home /\ snd f <> home) \/
      (fst f <> home /\ snd f = home)) flights ->
    ItineraryEndsAt home flights current ->
    (current = home <-> Zlength flights mod 2 = 0).
Proof.
  intros home flights current Hflights Hitinerary.
  unfold ItineraryEndsAt in Hitinerary.
  destruct Hitinerary as
      (ordered & locations & Hperm & Hlength & Hstart & Hedges & Hend).
  assert (Hordered : Forall (fun f =>
      (fst f = home /\ snd f <> home) \/
      (fst f <> home /\ snd f = home)) ordered).
  { eapply Permutation_Forall; eauto. }
  assert (Hparity : forall k : nat,
      Z.of_nat k <= Zlength ordered ->
      (Znth (Z.of_nat k) locations [] = home <->
       Z.of_nat k mod 2 = 0)).
  {
    induction k as [| k IH]; intros Hbound.
    - simpl. rewrite Hstart. tauto.
    - rewrite Nat2Z.inj_succ.
      set (i := Z.of_nat k) in *.
      change (Znth (i + 1) locations [] = home <->
              (i + 1) mod 2 = 0).
      assert (Hi : 0 <= i) by (subst i; lia).
      assert (Histep : i < Zlength ordered) by lia.
      specialize (IH ltac:(lia)).
      specialize (Hedges i ltac:(lia)).
      destruct Hedges as [Hfrom Hto].
      assert (Hflight :
          (fst (Znth i ordered ([], [])) = home /\
           snd (Znth i ordered ([], [])) <> home) \/
          (fst (Znth i ordered ([], [])) <> home /\
           snd (Znth i ordered ([], [])) = home)).
      {
        rewrite Forall_forall in Hordered.
        apply Hordered.
        unfold Znth.
        apply nth_In.
        rewrite Zlength_correct in Histep.
        lia.
      }
      assert (Hmodstep : (i + 1) mod 2 = (i mod 2 + 1) mod 2).
      { rewrite Z.add_mod by lia. reflexivity. }
      destruct (Z.eq_dec (i mod 2) 0) as [Hieven | Hiodd].
      + assert (Hiloc : Znth i locations [] = home).
        { apply IH. exact Hieven. }
        assert (Hnextloc : Znth (i + 1) locations [] <> home).
        {
          destruct Hflight as [[Hfh Htn] | [Hfn Hth]].
          - rewrite Hto in Htn. exact Htn.
          - rewrite Hfrom in Hfn. contradiction.
        }
        assert (Hnextmod : (i + 1) mod 2 = 1).
        { rewrite Hmodstep, Hieven. reflexivity. }
        rewrite Hnextmod.
        split; intros Hcontra; [contradiction | lia].
      + assert (Himod : i mod 2 = 1).
        { pose proof (Z.mod_pos_bound i 2 ltac:(lia)); lia. }
        assert (Hiloc : Znth i locations [] <> home).
        { intro Heq. apply IH in Heq. contradiction. }
        assert (Hnextloc : Znth (i + 1) locations [] = home).
        {
          destruct Hflight as [[Hfh Htn] | [Hfn Hth]].
          - rewrite Hfrom in Hfh. contradiction.
          - rewrite Hto in Hth. exact Hth.
        }
        assert (Hnextmod : (i + 1) mod 2 = 0).
        { rewrite Hmodstep, Himod. reflexivity. }
        rewrite Hnextloc, Hnextmod.
        tauto.
  }
  assert (Hordered_length : Zlength flights = Zlength ordered).
  {
    rewrite !Zlength_correct.
    rewrite (Permutation_length Hperm).
    reflexivity.
  }
  specialize (Hparity (length ordered)).
  rewrite <- Zlength_correct in Hparity.
  specialize (Hparity ltac:(lia)).
  assert (Hend' : Znth (Zlength ordered) locations [] = current).
  {
    rewrite Hlength in Hend.
    replace (Zlength ordered + 1 - 1) with (Zlength ordered) in Hend by lia.
    exact Hend.
  }
  rewrite Hordered_length.
  rewrite <- Hend'.
  exact Hparity.
Qed.
