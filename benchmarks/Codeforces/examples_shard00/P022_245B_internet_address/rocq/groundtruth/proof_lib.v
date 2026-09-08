Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.
Require Import Coq.micromega.Psatz.
Require Export PVbench.Codeforces.examples_shard00.P022_245B_internet_address.rocq.spec_lib.

Lemma Forall_firstn__final_semantic :
  forall (A : Type) (P : A -> Prop) (n : nat) (l : list A),
    Forall P l -> Forall P (firstn n l).
Proof.
  intros A P n.
  induction n as [|n IH]; intros l Hall.
  - simpl. constructor.
  - destruct l as [|x xs].
    + simpl. constructor.
    + inversion Hall; subst.
      simpl. constructor; auto.
Qed.
Lemma Forall_skipn__final_semantic :
  forall (A : Type) (P : A -> Prop) (n : nat) (l : list A),
    Forall P l -> Forall P (skipn n l).
Proof.
  intros A P n.
  induction n as [|n IH]; intros l Hall.
  - simpl. exact Hall.
  - destruct l as [|x xs].
    + simpl. constructor.
    + inversion Hall; subst.
      simpl. apply IH. assumption.
Qed.
Lemma restored_address_with_context__final_semantic :
  forall (plain protocol domain context : list Z),
    (protocol = [104; 116; 116; 112] \/ protocol = [102; 116; 112]) ->
    LowercaseNonempty domain ->
    LowercaseNonempty context ->
    plain = protocol ++ domain ++ [114; 117] ++ context ->
    RestoredInternetAddress plain
      (protocol ++ [58; 47; 47] ++ domain ++
       [46; 114; 117] ++ [47] ++ context).
Proof.
  intros plain protocol domain context Hprotocol Hdomain Hcontext Hplain.
  unfold RestoredInternetAddress.
  exists protocol, domain, context.
  split.
  - exact Hprotocol.
  - split.
    + exact Hdomain.
    + split.
      * right. exact Hcontext.
      * split.
        -- exact Hplain.
        -- destruct Hcontext as [Hcontext _].
           destruct context as [|c context].
           ++ rewrite Zlength_nil in Hcontext. lia.
           ++ reflexivity.
Qed.
Lemma restored_address_without_context__final_semantic :
  forall (plain protocol domain : list Z),
    (protocol = [104; 116; 116; 112] \/ protocol = [102; 116; 112]) ->
    LowercaseNonempty domain ->
    plain = protocol ++ domain ++ [114; 117] ->
    RestoredInternetAddress plain
      (protocol ++ [58; 47; 47] ++ domain ++ [46; 114; 117]).
Proof.
  intros plain protocol domain Hprotocol Hdomain Hplain.
  unfold RestoredInternetAddress.
  exists protocol, domain, [].
  split.
  - exact Hprotocol.
  - split.
    + exact Hdomain.
    + split.
      * left. reflexivity.
      * split.
        -- rewrite app_nil_r. exact Hplain.
        -- reflexivity.
Qed.
