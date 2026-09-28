Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
From SumLib Require Import Sum.
Import ListNotations.
Local Open Scope Z_scope.

(** A valid climbing-stairs path consists only of one-step and two-step
    moves, and its moves add up to the target stair. *)
Definition IsClimbingStep (x : Z) : Prop := x = 1 \/ x = 2.

Definition ValidClimbingWay (n : Z) (xs : list Z) : Prop :=
  Forall IsClimbingStep xs /\ ListLib.sum xs = n.

(** This enumeration is used only to discharge the finiteness requirement
    of [SumLib.Sum.sum].  Its elements are the mathematical paths. *)
Fixpoint climbing_way_enum_pair (n : nat) :
    list (list Z) * list (list Z) :=
  match n with
  | O => ([[]], [[1]])
  | S k =>
      let previous := climbing_way_enum_pair k in
      (snd previous,
       map (cons 1) (snd previous) ++ map (cons 2) (fst previous))
  end.

Definition climbing_way_enum_nat (n : nat) : list (list Z) :=
  fst (climbing_way_enum_pair n).

Lemma climbing_way_enum_nat_S_S :
  forall n,
    climbing_way_enum_nat (S (S n)) =
    map (cons 1) (climbing_way_enum_nat (S n)) ++
    map (cons 2) (climbing_way_enum_nat n).
Proof.
  intro n.
  unfold climbing_way_enum_nat.
  simpl climbing_way_enum_pair.
  destruct (climbing_way_enum_pair n).
  reflexivity.
Qed.

Lemma climbing_steps_sum_nonnegative :
  forall xs,
    Forall IsClimbingStep xs -> 0 <= ListLib.sum xs.
Proof.
  intros xs Hsteps.
  induction Hsteps as [|x xs Hx Hsteps IH]; simpl.
  - lia.
  - unfold IsClimbingStep in Hx.
    destruct Hx as [-> | ->]; lia.
Qed.

Lemma climbing_steps_sum_zero_nil :
  forall xs,
    Forall IsClimbingStep xs ->
    ListLib.sum xs = 0 ->
    xs = [].
Proof.
  intros xs Hsteps Hsum.
  destruct xs as [|x tail]; [reflexivity |].
  inversion Hsteps as [|? ? Hx Htail]; subst.
  pose proof (climbing_steps_sum_nonnegative tail Htail).
  unfold IsClimbingStep in Hx.
  destruct Hx as [-> | ->].
  - change (1 + ListLib.sum tail = 0) in Hsum.
    exfalso. lia.
  - change (2 + ListLib.sum tail = 0) in Hsum.
    exfalso. lia.
Qed.

Lemma in_climbing_way_enum_nat :
  forall n xs,
    In xs (climbing_way_enum_nat n) <->
    Forall IsClimbingStep xs /\ ListLib.sum xs = Z.of_nat n.
Proof.
  assert (Hpair :
    forall n,
      (forall xs,
        In xs (climbing_way_enum_nat n) <->
        Forall IsClimbingStep xs /\ ListLib.sum xs = Z.of_nat n) /\
      (forall xs,
        In xs (climbing_way_enum_nat (S n)) <->
        Forall IsClimbingStep xs /\ ListLib.sum xs = Z.of_nat (S n))).
  {
    induction n as [|n [IHn IHSn]].
    - split.
      + intros xs. simpl.
        split.
        * intros [Heq | Hfalse].
          -- symmetry in Heq. subst xs.
             split; [constructor | reflexivity].
          -- contradiction.
        * intros [Hsteps Hsum].
          rewrite (climbing_steps_sum_zero_nil xs Hsteps Hsum).
          left. reflexivity.
      + intros xs. simpl.
        split.
        * intros [Heq | Hfalse].
          -- symmetry in Heq. subst xs.
             split.
             ++ constructor; [left; reflexivity | constructor].
             ++ reflexivity.
          -- contradiction.
        * intros [Hsteps Hsum].
          destruct xs as [|x tail]; [simpl in Hsum; lia |].
          inversion Hsteps as [|? ? Hx Htail]; subst.
          unfold IsClimbingStep in Hx.
          destruct Hx as [-> | ->].
          -- change (1 + ListLib.sum tail = 1) in Hsum.
             assert (Htail_sum : ListLib.sum tail = 0) by lia.
             rewrite (climbing_steps_sum_zero_nil tail Htail Htail_sum).
             left. reflexivity.
          -- pose proof (climbing_steps_sum_nonnegative tail Htail).
             change (2 + ListLib.sum tail = 1) in Hsum.
             exfalso. lia.
    - split.
      + exact IHSn.
      + intros xs. rewrite climbing_way_enum_nat_S_S.
        rewrite in_app_iff.
        split.
        * intros [Hin | Hin].
          -- apply in_map_iff in Hin as [tail [Heq Htail]].
             symmetry in Heq. subst xs.
             apply IHSn in Htail as [Hsteps Hsum].
             split.
             ++ constructor; [left; reflexivity | exact Hsteps].
             ++ change (1 + ListLib.sum tail = Z.of_nat (S (S n))).
                rewrite Hsum, !Nat2Z.inj_succ. lia.
          -- apply in_map_iff in Hin as [tail [Heq Htail]].
             symmetry in Heq. subst xs.
             apply IHn in Htail as [Hsteps Hsum].
             split.
             ++ constructor; [right; reflexivity | exact Hsteps].
             ++ change (2 + ListLib.sum tail = Z.of_nat (S (S n))).
                rewrite Hsum, !Nat2Z.inj_succ. lia.
        * intros [Hsteps Hsum].
          destruct xs as [|x tail].
          -- change (0 = Z.of_nat (S (S n))) in Hsum.
             rewrite !Nat2Z.inj_succ in Hsum.
             pose proof (Nat2Z.is_nonneg n).
             exfalso. lia.
          -- inversion Hsteps as [|? ? Hhead Htail]; subst.
             unfold IsClimbingStep in Hhead.
             destruct Hhead as [-> | ->].
             ++ left. apply in_map_iff. exists tail. split; [reflexivity |].
             apply IHSn. split; [exact Htail |].
             change (1 + ListLib.sum tail = Z.of_nat (S (S n))) in Hsum.
             rewrite !Nat2Z.inj_succ in Hsum |- *. lia.
             ++ right. apply in_map_iff. exists tail. split; [reflexivity |].
             apply IHn. split; [exact Htail |].
             change (2 + ListLib.sum tail = Z.of_nat (S (S n))) in Hsum.
             rewrite !Nat2Z.inj_succ in Hsum. lia.
  }
  intros n xs.
  exact ((proj1 (Hpair n)) xs).
Qed.

Lemma NoDup_climbing_way_enum_nat :
  forall n, NoDup (climbing_way_enum_nat n).
Proof.
  assert (Hpair :
    forall n,
      NoDup (climbing_way_enum_nat n) /\
      NoDup (climbing_way_enum_nat (S n))).
  {
    induction n as [|n [IHn IHSn]].
    - split; repeat constructor; simpl; intuition discriminate.
    - split.
      + exact IHSn.
      + rewrite climbing_way_enum_nat_S_S.
        apply NoDup_app.
        * apply FinFun.Injective_map_NoDup; [| exact IHSn].
          intros x y Heq. injection Heq. auto.
        * apply FinFun.Injective_map_NoDup; [| exact IHn].
          intros x y Heq. injection Heq. auto.
        * intros xs Hin1 Hin2.
          apply in_map_iff in Hin1 as [a [Ha _]].
          apply in_map_iff in Hin2 as [b [Hb _]].
          subst xs.
          discriminate.
  }
  intro n.
  exact (proj1 (Hpair n)).
Qed.

Definition climbing_way_enum (n : Z) : list (list Z) :=
  if Z.ltb n 0 then [] else climbing_way_enum_nat (Z.to_nat n).

Lemma valid_climbing_way_sum_nonnegative :
  forall xs n,
    ValidClimbingWay n xs -> 0 <= n.
Proof.
  intros xs n [Hsteps <-].
  induction Hsteps as [|x xs Hx Hsteps IH]; simpl.
  - lia.
  - unfold IsClimbingStep in Hx.
    destruct Hx as [-> | ->]; lia.
Qed.

Lemma valid_climbing_way_enum_ok :
  forall n xs,
    ValidClimbingWay n xs <-> In xs (climbing_way_enum n).
Proof.
  intros n xs.
  unfold climbing_way_enum.
  destruct (Z.ltb n 0) eqn:Hneg.
  - apply Z.ltb_lt in Hneg.
    split.
    + intro Hvalid.
      pose proof (valid_climbing_way_sum_nonnegative xs n Hvalid).
      lia.
    + intros [].
  - apply Z.ltb_ge in Hneg.
    rewrite in_climbing_way_enum_nat.
    unfold ValidClimbingWay.
    rewrite Z2Nat.id by lia.
    tauto.
Qed.

Lemma NoDup_climbing_way_enum :
  forall n, NoDup (climbing_way_enum n).
Proof.
  intro n.
  unfold climbing_way_enum.
  destruct (Z.ltb n 0).
  - constructor.
  - apply NoDup_climbing_way_enum_nat.
Qed.

#[export] Instance finite_valid_climbing_ways (n : Z) :
  Finite (ValidClimbingWay n).
Proof.
  refine {| enum := climbing_way_enum n |}.
  - apply valid_climbing_way_enum_ok.
  - apply NoDup_climbing_way_enum.
Defined.

(** This is the direct problem specification: the result is the cardinality
    of the finite set of 1/2-step lists whose repository list sum is [n]. *)
Definition ClimbingWays (n : Z) : Z :=
  @SumLib.Sum.sum
    (list Z)
    (ValidClimbingWay n)
    (finite_valid_climbing_ways n)
    (fun _ => 1).

Definition ClimbingStairsCount (n result : Z) : Prop :=
  result = ClimbingWays n.
