Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.
From SumLib Require Import Sum FiniteExtra ZRange.
Require Import Coq.Lists.ListDec.

(** Actual stack semantics: remaining input, stack top first, and output in
    production order.  A failed push/pop makes the execution invalid. *)
Definition StackValueStep
    (state : option (list Z * list Z * list Z)) (push : bool) :=
  match state with
  | None => None
  | Some (input, stack, output) =>
      if push then
        match input with
        | [] => None
        | x :: rest => Some (rest, x :: stack, output)
        end
      else
        match stack with
        | [] => None
        | x :: rest => Some (input, rest, output ++ [x])
        end
  end.

Definition StackValueExecution (n : Z) (ops : list bool) :=
  fold_left StackValueStep ops (Some (Zrange 1 (n + 1), [], [])).

Definition StackOutput (n : Z) (output : list Z) : Prop :=
  exists ops, Zlength ops = 2 * n /\
    StackValueExecution n ops = Some ([], [], output).

Definition StackCompleteWord (n : Z) (ops : list bool) : bool :=
  Z.eqb (Zlength ops) (2 * n) &&
  match StackValueExecution n ops with
  | Some ([], [], _) => true
  | _ => false
  end.

Definition StackWordOutput (n : Z) (ops : list bool) : list Z :=
  match StackValueExecution n ops with
  | Some (_, _, output) => output
  | None => []
  end.

(** This enumeration serves only to construct the Finite instance.  The
    public set is defined above by actual input/stack/output semantics. *)
Definition StackOutputEnumeration (n : Z) : list (list Z) :=
  map (StackWordOutput n)
    (filter (StackCompleteWord n) (all_lists (Z.to_nat (2 * n)) [true; false])).

Lemma StackCompleteWord_spec n ops :
  StackCompleteWord n ops = true <->
  Zlength ops = 2 * n /\ exists output,
    StackValueExecution n ops = Some ([], [], output).
Proof.
  unfold StackCompleteWord. rewrite andb_true_iff, Z.eqb_eq.
  destruct (StackValueExecution n ops) as [[[input stack] output] |] eqn:He.
  - destruct input, stack; cbn.
    all: try solve [split; intros [Hlen Hbad];
      [discriminate | destruct Hbad as [result Hbad]; discriminate]].
    split; intros [Hlen H]; split; try assumption.
    + exists output. reflexivity.
    + reflexivity.
  - cbn. split; intros [Hlen Hbad];
      [discriminate | destruct Hbad as [result Hbad]; discriminate].
Qed.

Lemma StackOutputEnumeration_spec n output :
  StackOutput n output <-> In output (StackOutputEnumeration n).
Proof.
  unfold StackOutput, StackOutputEnumeration. rewrite in_map_iff.
  split.
  - intros [ops [Hlen Hrun]]. exists ops. split.
    + unfold StackWordOutput. rewrite Hrun. reflexivity.
    + apply filter_In. split.
      * apply in_all_lists. split.
        -- rewrite Zlength_correct in Hlen. lia.
        -- apply Forall_forall. intros x _. destruct x; simpl; auto.
      * apply StackCompleteWord_spec. split; [exact Hlen | eauto].
  - intros [ops [Hout Hin]]. apply filter_In in Hin as [_ Hcomplete].
    apply StackCompleteWord_spec in Hcomplete as [Hlen [result Hrun]].
    exists ops. split; [exact Hlen |].
    unfold StackWordOutput in Hout. rewrite Hrun in Hout. subst result. exact Hrun.
Qed.

#[export] Instance finite_stack_outputs n : Finite (StackOutput n).
Proof.
  refine {| enum := nodup (list_eq_dec Z.eq_dec) (StackOutputEnumeration n) |}.
  - intros output. rewrite nodup_In. apply StackOutputEnumeration_spec.
  - apply NoDup_nodup.
Defined.

Definition StackSequenceCount (n value : Z) : Prop :=
  value = SumLib.Sum.sum (StackOutput n) (fun _ => 1).
