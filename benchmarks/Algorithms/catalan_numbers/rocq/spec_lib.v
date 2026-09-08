Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Fixpoint stack_run (depth : nat) (ops : list bool) : option nat :=
  match ops with
  | nil => Some depth
  | true :: rest => stack_run (S depth) rest
  | false :: rest =>
      match depth with
      | O => None
      | S depth' => stack_run depth' rest
      end
  end.
Fixpoint stack_push_count (ops : list bool) : nat :=
  match ops with
  | nil => O
  | true :: rest => S (stack_push_count rest)
  | false :: rest => stack_push_count rest
  end.

(** All push/pop words of an exact length.  This is a canonical finite
    carrier used only to take the cardinality of the mathematical set. *)
Fixpoint all_stack_words (len : nat) : list (list bool) :=
  match len with
  | O => cons nil nil
  | S len' =>
      map (cons true) (all_stack_words len') ++
      map (cons false) (all_stack_words len')
  end.
Definition legal_stack_completion_nat
    (pushes depth : nat) (ops : list bool) : Prop :=
  length ops = (2 * pushes + depth)%nat /\
  stack_push_count ops = pushes /\
  stack_run depth ops = Some O.
Definition legal_stack_completionb
    (pushes depth : nat) (ops : list bool) : bool :=
  Nat.eqb (length ops) (2 * pushes + depth) &&
  Nat.eqb (stack_push_count ops) pushes &&
  match stack_run depth ops with
  | Some O => true
  | _ => false
  end.
Definition stack_completion_set (pushes depth : nat) : list (list bool) :=
  filter (legal_stack_completionb pushes depth)
    (all_stack_words (2 * pushes + depth)).
Definition LegalStackCompletion
    (pushes depth : Z) (ops : list bool) : Prop :=
  0 <= pushes /\
  0 <= depth /\
  legal_stack_completion_nat (Z.to_nat pushes) (Z.to_nat depth) ops.
Definition LegalStackBehavior (pushes : Z) (ops : list bool) : Prop :=
  LegalStackCompletion pushes 0 ops.
Definition StackSequenceSet (pushes : Z) : list (list bool) :=
  stack_completion_set (Z.to_nat pushes) O.
Definition StackCompletionCount
    (pushes depth value : Z) : Prop :=
  0 <= pushes /\
  0 <= depth /\
  value = Z.of_nat
    (length (stack_completion_set (Z.to_nat pushes) (Z.to_nat depth))).

(** The requested result is the cardinality of the finite set of legal
    push/pop traces which starts and ends with an empty stack. *)
Definition StackSequenceCount (pushes value : Z) : Prop :=
  0 <= pushes /\
  value = Z.of_nat (length (StackSequenceSet pushes)) /\
  forall ops,
    In ops (StackSequenceSet pushes) <->
    LegalStackBehavior pushes ops.
Definition StackCellIndex (n row col : Z) : Z :=
  row * (n + 1) + col.

(** The exponential bound counts all push/pop words of the required
    length; legal completions form a subset. *)
Definition StackCellBound (row col value : Z) : Prop :=
  0 <= row /\
  0 <= col /\
  0 <= value <= 2 ^ (2 * row + col).

(** Only the lower-left triangle can influence the requested cell.  The
    remaining cells are still tracked by [StackCellBound] for C safety. *)
Definition StackCellCorrect
    (n row col value : Z) : Prop :=
  row + col <= n -> StackCompletionCount row col value.
Definition StackTablePrefix
    (n : Z) (table : list Z) (written : Z) : Prop :=
  0 <= n /\
  (0 <= written /\ Zlength table = written) /\
  forall row col,
    0 <= row <= n ->
    0 <= col <= n ->
    0 <= StackCellIndex n row col < written ->
    StackCellBound row col
      (Znth (StackCellIndex n row col) table 0) /\
    StackCellCorrect n row col
      (Znth (StackCellIndex n row col) table 0).
Definition StackRowsDone
    (n : Z) (table : list Z) (rows_done : Z) : Prop :=
  0 <= rows_done /\
  StackTablePrefix n table (rows_done * (n + 1)).
