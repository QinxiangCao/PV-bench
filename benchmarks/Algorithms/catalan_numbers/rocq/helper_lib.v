Require Export PVbench.Algorithms.catalan_numbers.rocq.spec_lib.
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

(** [true] is a push and [false] is a pop.  [stack_run depth ops]
    rejects exactly those traces which try to pop an empty stack. *)
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

(** Cardinalities describe only the requested mathematical counts.  The
    existing finite-word enumeration above is retained as a computation helper. *)
Definition StackCompletionCount (pushes depth value : Z) : Prop :=
  value = Zlength
    (stack_completion_set (Z.to_nat pushes) (Z.to_nat depth)).

Definition StackCellIndex (n row col : Z) : Z :=
  row * (n + 1) + col.

Definition StackCellCorrect (n row col value : Z) : Prop :=
  row + col <= n -> StackCompletionCount row col value.

(** Only mathematical correctness belongs here.  Length, loop bounds and
    overflow bounds are separate premises in annotations and lemmas. *)
Definition StackTablePrefix (n : Z) (table : list Z) (written : Z) : Prop :=
  forall row col,
    0 <= row <= n -> 0 <= col <= n ->
    StackCellIndex n row col < written ->
    StackCellCorrect n row col (Znth (StackCellIndex n row col) table 0).

(* QCP identifiers cannot contain a dot; this notation exposes Z.pow. *)
Notation Zpower := Z.pow.
