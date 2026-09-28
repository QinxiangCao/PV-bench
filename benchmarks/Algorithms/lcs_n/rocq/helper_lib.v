Require Export PVbench.Algorithms.lcs_n.rocq.spec_lib.
From Coq Require Import ZArith List.
From AUXLib Require Import ListLib MonotonicList.
Import ListNotations.
Local Open Scope Z_scope.
From Coq Require Import Lia Ring.
From Coq Require Import Lia.
From Coq Require Import micromega.Psatz.
From MaxMinLib Require Import MaxMin Interface.
From Coq Require Import Sorting.Sorted.

(** Row-major address using the caller-selected runtime dimension. *)
Definition LCSNCellIndex (n row col : Z) : Z :=
  row * (n + 1) + col.

(** The mathematical prefix-table equation for one public cell. *)
Definition LCSNCellRecurrence
    (xs ys table : list Z) (n row col : Z) : Prop :=
  ((row = 0 \/ col = 0) /\
     Znth (LCSNCellIndex n row col) table 0 = 0) \/
  (0 < row /\ 0 < col /\
    ((Znth (row - 1) xs 0 = Znth (col - 1) ys 0 /\
       Znth (LCSNCellIndex n row col) table 0 =
         Znth (LCSNCellIndex n (row - 1) (col - 1)) table 0 + 1) \/
     (Znth (row - 1) xs 0 <> Znth (col - 1) ys 0 /\
       Znth (LCSNCellIndex n row col) table 0 =
         Z.max
           (Znth (LCSNCellIndex n (row - 1) col) table 0)
           (Znth (LCSNCellIndex n row (col - 1)) table 0)))).

Definition LCSNCellInitialized
    (mixed : list (option Z)) (table : list Z)
    (n row col : Z) : Prop :=
  Znth (LCSNCellIndex n row col) mixed None =
    Some (Znth (LCSNCellIndex n row col) table 0).

Definition LCSNBoundaryCell
    (mixed : list (option Z)) (table : list Z)
    (n row col : Z) : Prop :=
  LCSNCellInitialized mixed table n row col /\
  Znth (LCSNCellIndex n row col) table 0 = 0.

Definition LCSNCellUndefined
    (mixed : list (option Z)) (n row col : Z) : Prop :=
  Znth (LCSNCellIndex n row col) mixed None = None.

Definition LCSNBoundariesReady
    (mixed : list (option Z)) (table : list Z) (n : Z) : Prop :=
  (forall row,
    0 <= row <= n ->
    LCSNBoundaryCell mixed table n row 0) /\
  (forall col,
    0 <= col <= n ->
    LCSNBoundaryCell mixed table n 0 col).

Definition LCSNInteriorRowsUndefinedFrom
    (mixed : list (option Z)) (n rows_from : Z) : Prop :=
  forall row, rows_from <= row <= n ->
    Forall (eq (@None Z))
      (sublist (LCSNCellIndex n row 1) (LCSNCellIndex n row (n + 1)) mixed).

(** Public progress separates mathematical table meaning from shape. *)
Definition LCSNTableResult (xs ys : list Z) (n : Z) (table : list Z) : Prop :=
  forall row col, 0 <= row <= n -> 0 <= col <= n ->
    LCSNCellRecurrence xs ys table n row col.

Definition LCSNInteriorCell (xs ys : list Z) (mixed : list (option Z))
    (table : list Z) (n row col : Z) : Prop :=
  LCSNCellInitialized mixed table n row col /\
  LCSNCellRecurrence xs ys table n row col.

Definition LCSNCompletedInteriorRows (xs ys : list Z) (mixed : list (option Z))
    (table : list Z) (n rows_done : Z) : Prop :=
  forall row col, 1 <= row < rows_done -> 1 <= col <= n ->
    LCSNInteriorCell xs ys mixed table n row col.

Definition LCSNColumnProgress (mixed : list (option Z)) (table : list Z)
    (n rows_done : Z) : Prop :=
  (forall row, 0 <= row < rows_done -> LCSNBoundaryCell mixed table n row 0) /\
  (forall row, rows_done <= row <= n -> LCSNCellUndefined mixed n row 0) /\
  LCSNInteriorRowsUndefinedFrom mixed n 0.

Definition LCSNBoundaryProgress (mixed : list (option Z)) (table : list Z)
    (n cols_done : Z) : Prop :=
  (forall row, 0 <= row <= n -> LCSNBoundaryCell mixed table n row 0) /\
  (forall col, 1 <= col < cols_done -> LCSNBoundaryCell mixed table n 0 col) /\
  Forall (eq (@None Z)) (sublist cols_done (n + 1) mixed) /\
  LCSNInteriorRowsUndefinedFrom mixed n 1.

Definition LCSNRowsProgress (xs ys : list Z) (mixed : list (option Z))
    (table : list Z) (n rows_done : Z) : Prop :=
  LCSNBoundariesReady mixed table n /\
  LCSNCompletedInteriorRows xs ys mixed table n rows_done /\
  LCSNInteriorRowsUndefinedFrom mixed n rows_done.

Definition LCSNRowProgress (xs ys : list Z) (mixed : list (option Z))
    (table : list Z) (n row next_col : Z) : Prop :=
  LCSNBoundariesReady mixed table n /\
  LCSNCompletedInteriorRows xs ys mixed table n row /\
  (forall col, 1 <= col < next_col -> LCSNInteriorCell xs ys mixed table n row col) /\
  Forall (eq (@None Z))
    (sublist (LCSNCellIndex n row next_col) (LCSNCellIndex n row (n + 1)) mixed) /\
  LCSNInteriorRowsUndefinedFrom mixed n (row + 1).
