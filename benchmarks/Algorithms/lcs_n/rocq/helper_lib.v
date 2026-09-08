Require Import PVbench.Algorithms.lcs_n.rocq.spec_lib.

From Coq Require Import ZArith List.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.

Definition LCSNLogicalTableShape
    (mixed : list (option Z)) (table : list Z) (n : Z) : Prop :=
  Zlength mixed = (n + 1) * (n + 1) /\
  Zlength table = (n + 1) * (n + 1).
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
Definition LCSNInteriorCell
    (xs ys : list Z) (mixed : list (option Z)) (table : list Z)
    (n row col : Z) : Prop :=
  LCSNCellInitialized mixed table n row col /\
  LCSNCellRecurrence xs ys table n row col /\
  0 <= Znth (LCSNCellIndex n row col) table 0 <= Z.min row col.
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
Definition LCSNCompletedInteriorRows
    (xs ys : list Z) (mixed : list (option Z)) (table : list Z)
    (n rows_done : Z) : Prop :=
  forall row col,
    1 <= row < rows_done ->
    1 <= col <= n ->
    LCSNInteriorCell xs ys mixed table n row col.
Definition LCSNInteriorRowsUndefinedFrom
    (mixed : list (option Z)) (n rows_from : Z) : Prop :=
  forall row col,
    rows_from <= row <= n ->
    1 <= col <= n ->
    LCSNCellUndefined mixed n row col.

(** Stable state of the first, strided initialization loop.  The predicate
    classifies the entire square, not only the written column prefix. *)
Definition LCSNColumnProgress
    (mixed : list (option Z)) (table : list Z)
    (n rows_done : Z) : Prop :=
  LCSNLogicalTableShape mixed table n /\
  (forall row,
    0 <= row < rows_done ->
    LCSNBoundaryCell mixed table n row 0) /\
  (forall row,
    rows_done <= row <= n ->
    LCSNCellUndefined mixed n row 0) /\
  (forall row col,
    0 <= row <= n ->
    1 <= col <= n ->
    LCSNCellUndefined mixed n row col).

(** Stable state of the row-zero initialization loop; the first column is
    already complete, [cols_done] records the row-zero prefix, and every
    complementary cell is explicitly undefined. *)
Definition LCSNBoundaryProgress
    (mixed : list (option Z)) (table : list Z)
    (n cols_done : Z) : Prop :=
  LCSNLogicalTableShape mixed table n /\
  (forall row,
    0 <= row <= n ->
    LCSNBoundaryCell mixed table n row 0) /\
  (forall col,
    1 <= col < cols_done ->
    LCSNBoundaryCell mixed table n 0 col) /\
  (forall col,
    cols_done <= col <= n ->
    LCSNCellUndefined mixed n 0 col) /\
  (forall row col,
    1 <= row <= n ->
    1 <= col <= n ->
    LCSNCellUndefined mixed n row col).

(** Outer-loop state: completed rows have their final meanings, while the
    entire future interior is still undefined. *)
Definition LCSNRowsProgress
    (xs ys : list Z) (mixed : list (option Z)) (table : list Z)
    (n rows_done : Z) : Prop :=
  LCSNLogicalTableShape mixed table n /\
  LCSNBoundariesReady mixed table n /\
  LCSNCompletedInteriorRows xs ys mixed table n rows_done /\
  LCSNInteriorRowsUndefinedFrom mixed n rows_done.

(** Inner-loop state.  Unlike [LCSNRowsProgress], it treats the current row
    separately so that a written prefix can coexist with an undefined suffix. *)
Definition LCSNRowProgress
    (xs ys : list Z) (mixed : list (option Z)) (table : list Z)
    (n row next_col : Z) : Prop :=
  LCSNLogicalTableShape mixed table n /\
  LCSNBoundariesReady mixed table n /\
  LCSNCompletedInteriorRows xs ys mixed table n row /\
  (forall col,
    1 <= col < next_col ->
    LCSNInteriorCell xs ys mixed table n row col) /\
  (forall col,
    next_col <= col <= n ->
    LCSNCellUndefined mixed n row col) /\
  LCSNInteriorRowsUndefinedFrom mixed n (row + 1).
