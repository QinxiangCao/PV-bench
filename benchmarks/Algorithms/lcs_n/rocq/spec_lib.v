From Coq Require Import ZArith List.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.

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

(** Complete observable LCS table for equal prefix bounds [n]. *)
Definition LCSNTableResult
    (xs ys : list Z) (n : Z) (table : list Z) : Prop :=
  Zlength table = (n + 1) * (n + 1) /\
  forall row col,
    0 <= row <= n ->
    0 <= col <= n ->
    LCSNCellRecurrence xs ys table n row col.

(** A mixed array retains [None] for cells that the C program has not yet
    initialized.  [table] is the mathematical table being revealed. *)
