Require Export PVbench.Codeforces.examples_shard00.P025_1207B_square_filling.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

(* The remaining definitions describe stable mathematical states exposed by
   the two row-major scans in the C implementation.  They deliberately keep
   the functional specification above independent of that implementation. *)

Definition SquareAllOn (a : list (list Z)) (row col : Z) : Prop :=
  Znth col (Znth row a nil) 0 = 1 /\
  Znth col (Znth (row + 1) a nil) 0 = 1 /\
  Znth (col + 1) (Znth row a nil) 0 = 1 /\
  Znth (col + 1) (Znth (row + 1) a nil) 0 = 1.

Definition BeforeSquare (scan_row scan_col row col : Z) : Prop :=
  row < scan_row \/ (row = scan_row /\ col < scan_col).

Definition ScanOperations
    (n m : Z) (a : list (list Z))
    (scan_row scan_col : Z) (ops : list (Z * Z)) : Prop :=
  NoDup ops /\
  Forall (fun p => 0 <= fst p < n - 1 /\ 0 <= snd p < m - 1) ops /\
  forall row col,
    0 <= row < n - 1 -> 0 <= col < m - 1 ->
    (In (row, col) ops <->
       BeforeSquare scan_row scan_col row col /\ SquareAllOn a row col).

Definition made_cell (ops : list (Z * Z)) (k : nat) : Z :=
  if excluded_middle_informative
       (CellCovered ops (Z.of_nat k / 50) (Z.of_nat k mod 50))
  then 1 else 0.

Definition made_state (ops : list (Z * Z)) : list Z :=
  map (made_cell ops) (seq 0 2500).

Definition operation_words (ops : list (Z * Z)) : list (option Z) :=
  flat_map
    (fun p => cons (Some (fst p + 1)) (cons (Some (snd p + 1)) nil))
    ops.

Definition staged_ops (ops : list (Z * Z)) : list (option Z) :=
  operation_words ops ++
  repeat None (Z.to_nat (5000 - Zlength (operation_words ops))).

Definition BeforeCell (scan_row scan_col row col : Z) : Prop :=
  row < scan_row \/ (row = scan_row /\ col < scan_col).

Definition CheckedPrefix
    (n m : Z) (a : list (list Z)) (ops : list (Z * Z))
    (scan_row scan_col : Z) : Prop :=
  forall row col,
    0 <= row < n -> 0 <= col < m ->
    BeforeCell scan_row scan_col row col ->
    (Znth col (Znth row a nil) 0 = 1 <-> CellCovered ops row col).

Require Import Coq.micromega.Lia.

Require Import Coq.micromega.Psatz.

Require Import Coq.Logic.ClassicalEpsilon.
