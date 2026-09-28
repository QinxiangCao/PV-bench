From Coq Require Import ZArith List Lia.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
From SimpleC.SL Require Import Mem SeparationLogic ArrayLib Array2Lib.
Require Import Logic.LogicGenerator.demo932.Interface.
Import naive_C_Rules.
Local Open Scope sac.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
Require Import AUXLib.ListLib.
Require Import MaxMinLib.MaxMin.
Require Import Coq.ZArith.Zpow_facts.
(* Let higher-order C annotations pass Zlength directly to map. *)
Arguments Zlength {A}.

(** Decode the significant numeric digits of each fixed-width input row. *)
Definition DecimalRowValues (rows : list (list Z)) (lengths : list Z) : list Z :=
  map (fun row_length =>
    fold_left (fun value digit => 10 * value + digit)
      (sublist 0 (snd row_length) (fst row_length)) 0)
    (combine rows lengths).

Definition number_item : Type := (list Z * Z)%type.

Definition item_digits (x : number_item) : list Z :=
  sublist 0 (snd x) (fst x).

Definition paired_items (rows : list (list Z)) (lengths : list Z) :
  list number_item :=
  combine rows lengths.

Definition concatenate_items (items : list number_item) : list Z :=
  concat (map item_digits items).

Definition concatenate_rows (rows : list (list Z)) (lengths : list Z) :
  list Z :=
  concatenate_items (paired_items rows lengths).

Definition digit_lex_ge (xs ys : list Z) : Prop :=
  Zlength xs = Zlength ys /\
  (xs = ys \/
   exists k,
     0 <= k < Zlength xs /\
     (forall j, 0 <= j < k -> Znth j xs 0 = Znth j ys 0) /\
     Znth k ys 0 < Znth k xs 0).

(* The result is the greatest concatenation among all permutations of the
   input items.  Layout, capacities, digit bounds and sorting state are not
   part of this mathematical output relation. *)
Definition LargestConcatenation
    (rows : list (list Z)) (lens output : list Z) : Prop :=
  max_value_of_subset
    (fun xs ys => digit_lex_ge ys xs)
    (Permutation (paired_items rows lens))
    concatenate_items output.
