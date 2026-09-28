Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
Require Import MaxMinLib.MaxMin.
Require Import SumLib.ZRange.
Require Import AUXLib.ListLib.
Require Import AUXLib.MonotonicList.
Local Notation sum := AUXLib.ListLib.sum.
Import ListNotations.
Local Open Scope Z_scope.
Require Import Coq.ZArith.Zpow_facts.
Require Import Coq.ZArith.Zbitwise.
Require Import Coq.Logic.ClassicalDescription.
(* The annotation parser emits Zlength as a higher-order argument to map. *)
Arguments Zlength {A}.

(* Permit the polymorphic length function in higher-order C predicates. *)
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

Definition item_at
    (rows : list (list Z)) (lengths : list Z) (i : Z) : number_item :=
  (Znth i rows nil, Znth i lengths 0).

Definition concatenate_indices
    (rows : list (list Z)) (lengths indices : list Z) : list Z :=
  concat (map (fun i => item_digits (item_at rows lengths i)) indices).

Definition all_indices (count : Z) : list Z :=
  Zrange 0 count.

Definition digit_lex_ge (xs ys : list Z) : Prop :=
  Zlength xs = Zlength ys /\
  (xs = ys \/
   exists k,
     0 <= k < Zlength xs /\
     (forall j, 0 <= j < k -> Znth j xs 0 = Znth j ys 0) /\
     Znth k ys 0 < Znth k xs 0).

(* The output loop has consumed [done] and still owns exactly the rows whose
   bits occur in [mask].  The concatenation of [done ++ todo] is a global
   optimum, so this describes a mathematical optimal-prefix state rather
   than an execution trace of the C loop. *)
Definition LargestConcatenation
    (rows : list (list Z)) (lens output : list Z) : Prop :=
  max_value_of_subset
    (fun xs ys => digit_lex_ge ys xs)
    (Permutation (all_indices (Zlength rows)))
    (concatenate_indices rows lens) output.
