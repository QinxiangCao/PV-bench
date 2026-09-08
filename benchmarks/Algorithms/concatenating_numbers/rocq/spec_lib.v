Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
Require Import AUXLib.ListLib.

Import ListNotations.
Local Open Scope Z_scope.

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
Definition RowsWellFormed
    (rows : list (list Z)) (lengths : list Z)
    (count width : Z) : Prop :=
  Zlength rows = count /\
  Zlength lengths = count /\
  (forall i,
     0 <= i < count ->
     Zlength (Znth i rows nil) = width /\
     1 <= Znth i lengths 0 <= width /\
     1 <= Znth 0 (Znth i rows nil) 0 <= 9 /\
     (forall j,
        0 <= j < Znth i lengths 0 ->
        0 <= Znth j (Znth i rows nil) 0 <= 9)).
Definition FlatRows
    (flat : list Z) (rows : list (list Z)) (count width : Z) : Prop :=
  Zlength flat = count * width /\
  Zlength rows = count /\
  forall i,
    0 <= i < count ->
    Znth i rows nil = sublist (i * width) ((i + 1) * width) flat.
Definition PairedPermutation
    (rows lengths_rows : list (list Z))
    (lens lengths_lens : list Z) : Prop :=
  Zlength rows = Zlength lens /\
  Zlength lengths_rows = Zlength lengths_lens /\
  Permutation (paired_items rows lens)
              (paired_items lengths_rows lengths_lens).
Definition LargestConcatenation
    (original_rows arranged_rows : list (list Z))
    (original_lens arranged_lens output : list Z) : Prop :=
  PairedPermutation original_rows arranged_rows
                    original_lens arranged_lens /\
  output = concatenate_rows arranged_rows arranged_lens /\
  forall alternative_rows alternative_lens,
    PairedPermutation original_rows alternative_rows
                      original_lens alternative_lens ->
    digit_lex_ge output
      (concatenate_rows alternative_rows alternative_lens).

Require Import Coq.ZArith.Zpow_facts.
