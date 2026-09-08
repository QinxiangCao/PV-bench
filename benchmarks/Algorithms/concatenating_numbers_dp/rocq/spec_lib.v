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
Definition item_at
    (rows : list (list Z)) (lengths : list Z) (i : Z) : number_item :=
  (Znth i rows nil, Znth i lengths 0).
Definition concatenate_indices
    (rows : list (list Z)) (lengths indices : list Z) : list Z :=
  concat (map (fun i => item_digits (item_at rows lengths i)) indices).
Definition all_indices (count : Z) : list Z :=
  map Z.of_nat (seq 0 (Z.to_nat count)).
Definition digit_lex_ge (xs ys : list Z) : Prop :=
  Zlength xs = Zlength ys /\
  (xs = ys \/
   exists k,
     0 <= k < Zlength xs /\
     (forall j, 0 <= j < k -> Znth j xs 0 = Znth j ys 0) /\
     Znth k ys 0 < Znth k xs 0).
Definition item_before_or_equal
    (rows : list (list Z)) (lengths : list Z) (i j : Z) : Prop :=
  digit_lex_ge
    (item_digits (item_at rows lengths i) ++
     item_digits (item_at rows lengths j))
    (item_digits (item_at rows lengths j) ++
     item_digits (item_at rows lengths i)).
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
Definition BestIndexForMask
    (rows : list (list Z)) (lens : list Z)
    (count mask index : Z) : Prop :=
  0 <= index < count /\
  Z.testbit mask index = true /\
  forall other,
    0 <= other < count ->
    Z.testbit mask other = true ->
    item_before_or_equal rows lens index other.

(* A semantic table invariant: every materialized nonzero mask stores a
   mathematically greatest first row for that selected subset. *)
Definition DPTablePrefix
    (rows : list (list Z)) (lens : list Z) (count computed : Z)
    (choices : list Z) : Prop :=
  1 <= computed <= Z.shiftl 1 count /\
  Zlength choices = computed /\
  Znth 0 choices 0 = -1 /\
  forall mask,
    1 <= mask < computed ->
    BestIndexForMask rows lens count mask (Znth mask choices 0).
Definition LargestConcatenation
    (rows : list (list Z)) (lens output : list Z) : Prop :=
  exists order,
    Permutation (all_indices (Zlength rows)) order /\
    output = concatenate_indices rows lens order /\
    forall alternative,
      Permutation (all_indices (Zlength rows)) alternative ->
      digit_lex_ge output (concatenate_indices rows lens alternative).
