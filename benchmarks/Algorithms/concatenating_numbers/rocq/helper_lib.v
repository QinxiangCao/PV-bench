Require Import PVbench.Algorithms.concatenating_numbers.rocq.spec_lib.

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
Require Import AUXLib.ListLib.

Import ListNotations.
Local Open Scope Z_scope.

Definition digit_lex_gt (xs ys : list Z) : Prop :=
  Zlength xs = Zlength ys /\
  exists k,
    0 <= k < Zlength xs /\
    (forall j, 0 <= j < k -> Znth j xs 0 = Znth j ys 0) /\
    Znth k ys 0 < Znth k xs 0.
Definition item_at (rows : list (list Z)) (lengths : list Z) (i : Z) :
  number_item :=
  (Znth i rows nil, Znth i lengths 0).
Definition item_before
    (rows : list (list Z)) (lengths : list Z) (i j : Z) : Prop :=
  digit_lex_gt
    (item_digits (item_at rows lengths i) ++
     item_digits (item_at rows lengths j))
    (item_digits (item_at rows lengths j) ++
     item_digits (item_at rows lengths i)).
Definition item_before_or_equal
    (rows : list (list Z)) (lengths : list Z) (i j : Z) : Prop :=
  digit_lex_ge
    (item_digits (item_at rows lengths i) ++
     item_digits (item_at rows lengths j))
    (item_digits (item_at rows lengths j) ++
     item_digits (item_at rows lengths i)).
Definition ConcatLeftDigit
    (rows : list (list Z)) (lens : list Z) (i j position : Z) : Z :=
  Znth position
    (item_digits (item_at rows lens i) ++
     item_digits (item_at rows lens j)) 0.
Definition ConcatRightDigit
    (rows : list (list Z)) (lens : list Z) (i j position : Z) : Z :=
  Znth position
    (item_digits (item_at rows lens j) ++
     item_digits (item_at rows lens i)) 0.
Definition SameOutsidePairedRange
    (rows0 rows1 : list (list Z)) (lens0 lens1 : list Z)
    (left right : Z) : Prop :=
  Zlength rows0 = Zlength rows1 /\
  Zlength lens0 = Zlength lens1 /\
  forall k,
    0 <= k < Zlength rows0 ->
    (k < left \/ right < k) ->
    item_at rows1 lens1 k = item_at rows0 lens0 k.
Definition ConcatComparePrefix
    (rows : list (list Z)) (lens : list Z)
    (i j position : Z) : Prop :=
  let lhs := item_digits (item_at rows lens i) ++
             item_digits (item_at rows lens j) in
  let rhs := item_digits (item_at rows lens j) ++
             item_digits (item_at rows lens i) in
  0 <= position <= Zlength lhs /\
  Zlength lhs = Zlength rhs /\
  forall k, 0 <= k < position -> Znth k lhs 0 = Znth k rhs 0.
Definition ConcatCompareOutcome
    (rows : list (list Z)) (lens : list Z)
    (i j comparison : Z) : Prop :=
  let lhs := item_digits (item_at rows lens i) ++
             item_digits (item_at rows lens j) in
  let rhs := item_digits (item_at rows lens j) ++
             item_digits (item_at rows lens i) in
  (comparison = 0 /\ lhs = rhs) \/
  (exists k,
     0 <= k < Zlength lhs /\
     Zlength lhs = Zlength rhs /\
     (forall p, 0 <= p < k -> Znth p lhs 0 = Znth p rhs 0) /\
     Znth k lhs 0 <> Znth k rhs 0 /\
     comparison = Znth k lhs 0 - Znth k rhs 0).
Definition SwapRowsPrefix
    (before after : list (list Z)) (first second progress width : Z) : Prop :=
  let first_row := Znth first before nil in
  let second_row := Znth second before nil in
  let first_now := sublist 0 progress second_row ++
                   sublist progress width first_row in
  let second_now := sublist 0 progress first_row ++
                    sublist progress width second_row in
  after = replace_Znth second second_now
            (replace_Znth first first_now before).
Definition PartitionScanState
    (rows0 rows1 : list (list Z)) (lens0 lens1 : list Z)
    (low high boundary scan : Z) : Prop :=
  PairedPermutation rows0 rows1 lens0 lens1 /\
  SameOutsidePairedRange rows0 rows1 lens0 lens1 low high /\
  item_at rows1 lens1 high = item_at rows0 lens0 high /\
  (forall k, low <= k <= boundary -> item_before rows1 lens1 k high) /\
  (forall k, boundary < k < scan -> ~ item_before rows1 lens1 k high).
Definition GreedyPartitionedAt
    (rows : list (list Z)) (lens : list Z)
    (low high pivot : Z) : Prop :=
  low <= pivot <= high /\
  (forall k, low <= k < pivot -> item_before rows lens k pivot) /\
  (forall k, pivot < k <= high -> ~ item_before rows lens k pivot).
Definition GreedySortedRange
    (rows : list (list Z)) (lens : list Z) (left right : Z) : Prop :=
  forall i j,
    left <= i /\ i <= j /\ j <= right ->
    item_before_or_equal rows lens i j.
Definition GreedySorted
    (rows : list (list Z)) (lens : list Z) : Prop :=
  forall i j,
    0 <= i /\ i <= j /\ j < Zlength rows ->
    item_before_or_equal rows lens i j.
Definition ConcatenatedPrefix
    (rows : list (list Z)) (lens : list Z) (row_count : Z) : list Z :=
  concatenate_rows (sublist 0 row_count rows) (sublist 0 row_count lens).
Definition ConcatenatedOutputPrefix
    (rows : list (list Z)) (lens : list Z)
    (row_count digit_count : Z) : list Z :=
  ConcatenatedPrefix rows lens row_count ++
  sublist 0 digit_count (Znth row_count rows nil).
