Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import ListLib.General.Presuffix.
Require Import PVbench.Codeforces.examples_shard01.P081_432E_square_tiling.rocq.spec_lib.

Import ListNotations.
Local Open Scope Z_scope.

Definition NeighborConflict
    (flat : list Z) (n m i j c left_override : Z) : Prop :=
  (0 < i /\ Znth ((i - 1) * m + j) flat 0 = c) \/
  (i + 1 < n /\ Znth ((i + 1) * m + j) flat 0 = c) \/
  (j + 1 < m /\ Znth (i * m + j + 1) flat 0 = c) \/
  (0 < j /\
    (if Z.eq_dec left_override 0
     then Znth (i * m + j - 1) flat 0
     else left_override) = c) \/
  (j = 0 /\ left_override = c).

Definition LegalColor
    (flat : list Z) (n m i j left_override c : Z) : Prop :=
  65 <= c <= 90 /\
  ~ NeighborConflict flat n m i j c left_override.

Definition LeastLegalColor
    (flat : list Z) (n m i j left_override c : Z) : Prop :=
  LegalColor flat n m i j left_override c /\
  forall d, 65 <= d < c ->
    ~ LegalColor flat n m i j left_override d.

Definition CanPlace
    (flat : list Z) (n m i j side color : Z) : Prop :=
  1 <= side /\ i + side <= n /\ j + side <= m /\
  (forall r q,
      i <= r < i + side -> j <= q < j + side ->
      Znth (r * m + q) flat 0 = 0) /\
  (forall q,
      j <= q < j + side ->
      (0 < i -> Znth ((i - 1) * m + q) flat 0 <> color) /\
      (i + side < n -> Znth ((i + side) * m + q) flat 0 <> color)) /\
  (forall r,
      i <= r < i + side ->
      (0 < j -> Znth (r * m + j - 1) flat 0 <> color) /\
      (j + side < m -> Znth (r * m + j + side) flat 0 <> color)).

Definition ZeroPrefix (flat : list Z) (upto : Z) : Prop :=
  forall k, 0 <= k < upto -> Znth k flat 0 = 0.

Definition NoConflictBelow
    (flat : list Z) (n m i j left_override next : Z) : Prop :=
  forall color, 65 <= color < next ->
    NeighborConflict flat n m i j color left_override.

Definition EmptySquarePrefix
    (flat : list Z) (m i j side done : Z) : Prop :=
  forall off, 0 <= off < done ->
    Znth ((i + off / side) * m + (j + off mod side)) flat 0 = 0.

Definition HorizontalBoundaryClearPrefix
    (flat : list Z) (n m i j side color done : Z) : Prop :=
  forall off, 0 <= off < done ->
    (0 < i -> Znth ((i - 1) * m + (j + off)) flat 0 <> color) /\
    (i + side < n -> Znth ((i + side) * m + (j + off)) flat 0 <> color).

Definition VerticalBoundaryClearPrefix
    (flat : list Z) (n m i j side color done : Z) : Prop :=
  forall off, 0 <= off < done ->
    (0 < j -> Znth ((i + off) * m + j - 1) flat 0 <> color) /\
    (j + side < m -> Znth ((i + off) * m + j + side) flat 0 <> color).

Definition RowsOfFlat (n m : Z) (flat : list Z) (grid : list (list Z)) : Prop :=
  Zlength grid = n /\
  Forall (fun row => Zlength row = m) grid /\
  Flatten grid = flat.

Definition LexPrefixLe (upto : Z) (left right : list Z) : Prop :=
  (forall k, 0 <= k < upto -> Znth k left 0 = Znth k right 0) \/
  exists first,
    0 <= first < upto /\
    (forall k, 0 <= k < first -> Znth k left 0 = Znth k right 0) /\
    Znth first left 0 < Znth first right 0.

Definition PartialSquareComponents
    (n m : Z) (grid : list (list Z)) : Prop :=
  forall p,
    0 <= fst p < n -> 0 <= snd p < m ->
    Znth (snd p) (Znth (fst p) grid []) 0 <> 0 ->
    exists r c side,
      1 <= side /\
      0 <= r /\ 0 <= c /\ r + side <= n /\ c + side <= m /\
      r <= fst p < r + side /\ c <= snd p < c + side /\
      forall q,
        0 <= fst q < n -> 0 <= snd q < m ->
        (SameColorPath grid p q <->
         r <= fst q < r + side /\ c <= snd q < c + side).

Definition PartialTilingState
    (n m next : Z) (flat : list Z) : Prop :=
  exists grid,
    RowsOfFlat n m flat grid /\
    (forall k, 0 <= k < next -> 65 <= Znth k flat 0 <= 90) /\
    (forall k, 0 <= k < n * m ->
       Znth k flat 0 = 0 \/ 65 <= Znth k flat 0 <= 90) /\
    PartialSquareComponents n m grid /\
    (forall candidate,
       SquareTiling n m candidate ->
       LexPrefixLe next flat (Flatten candidate)).

Definition NoPlaceableColorBelow
    (flat : list Z) (n m i j next : Z) : Prop :=
  forall color, 65 <= color < next ->
    ~ CanPlace flat n m i j 1 color.

Definition GreedySideState
    (flat : list Z) (n m i j color side : Z) : Prop :=
  CanPlace flat n m i j side color /\
  forall previous_side,
    1 <= previous_side < side ->
    CanPlace flat n m i j (previous_side + 1) color /\
    exists fallback,
      LeastLegalColor flat n m i (j + previous_side) color fallback /\
      color < fallback.

Definition PaintRectanglePrefix
    (before after : list Z) (m i j side color done : Z) : Prop :=
  Zlength after = Zlength before /\
  forall index,
    0 <= index < Zlength before ->
    ((exists off,
        0 <= off < done /\
        index = (i + off / side) * m + (j + off mod side)) /\
      Znth index after 0 = color) \/
    ((forall off,
        0 <= off < done ->
        index <> (i + off / side) * m + (j + off mod side)) /\
      Znth index after 0 = Znth index before 0).

Definition CanonicalGrid (flat : list Z) : Prop :=
  forall k, 0 <= k < Zlength flat ->
    Znth k flat 0 = 0 \/ 65 <= Znth k flat 0 <= 90.

Definition CommittedFrontierState
    (n m next : Z) (flat : list Z) : Prop :=
  forall upto,
    next <= upto <= n * m ->
    (forall k, next <= k < upto -> 65 <= Znth k flat 0 <= 90) ->
    PartialTilingState n m upto flat.

Definition ChosenSquareState
    (flat : list Z) (n m i j color side : Z) : Prop :=
  LeastLegalColor flat n m i j 0 color /\
  GreedySideState flat n m i j color side.

Definition SettledSquareState
    (flat : list Z) (n m i j color side : Z) : Prop :=
  ChosenSquareState flat n m i j color side /\
  (j + side = m \/
   ~ CanPlace flat n m i j (side + 1) color \/
   exists fallback,
     LeastLegalColor flat n m i (j + side) color fallback /\
     fallback <= color).

Inductive GreedyPlacementTrace (n m : Z) : Z -> list Z -> Prop :=
| GreedyTrace_zero : forall flat,
    Zlength flat = n * m ->
    ZeroPrefix flat (n * m) ->
    GreedyPlacementTrace n m 0 flat
| GreedyTrace_skip : forall next flat,
    GreedyPlacementTrace n m next flat ->
    0 <= next < n * m ->
    65 <= Znth next flat 0 <= 90 ->
    GreedyPlacementTrace n m (next + 1) flat
| GreedyTrace_place : forall next before after i j color side,
    GreedyPlacementTrace n m next before ->
    next = i * m + j ->
    0 <= i < n ->
    0 <= j < m ->
    Znth next before 0 = 0 ->
    SettledSquareState before n m i j color side ->
    PaintRectanglePrefix before after m i j side color (side * side) ->
    GreedyPlacementTrace n m (next + 1) after.
