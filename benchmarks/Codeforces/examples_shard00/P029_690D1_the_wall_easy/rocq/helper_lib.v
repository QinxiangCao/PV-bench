Require Import PVbench.Codeforces.examples_shard00.P029_690D1_the_wall_easy.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition NonemptyWallColumnBefore
    (grid : list (list Z)) (rows col : Z) : Prop :=
  exists row, 0 <= row < rows /\ Znth col (Znth row grid nil) 0 = 66.

Definition OccupancyValue (occupied : Z) (present : Prop) : Prop :=
  (occupied = 1 /\ present) \/ (occupied = 0 /\ ~ present).

Definition WallColumnsAfterRows
    (grid : list (list Z)) (rows : Z) (occupied : list Z) : Prop :=
  Zlength occupied = 100 /\
  forall col, 0 <= col < 100 ->
    OccupancyValue (Znth col occupied 0)
      (NonemptyWallColumnBefore grid rows col).

Definition WallColumnsDuringRow
    (grid : list (list Z)) (row next_col : Z) (occupied : list Z) : Prop :=
  Zlength occupied = 100 /\
  forall col, 0 <= col < 100 ->
    OccupancyValue (Znth col occupied 0)
      ((col < next_col /\ NonemptyWallColumnBefore grid (row + 1) col) \/
       (next_col <= col /\ NonemptyWallColumnBefore grid row col)).

Definition SegmentCountPrefix
    (grid : list (list Z)) (next_col segments : Z) : Prop :=
  segments = #(fun col : Z =>
    0 <= col < next_col /\ StartsWallSegment grid col).
