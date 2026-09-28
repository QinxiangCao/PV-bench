Require Export PVbench.Codeforces.examples_shard00.P070_886D_restoration_of_string.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import Coq.Sorting.Permutation.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Import ListNotations.

Definition BoundedGraphArray (values : list Z) : Prop :=
  Zlength values = 26 /\
  forall k, 0 <= k < 26 -> -1 <= Znth k values (-1) < 26.

Definition BooleanArray (values : list Z) : Prop :=
  Zlength values = 26 /\
  forall k, 0 <= k < 26 -> Znth k values 0 = 0 \/ Znth k values 0 = 1.

Definition AllMinusOne (values : list Z) : Prop :=
  forall k, 0 <= k < Zlength values -> Znth k values (-1) = -1.

Definition AllZero (values : list Z) : Prop :=
  forall k, 0 <= k < Zlength values -> Znth k values 0 = 0.

Definition UsedInWords (words : list (list Z)) (c : Z) : Prop :=
  exists word, In word words /\ In c word.

Definition AdjacentInWords
    (words : list (list Z)) (left right : Z) : Prop :=
  exists word i,
    In word words /\
    0 <= i /\ i + 1 < Zlength word /\
    Znth i word 0 = left /\ Znth (i + 1) word 0 = right.

Definition CompatibleWords (words : list (list Z)) : Prop :=
  (forall word, In word words -> NoDup word) /\
  (forall left right1 right2,
    AdjacentInWords words left right1 ->
    AdjacentInWords words left right2 -> right1 = right2) /\
  (forall left1 left2 right,
    AdjacentInWords words left1 right ->
    AdjacentInWords words left2 right -> left1 = left2).

Definition EncodesGraph
    (words : list (list Z))
    (next prev used : list Z) : Prop :=
  CompatibleWords words /\
  BoundedGraphArray next /\
  BoundedGraphArray prev /\
  BooleanArray used /\
  (forall c, 0 <= c < 26 ->
    (Znth c used 0 = 1 <-> UsedInWords words (97 + c))) /\
  (forall left right, 0 <= left < 26 -> 0 <= right < 26 ->
    (Znth left next (-1) = right <->
      AdjacentInWords words (97 + left) (97 + right))) /\
  (forall left right, 0 <= left < 26 -> 0 <= right < 26 ->
    (Znth right prev (-1) = left <->
      AdjacentInWords words (97 + left) (97 + right))).

Definition InitState
    (next_prefix prev_prefix used : list Z) : Prop :=
  Zlength next_prefix = Zlength prev_prefix /\
  AllMinusOne next_prefix /\
  AllMinusOne prev_prefix /\
  BooleanArray used /\ AllZero used.

Definition GraphBuildState
    (given : list (list Z)) (words_done : Z)
    (next prev used : list Z) : Prop :=
  Pre given /\
  EncodesGraph (sublist 0 words_done given) next prev used.

Definition WordScanState
    (given : list (list Z)) (word_index scanned : Z)
    (next prev used seen : list Z) (last : Z) : Prop :=
  let word := Znth word_index given [] in
  Pre given /\
  EncodesGraph
    (sublist 0 word_index given ++ [sublist 0 scanned word])
    next prev used /\
  BooleanArray seen /\
  (forall c, 0 <= c < 26 ->
    (Znth c seen 0 = 1 <-> In (97 + c) (sublist 0 scanned word))) /\
  (scanned = 0 /\ last = -1 \/
   0 < scanned /\ last = Znth (scanned - 1) word 0 - 97).

Inductive NextReach (next : list Z) : Z -> Z -> Prop :=
| next_reach_refl : forall c, NextReach next c c
| next_reach_step : forall from mid to,
    Znth from next (-1) = mid ->
    0 <= mid < 26 ->
    NextReach next mid to ->
    NextReach next from to.

Definition IsHead
    (prev used : list Z) (c : Z) : Prop :=
  0 <= c < 26 /\ Znth c used 0 = 1 /\ Znth c prev (-1) = -1.

Definition CompletedHeadSet
    (next prev used : list Z) (heads_done : Z) (visited : list Z) : Prop :=
  BooleanArray visited /\
  forall c, 0 <= c < 26 ->
    (Znth c visited 0 = 1 <->
      exists head,
        0 <= head < heads_done /\
        IsHead prev used head /\ NextReach next head c).

Definition OutputMatchesVisited
    (visited output : list Z) : Prop :=
  NoDup output /\
  (forall c, 0 <= c < 26 ->
    (Znth c visited 0 = 1 <-> In (97 + c) output)).

Inductive PathPrefix (next : list Z) (start : Z) : list Z -> Z -> Prop :=
| path_prefix_start : PathPrefix next start [] start
| path_prefix_step : forall path current successor,
    PathPrefix next start path current ->
    0 <= current < 26 ->
    Znth current next (-1) = successor ->
    PathPrefix next start (path ++ [current]) successor.

Definition MarkedPath
    (before path after : list Z) : Prop :=
  BooleanArray before /\ BooleanArray after /\
  forall c, 0 <= c < 26 ->
    (Znth c after 0 = 1 <->
      Znth c before 0 = 1 \/ In c path).

Inductive OrderedTraversal
    (next prev used : list Z) : Z -> list Z -> Prop :=
| ordered_traversal_zero : OrderedTraversal next prev used 0 []
| ordered_traversal_skip : forall bound output,
    OrderedTraversal next prev used bound output ->
    0 <= bound < 26 ->
    ~ IsHead prev used bound ->
    OrderedTraversal next prev used (bound + 1) output
| ordered_traversal_head : forall bound output path,
    OrderedTraversal next prev used bound output ->
    0 <= bound < 26 ->
    IsHead prev used bound ->
    PathPrefix next bound path (-1) ->
    OrderedTraversal next prev used (bound + 1)
      (output ++ map (fun c => 97 + c) path).

Definition TraversalState
    (next prev used : list Z) (heads_done : Z)
    (visited output : list Z) : Prop :=
  CompletedHeadSet next prev used heads_done visited /\
  OutputMatchesVisited visited output /\
  OrderedTraversal next prev used heads_done output.

Definition PathScanState
    (next prev used : list Z) (start current : Z)
    (visited output : list Z) : Prop :=
  exists visited_before output_before path,
    TraversalState next prev used start visited_before output_before /\
    IsHead prev used start /\
    PathPrefix next start path current /\
    MarkedPath visited_before path visited /\
    output = output_before ++ map (fun c => 97 + c) path /\
    (current = -1 \/
      (0 <= current < 26 /\ Znth current visited 0 = 0)).

Definition CoverageScanState
    (used visited : list Z) (checked : Z) : Prop :=
  BooleanArray used /\ BooleanArray visited /\
  forall c, 0 <= c < checked ->
    Znth c used 0 = 1 -> Znth c visited 0 = 1.

Definition SuccessfulTraversal
    (given : list (list Z))
    (next prev used visited output : list Z) : Prop :=
  EncodesGraph given next prev used /\
  TraversalState next prev used 26 visited output /\
  CoverageScanState used visited 26 /\
  GoodRestoration given output.

Require Import Coq.micromega.Lia.

Require Import Coq.micromega.Psatz.

From Coq Require Import Lia.
