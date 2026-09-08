Require Import PVbench.Codeforces.examples_shard00.P039_1955D_inaccurate_subsequence_search.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import Coq.Sorting.Permutation.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

(* Implementation-facing mathematical states.  These declarations are
   intentionally phrased in terms of multisets and finite prefixes rather
   than as an execution model of the C loops. *)
Definition z_min (x y : Z) : Z := Z.min x y.

Definition Occurrences (xs : list Z) (value : Z) : Z :=
  #(fun i : Z =>
      0 <= i < Zlength xs /\ Znth i xs 0 = value).

Definition FrequencyTable (xs table : list Z) : Prop :=
  Zlength table = 1000001 /\
  forall value, 0 <= value < 1000001 ->
    Znth value table 0 = Occurrences xs value.

Definition TableMatchScore
    (need_table have_table : list Z) (score : Z) : Prop :=
  score = SumLib.Sum.sum
    (fun value : Z => 0 <= value < 1000001)
    (fun value =>
       Z.min (Znth value need_table 0) (Znth value have_table 0)).

Definition CountedGoodWindows
    (k : Z) (values b : list Z) (upto answer : Z) : Prop :=
  answer = #(fun start : Z =>
    0 <= start < upto /\
    GoodWindow b
      (sublist start (start + Zlength b) values) k).

Definition ClearedByPrefix
    (original source : list Z) (upto : Z) (table : list Z) : Prop :=
  Zlength table = 1000001 /\
  (forall value,
     0 <= value < 1000001 ->
     (forall i, 0 <= i < upto -> Znth i source 0 <> value) ->
     Znth value table 0 = Znth value original 0) /\
  (forall i, 0 <= i < upto ->
     Znth (Znth i source 0) table 0 = 0).
