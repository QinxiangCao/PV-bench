Require Export PVbench.Codeforces.examples_shard00.P068_1416C_xor_inverse.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import Coq.Sorting.Permutation.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

From SimpleC.SL Require Import Mem SeparationLogic ArrayLib Array2Lib.

Local Open Scope Z_scope.

Import naive_C_Rules.

Local Open Scope sac.

Definition BitAt (value bit : Z) : Z :=
  Z.land (Z.shiftr value bit) 1.

Definition SameHigherBits
    (segment : list Z) (upper bit i j : Z) : Prop :=
  forall k,
    bit < k <= upper ->
    BitAt (Znth i segment 0) k = BitAt (Znth j segment 0) k.

Definition BitContribution
    (segment : list Z) (upper bit choice count : Z) : Prop :=
  count = #(fun p : Z * Z =>
    (0 <= fst p < Zlength segment /\ 0 <= snd p < Zlength segment) /\
    fst p < snd p /\
    SameHigherBits segment upper bit (fst p) (snd p) /\
    ((choice = 0 /\ BitAt (Znth (fst p) segment 0) bit = 1 /\
                    BitAt (Znth (snd p) segment 0) bit = 0) \/
     (choice = 1 /\ BitAt (Znth (fst p) segment 0) bit = 0 /\
                    BitAt (Znth (snd p) segment 0) bit = 1))).

Definition CostAt (costs : list (list Z)) (bit choice : Z) : Z :=
  Znth choice (Znth bit costs nil) 0.

Definition CostBound (costs : list (list Z)) (limit : Z) : Prop :=
  0 <= limit /\
  Zlength costs = 30 /\
  forall bit choice,
    0 <= bit < 30 -> 0 <= choice < 2 ->
    0 <= CostAt costs bit choice <= limit.

Definition CostTable (input : list Z) (costs : list (list Z)) : Prop :=
  Zlength costs = 30 /\
  (forall bit, 0 <= bit < 30 -> Zlength (Znth bit costs nil) = 2) /\
  (forall bit choice,
    0 <= bit < 30 -> 0 <= choice < 2 ->
    BitContribution input 29 bit choice (CostAt costs bit choice)).

Definition SolveEffect
    (before after : list Z) (cost_before cost_after : list (list Z))
    (l r bit : Z) : Prop :=
  Zlength after = Zlength before /\
  sublist 0 l after = sublist 0 l before /\
  sublist r (Zlength before) after = sublist r (Zlength before) before /\
  Permutation (sublist l r before) (sublist l r after) /\
  Zlength cost_before = 30 /\ Zlength cost_after = 30 /\
  (forall b, 0 <= b < 30 ->
    Zlength (Znth b cost_before nil) = 2 /\
    Zlength (Znth b cost_after nil) = 2) /\
  (forall b choice,
    0 <= b < 30 -> 0 <= choice < 2 ->
    ((0 <= b <= bit /\
      exists delta,
        BitContribution (sublist l r before) bit b choice delta /\
        CostAt cost_after b choice = CostAt cost_before b choice + delta) \/
     (~ (0 <= b <= bit) /\
      CostAt cost_after b choice = CostAt cost_before b choice))) /\
  ((l = 0 /\ r = Zlength before /\ bit = 29 /\
    (forall b choice,
      0 <= b < 30 -> 0 <= choice < 2 -> CostAt cost_before b choice = 0)) ->
    CostTable before cost_after).

Definition SolveCountPrefix
    (before : list Z) (entry_costs current_costs : list (list Z))
    (l i bit zeros ones : Z) : Prop :=
  zeros = #(fun k : Z =>
    l <= k < i /\ BitAt (Znth k before 0) bit = 0) /\
  ones = #(fun k : Z =>
    l <= k < i /\ BitAt (Znth k before 0) bit = 1) /\
  Zlength entry_costs = 30 /\ Zlength current_costs = 30 /\
  (forall b, 0 <= b < 30 ->
    Zlength (Znth b entry_costs nil) = 2 /\
    Zlength (Znth b current_costs nil) = 2) /\
  (forall b choice,
    0 <= b < 30 -> 0 <= choice < 2 ->
    ((b = bit /\
      exists delta,
        BitContribution (sublist l i before) bit bit choice delta /\
        CostAt current_costs b choice = CostAt entry_costs b choice + delta) \/
     (b <> bit /\
      CostAt current_costs b choice = CostAt entry_costs b choice))).

Definition BitIs (bit choice value : Z) : bool :=
  Z.eqb (BitAt value bit) choice.

Definition InitializedSlice
    (cells : list (option Z)) (lo hi : Z) (values : list Z) : Prop :=
  sublist lo hi cells = map (@Some Z) values.

Definition StablePartitionPrefix
    (before : list Z) (scratch : list (option Z))
    (l r bit source_done write_end phase : Z) : Prop :=
  (phase = 0 /\
   InitializedSlice scratch l write_end
     (filter (BitIs bit 0) (sublist l source_done before))) \/
  (phase = 1 /\
   InitializedSlice scratch l write_end
     (filter (BitIs bit 0) (sublist l r before) ++
      filter (BitIs bit 1) (sublist l source_done before))).

Definition PartitionCopyBack
    (before current partitioned : list Z) (l r copied : Z) : Prop :=
  Zlength current = Zlength before /\
  Zlength partitioned = r - l /\
  sublist 0 l current = sublist 0 l before /\
  sublist l copied current = sublist 0 (copied - l) partitioned /\
  sublist copied (Zlength before) current =
    sublist copied (Zlength before) before /\
  Permutation (sublist l r before) partitioned.

Definition InputCopyPrefix
    (input : list Z) (working_cells : list (option Z)) (copied : Z) : Prop :=
  InitializedSlice working_cells 0 copied (sublist 0 copied input).

Definition ZeroCostPrefix
    (cost_cells : list (list (option Z))) (next_row : Z) : Prop :=
  Zlength cost_cells = 30 /\
  (forall row, 0 <= row < 30 -> Zlength (Znth row cost_cells nil) = 2) /\
  (forall row choice,
    0 <= row < next_row -> 0 <= choice < 2 ->
    Znth choice (Znth row cost_cells nil) None = Some 0).

Definition CostArrayMixed : Z -> Z -> Z -> list (list (option Z)) -> Assertion :=
  Int64Array2.mixed_full.

Definition XorChoicePrefix
    (input : list Z) (costs : list (list Z))
    (next_bit inv x : Z) : Prop :=
  CostTable input costs /\
  inv = SumLib.Sum.sum (fun bit : Z => 0 <= bit < next_bit)
    (fun bit => Z.min (CostAt costs bit 0) (CostAt costs bit 1)) /\
  x = SumLib.Sum.sum (fun bit : Z => 0 <= bit < next_bit /\
                    CostAt costs bit 1 < CostAt costs bit 0)
    (fun bit => 2 ^ bit).

Require Import Coq.micromega.Lia.

Require Import Coq.Logic.FunctionalExtensionality.

Require Import Coq.micromega.Psatz.

Require Import Coq.setoid_ring.Ring.
