import Codeforces.examples_shard00.P030_1113B_sasha_and_magnetic_machines.lean.spec_lib

namespace Codeforces.examples_shard00.P030_1113B_sasha_and_magnetic_machines.lean

open AUXLib
open MaxMinLib

def PrefixSummary (a : List Int) (i total least : Int) : Prop :=
  (0 ≤ i ∧ i ≤ Zlength a) ∧ total = TotalPower (sublist 0 i a) ∧
    ((i = 0 ∧ least = 101) ∨ (0 < i ∧ ∃ least_index,
      (0 ≤ least_index ∧ least_index < i) ∧ least = Znth least_index a 0 ∧
      ∀ k, (0 ≤ k ∧ k < i) → least ≤ Znth k a 0))

def EnumeratedCost (a : List Int) (total least i x cost : Int) : Prop :=
  cost = total ∨ ∃ source factor, (0 ≤ source ∧ source < Zlength a) ∧
    (2 ≤ factor ∧ factor ≤ Znth source a 0) ∧ factor ∣ Znth source a 0 ∧
    (source < i ∨ (source = i ∧ factor < x)) ∧
    cost = total - Znth source a 0 - least + Z.div (Znth source a 0) factor + least * factor

def SearchMinimum (a : List Int) (total least i x answer : Int) : Prop :=
  min_value_of_subset (· ≤ ·) (EnumeratedCost a total least i x) (fun cost => cost) answer

end Codeforces.examples_shard00.P030_1113B_sasha_and_magnetic_machines.lean
