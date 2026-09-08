import Algorithms.energy_necklace.lean.spec_lib

namespace Algorithms.energy_necklace.lean

open AUXLib MaxMinLib

def EnergyZeroTable (dp : List Int) (total width : Int) : Prop :=
  0 ≤ total ∧ width = total ∧ Zlength dp = total * width ∧
  ∀ idx : Int, (0 ≤ idx ∧ idx < total * width) → Znth idx dp 0 = 0

def EnergyLeftProgress (vals dp : List Int) (total width len left : Int) : Prop :=
  EnergyLenDone vals dp total width len ∧ 2 ≤ len ∧ 0 ≤ left ∧
  ∀ done_left right idx : Int, (0 ≤ done_left ∧ done_left < left) → right = done_left + len - 1 →
    idx = EnergyCellIndex width done_left right → done_left + len < Zlength vals →
    EnergyIntervalBest vals done_left right (Znth idx dp 0)

def EnergySplitCandidate (vals dp : List Int) (width left right split candidate : Int) : Prop :=
  (left ≤ split ∧ split < right) ∧ right + 1 < Zlength vals ∧
  candidate = Znth (EnergyCellIndex width left split) dp 0 +
    Znth (EnergyCellIndex width (split + 1) right) dp 0 +
    Znth left vals 0 * Znth (split + 1) vals 0 * Znth (right + 1) vals 0

def EnergySplitProgress (vals dp : List Int) (total width len left split best : Int) : Prop :=
  EnergyLeftProgress vals dp total width len left ∧
  let right := left + len - 1
  2 ≤ len ∧ 0 ≤ left ∧ left + len ≤ total ∧ right = left + len - 1 ∧
  (left ≤ split ∧ split ≤ right) ∧ (0 ≤ best ∧ best ≤ 2100000000) ∧
  ((split = left ∧ best = 0) ∨ (left < split ∧
    MaxMinLib.max_value_of_subset (· ≤ ·)
      (fun candidate => ∃ k : Int, (left ≤ k ∧ k < split) ∧
        EnergySplitCandidate vals dp width left right k candidate)
      (fun candidate => candidate) best))

def EnergyUpdatedCell (vals old_dp new_dp : List Int) (width left right value : Int) : Prop :=
  (0 ≤ EnergyCellIndex width left right ∧ EnergyCellIndex width left right < Zlength old_dp) ∧
  new_dp = replace_Znth (EnergyCellIndex width left right) value old_dp ∧ EnergyIntervalBest vals left right value

def EnergyAnswerProgress (beads vals dp : List Int) (n total width start answer : Int) : Prop :=
  EnergyValsDuplicated beads vals n ∧ Zlength dp = total * width ∧ width = total ∧
  (0 ≤ start ∧ start ≤ n) ∧ (0 ≤ answer ∧ answer ≤ 2100000000) ∧
  ((start = 0 ∧ answer = 0) ∨ (0 < start ∧
    MaxMinLib.max_value_of_subset (· ≤ ·)
      (fun value => ∃ s : Int, (0 ≤ s ∧ s < start) ∧ EnergyIntervalBest vals s (s + n - 1) value)
      (fun value => value) answer))

end Algorithms.energy_necklace.lean
