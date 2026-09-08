import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

namespace Algorithms.energy_necklace.lean

open AUXLib MaxMinLib

def EnergyValsDuplicated (beads vals : List Int) (n : Int) : Prop :=
  0 ≤ n ∧ Zlength beads = n ∧ Zlength vals = 2 * n ∧
  (∀ i : Int, (0 ≤ i ∧ i < n) → Znth i vals 0 = Znth i beads 0) ∧
  (∀ i : Int, (0 ≤ i ∧ i < n) → Znth (n + i) vals 0 = Znth i beads 0)

def EnergyLabelsBounded (beads : List Int) (n : Int) : Prop :=
  Zlength beads = n ∧ ∀ i : Int, (0 ≤ i ∧ i < n) → (1 ≤ Znth i beads 0 ∧ Znth i beads 0 ≤ 1000)

inductive EnergyIntervalPlan (vals : List Int) : Int → Int → Int → Prop where
  | EnergyIntervalPlan_single (left : Int) : 0 ≤ left → left + 1 < Zlength vals →
      EnergyIntervalPlan vals left left 0
  | EnergyIntervalPlan_merge (left split right e_left e_right : Int) :
      0 ≤ left → (left ≤ split ∧ split < right) → right + 1 < Zlength vals →
      EnergyIntervalPlan vals left split e_left → EnergyIntervalPlan vals (split + 1) right e_right →
      EnergyIntervalPlan vals left right
        (e_left + e_right + Znth left vals 0 * Znth (split + 1) vals 0 * Znth (right + 1) vals 0)

export EnergyIntervalPlan (EnergyIntervalPlan_single EnergyIntervalPlan_merge)

def EnergyIntervalBest (vals : List Int) (left right answer : Int) : Prop :=
  MaxMinLib.max_value_of_subset (· ≤ ·) (fun energy => EnergyIntervalPlan vals left right energy)
    (fun energy => energy) answer

def EnergyRotationBest (beads : List Int) (n start answer : Int) : Prop :=
  ∃ vals, EnergyValsDuplicated beads vals n ∧ (0 ≤ start ∧ start < n) ∧
    EnergyIntervalBest vals start (start + n - 1) answer

def EnergyNecklaceAnswer (beads : List Int) (n answer : Int) : Prop :=
  MaxMinLib.max_value_of_subset (· ≤ ·)
    (fun energy => ∃ start : Int, (0 ≤ start ∧ start < n) ∧ EnergyRotationBest beads n start energy)
    (fun energy => energy) answer

def EnergyCellIndex (width left right : Int) : Int := left * width + right

def EnergyLenDone (vals dp : List Int) (total width len : Int) : Prop :=
  0 ≤ total ∧ width = total ∧ Zlength vals = total ∧ Zlength dp = total * width ∧ 1 ≤ len ∧
  ∀ l left right idx : Int, (1 ≤ l ∧ l < len) → right = left + l - 1 →
    idx = EnergyCellIndex width left right → 0 ≤ left → left + l < Zlength vals →
    EnergyIntervalBest vals left right (Znth idx dp 0)

def EnergySplitArithmeticBounded (vals dp : List Int) (width left right split bound : Int) : Prop :=
  let left_value := Znth (EnergyCellIndex width left split) dp 0
  let right_value := Znth (EnergyCellIndex width (split + 1) right) dp 0
  let gain := Znth left vals 0 * Znth (split + 1) vals 0 * Znth (right + 1) vals 0
  (0 ≤ left_value ∧ left_value ≤ bound) ∧ (0 ≤ right_value ∧ right_value ≤ bound) ∧
  (0 ≤ gain ∧ gain ≤ bound) ∧ (0 ≤ left_value + right_value ∧ left_value + right_value ≤ bound) ∧
  (0 ≤ left_value + right_value + gain ∧ left_value + right_value + gain ≤ bound)

def EnergyComputationBounded (beads : List Int) (n bound : Int) : Prop :=
  0 ≤ bound ∧
  (∀ vals dp total width len left right split,
    EnergyValsDuplicated beads vals n → total = 2 * n → width = total → (2 ≤ len ∧ len ≤ n) →
    (0 ≤ left ∧ left < total - len) → right = left + len - 1 → (left ≤ split ∧ split < right) →
    Zlength dp = total * width → EnergyLenDone vals dp total width len →
    EnergySplitArithmeticBounded vals dp width left right split bound) ∧
  (∀ vals left right answer, EnergyValsDuplicated beads vals n → 0 ≤ left → left ≤ right →
    right + 1 < Zlength vals → EnergyIntervalBest vals left right answer → (0 ≤ answer ∧ answer ≤ bound)) ∧
  (∀ vals dp total width start, EnergyValsDuplicated beads vals n → total = 2 * n → width = total →
    (0 ≤ start ∧ start < n) → Zlength dp = total * width → EnergyLenDone vals dp total width (n + 1) →
    (0 ≤ Znth (EnergyCellIndex width start (start + n - 1)) dp 0 ∧
     Znth (EnergyCellIndex width start (start + n - 1)) dp 0 ≤ bound))

end Algorithms.energy_necklace.lean
