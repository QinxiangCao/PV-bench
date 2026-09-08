import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import MaxMinLib.Interface

namespace Codeforces.examples_shard00.P035_807B_t_shirt_hunt.lean

open AUXLib
open MaxMinLib

def ShirtSelection (score place : Int) : Prop :=
  ∃ values, Zlength values = 26 ∧ Znth 0 values 0 = Z.modulo (Z.div score 50) 475 ∧
    (∀ i, (0 ≤ i ∧ i < 25) → Znth (i + 1) values 0 = Z.modulo (Znth i values 0 * 96 + 42) 475) ∧
    ∃ i, (1 ≤ i ∧ i ≤ 25) ∧ place = 26 + Znth i values 0

def GoalWithHacks (p x y successful : Int) : Prop :=
  ∃ unsuccessful, 0 ≤ unsuccessful ∧ y ≤ x + 100 * successful - 50 * unsuccessful ∧
    ShirtSelection (x + 100 * successful - 50 * unsuccessful) p

def Pre (p x y : Int) : Prop :=
  (26 ≤ p ∧ p ≤ 500) ∧ (1 ≤ y ∧ y ≤ x) ∧ x ≤ 20000 ∧ ∃ successful, 0 ≤ successful ∧ GoalWithHacks p x y successful

def Spec (p x y out : Int) : Prop :=
  min_value_of_subset (· ≤ ·) (fun successful : Int => 0 ≤ successful ∧ GoalWithHacks p x y successful) (fun successful => successful) out

end Codeforces.examples_shard00.P035_807B_t_shirt_hunt.lean
