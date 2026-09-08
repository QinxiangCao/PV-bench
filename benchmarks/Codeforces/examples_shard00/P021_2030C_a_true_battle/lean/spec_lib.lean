import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic

namespace Codeforces.examples_shard00.P021_2030C_a_true_battle.lean

open AUXLib

def HasAdjacentOnes (values : List Int) : Prop :=
  ∃ i : Int, 0 ≤ i ∧ i + 1 < Zlength values ∧
    Znth i values 0 = 49 ∧ Znth (i + 1) values 0 = 49

def WinningCriterion (values : List Int) : Prop :=
  Znth 0 values 0 = 49 ∨ Znth (Zlength values - 1) values 0 = 49 ∨ HasAdjacentOnes values

def Pre (values : List Int) : Prop :=
  (2 ≤ Zlength values ∧ Zlength values ≤ 200000) ∧ Forall (fun c => c = 48 ∨ c = 49) values

def Spec (values : List Int) (out : Int) : Prop :=
  (out = 0 ∨ out = 1) ∧ (out = 1 ↔ WinningCriterion values)

end Codeforces.examples_shard00.P021_2030C_a_true_battle.lean
