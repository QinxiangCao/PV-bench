import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import MaxMinLib.Interface

namespace Codeforces.examples_shard00.P030_1113B_sasha_and_magnetic_machines.lean

open AUXLib
open MaxMinLib

def OneMagneticTransfer (before after : List Int) : Prop :=
  after = before ∨ ∃ i j x, (0 ≤ i ∧ i < Zlength before) ∧ (0 ≤ j ∧ j < Zlength before) ∧ i ≠ j ∧
    x > 0 ∧ x ∣ Znth i before 0 ∧ Zlength after = Zlength before ∧
    ∀ k, (0 ≤ k ∧ k < Zlength before) → Znth k after 0 =
      if k = i then Z.div (Znth k before 0) x else if k = j then Znth k before 0 * x else Znth k before 0

def TotalPower (a : List Int) : Int := a.foldr (· + ·) 0

def Pre (a : List Int) : Prop :=
  (2 ≤ Zlength a ∧ Zlength a ≤ 50000) ∧ Forall (fun power => 1 ≤ power ∧ power ≤ 100) a

def Spec (a : List Int) (out : Int) : Prop :=
  min_value_of_subset (· ≤ ·) (OneMagneticTransfer a) TotalPower out

end Codeforces.examples_shard00.P030_1113B_sasha_and_magnetic_machines.lean
