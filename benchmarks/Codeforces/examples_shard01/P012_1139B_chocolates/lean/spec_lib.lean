import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

namespace Codeforces.examples_shard01.P012_1139B_chocolates.lean

open AUXLib

open MaxMinLib

def FeasiblePurchase (a x : List Int) : Prop :=
  Zlength x = Zlength a ∧
  (∀ i, (0 ≤ i ∧ i < Zlength a) → (0 ≤ Znth i x 0 ∧ Znth i x 0 ≤ Znth i a 0)) ∧
  (∀ j i, ((0 ≤ j ∧ j < i) ∧ i < Zlength a) → Znth j x 0 = 0 ∨ Znth j x 0 < Znth i x 0)

def Pre (a : List Int) : Prop := True

def Spec (a : List Int) (out : Int) : Prop :=
  max_value_of_subset (· ≤ ·) (fun v => ∃ x, FeasiblePurchase a x ∧ v = x.foldr (· + ·) 0) (fun x => x) out

end Codeforces.examples_shard01.P012_1139B_chocolates.lean
