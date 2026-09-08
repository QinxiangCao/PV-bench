import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import MaxMinLib.Interface
import SetsClass.RelsDomain

namespace Codeforces.examples_shard00.P003_1763A_absolute_maximization.lean

open AUXLib
open MaxMinLib

def SameBitsExcept (x y b : Int) : Prop :=
  ∀ k, 0 ≤ k → k ≠ b → Z.testbit x k = Z.testbit y k

def OneBitSwap (n : Int) (before after : List Int) : Prop :=
  ∃ i j b xi xj yi yj,
    (0 ≤ i ∧ i < n) ∧ (0 ≤ j ∧ j < n) ∧ 0 ≤ b ∧
    xi = Znth i before 0 ∧ xj = Znth j before 0 ∧
    yi = Znth i after 0 ∧ yj = Znth j after 0 ∧
    Zlength after = Zlength before ∧
    (∀ k, (0 ≤ k ∧ k < n) → k ≠ i → k ≠ j → Znth k after 0 = Znth k before 0) ∧
    SameBitsExcept xi yi b ∧ SameBitsExcept xj yj b ∧
    Z.testbit yi b = Z.testbit xj b ∧ Z.testbit yj b = Z.testbit xi b

def ReachableByBitSwaps (n : Int) (a out : List Int) : Prop :=
  clos_refl_trans (OneBitSwap n) a out

def ArraySpread (a : List Int) (d : Int) : Prop :=
  max_value_of_subset (· ≤ ·) (fun endpoints : Int × Int => endpoints.1 ∈ a ∧ endpoints.2 ∈ a)
    (fun endpoints => endpoints.2 - endpoints.1) d

def Pre (a : List Int) : Prop :=
  (3 ≤ Zlength a ∧ Zlength a ≤ 512) ∧ Forall (fun x => 0 ≤ x ∧ x < 1024) a

def Spec (a : List Int) (out : Int) : Prop :=
  max_value_of_subset (· ≤ ·)
    (fun candidate : List Int × Int => ReachableByBitSwaps (Zlength a) a candidate.1 ∧ ArraySpread candidate.1 candidate.2)
    Prod.snd out

end Codeforces.examples_shard00.P003_1763A_absolute_maximization.lean
