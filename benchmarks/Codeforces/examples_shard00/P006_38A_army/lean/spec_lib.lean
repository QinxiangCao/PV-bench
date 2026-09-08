import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic

namespace Codeforces.examples_shard00.P006_38A_army.lean

open AUXLib

def Pre (n : Int) (years : List Int) (a b : Int) : Prop :=
  (2 ≤ n ∧ n ≤ 100) ∧ Zlength years = n - 1 ∧
  Forall (fun d => 1 ≤ d ∧ d ≤ 100) years ∧ (1 ≤ a ∧ a < b) ∧ b ≤ n

def Spec (n : Int) (years : List Int) (a b out : Int) : Prop :=
  out = (sublist (a - 1) (b - 1) years).foldr (· + ·) 0

end Codeforces.examples_shard00.P006_38A_army.lean
