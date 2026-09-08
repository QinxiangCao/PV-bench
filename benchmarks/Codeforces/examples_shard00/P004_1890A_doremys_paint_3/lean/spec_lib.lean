import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic

namespace Codeforces.examples_shard00.P004_1890A_doremys_paint_3.lean

open AUXLib

def GoodAdjacentSums (b : List Int) : Prop :=
  ∃ k, ∀ i, (0 ≤ i ∧ i < Zlength b - 1) → Znth i b 0 + Znth (i + 1) b 0 = k

def Pre (a : List Int) : Prop :=
  (2 ≤ Zlength a ∧ Zlength a ≤ 100) ∧ Forall (fun x => 1 ≤ x ∧ x ≤ 100000) a

def Spec (a : List Int) (out : Int) : Prop :=
  (out = 0 ∨ out = 1) ∧ (out = 1 ↔ ∃ b, List.Perm a b ∧ GoodAdjacentSums b)

end Codeforces.examples_shard00.P004_1890A_doremys_paint_3.lean
