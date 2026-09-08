import Codeforces.examples_shard00.P003_1763A_absolute_maximization.lean.spec_lib

namespace Codeforces.examples_shard00.P003_1763A_absolute_maximization.lean

open AUXLib

def BitwiseScanState (a : List Int) (i acc_or acc_and : Int) : Prop :=
  (0 ≤ i ∧ i ≤ Zlength a) ∧
  (∀ b, 0 ≤ b → (Z.testbit acc_or b = true ↔ ∃ j, (0 ≤ j ∧ j < i) ∧ Z.testbit (Znth j a 0) b = true)) ∧
  (∀ b, 0 ≤ b → (Z.testbit acc_and b = true ↔ ∀ j, (0 ≤ j ∧ j < max 1 i) → Z.testbit (Znth j a 0) b = true))

end Codeforces.examples_shard00.P003_1763A_absolute_maximization.lean
