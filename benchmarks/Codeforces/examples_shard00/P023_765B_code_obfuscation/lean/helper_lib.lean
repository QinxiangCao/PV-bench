import Codeforces.examples_shard00.P023_765B_code_obfuscation.lean.spec_lib

namespace Codeforces.examples_shard00.P023_765B_code_obfuscation.lean

open AUXLib

def ObfuscationPrefixState (s : List Int) (processed next : Int) : Prop :=
  (0 ≤ processed ∧ processed ≤ Zlength s) ∧ (97 ≤ next ∧ next ≤ 122) ∧
  (∀ c d j, 97 ≤ c → c < d → d ≤ 122 → FirstOccurrence s d j → j < processed → ∃ k, FirstOccurrence s c k ∧ k < j) ∧
  (∀ k, (0 ≤ k ∧ k < processed) → Znth k s 0 ≤ next) ∧
  (∀ c, (97 ≤ c ∧ c < next) → ∃ k, FirstOccurrence s c k ∧ k < processed) ∧
  (next < 122 → ∀ k, (0 ≤ k ∧ k < processed) → Znth k s 0 ≠ next)

end Codeforces.examples_shard00.P023_765B_code_obfuscation.lean
