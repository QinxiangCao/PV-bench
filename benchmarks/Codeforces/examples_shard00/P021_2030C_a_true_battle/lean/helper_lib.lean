import Codeforces.examples_shard00.P021_2030C_a_true_battle.lean.spec_lib

namespace Codeforces.examples_shard00.P021_2030C_a_true_battle.lean

open AUXLib

def NoAdjacentOnesBefore (values : List Int) (upto : Int) : Prop :=
  ∀ i : Int, (0 ≤ i ∧ i < upto) → Znth i values 0 ≠ 49 ∨ Znth (i + 1) values 0 ≠ 49

end Codeforces.examples_shard00.P021_2030C_a_true_battle.lean
