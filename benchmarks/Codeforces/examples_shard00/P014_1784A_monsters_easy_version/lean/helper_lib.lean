import Codeforces.examples_shard00.P014_1784A_monsters_easy_version.lean.spec_lib

namespace Codeforces.examples_shard00.P014_1784A_monsters_easy_version.lean

open AUXLib

def PrefixGreedyState (original sorted : List Int) (processed kept spent : Int) : Prop :=
  (0 ≤ processed ∧ processed ≤ Zlength sorted) ∧ ∃ prepared,
    MaximalCascadePreparation (sublist 0 processed sorted) prepared ∧ kept = prepared.getLastD 0 ∧
    spent = ZListSum (sublist 0 processed sorted) - ZListSum prepared ∧ (processed = Zlength sorted → Spec original spent)

end Codeforces.examples_shard00.P014_1784A_monsters_easy_version.lean
