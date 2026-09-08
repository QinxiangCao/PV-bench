import Codeforces.examples_shard00.P035_807B_t_shirt_hunt.lean.spec_lib

namespace Codeforces.examples_shard00.P035_807B_t_shirt_hunt.lean

open AUXLib

def ShirtTrace (score : Int) (values : List Int) : Prop :=
  Zlength values = 26 ∧ Znth 0 values 0 = Z.modulo (Z.div score 50) 475 ∧
    ∀ i, (0 ≤ i ∧ i < 25) → Znth (i + 1) values 0 = Z.modulo (Znth i values 0 * 96 + 42) 475

def NoShirtSelection (score place : Int) : Prop := ¬ ShirtSelection score place

def ShirtScanState (score place scanned current : Int) : Prop :=
  ∃ values, ShirtTrace score values ∧ (0 ≤ scanned ∧ scanned ≤ 25) ∧ current = Znth scanned values 0 ∧
    (∀ i, (1 ≤ i ∧ i ≤ scanned) → place ≠ 26 + Znth i values 0)

def AlignmentSearch (x y score : Int) : Prop :=
  y ≤ score ∧ ∀ candidate, (y ≤ candidate ∧ candidate < score) → Z.modulo (candidate - x) 50 ≠ 0

def CandidateSearch (place x y score : Int) : Prop :=
  y ≤ score ∧ Z.modulo (score - x) 50 = 0 ∧ ∀ candidate,
    (y ≤ candidate ∧ candidate < score) → Z.modulo (candidate - x) 50 = 0 → NoShirtSelection candidate place

def FirstWinningCandidate (place x y score : Int) : Prop := CandidateSearch place x y score ∧ ShirtSelection score place

end Codeforces.examples_shard00.P035_807B_t_shirt_hunt.lean
