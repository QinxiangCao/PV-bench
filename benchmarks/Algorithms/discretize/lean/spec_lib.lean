import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic

namespace Algorithms.discretize.lean

open AUXLib

def strict_increasing_prefix (l : List Int) (len : Int) : Prop :=
  (0 ≤ len ∧ len ≤ Zlength l) ∧ ∀ i j, (0 ≤ i ∧ i < j) → j < len → Znth i l 0 < Znth j l 0

def same_values_prefix (out : List Int) (out_len : Int) (src : List Int) (src_len : Int) : Prop :=
  ∀ x, x ∈ sublist 0 out_len out ↔ x ∈ sublist 0 src_len src

def discretize_result (src : List Int) (n : Int) (out : List Int) (ret : Int) : Prop :=
  Zlength src = n ∧ Zlength out = n ∧ 1 ≤ n ∧ (1 ≤ ret ∧ ret ≤ n) ∧ strict_increasing_prefix out ret ∧
  same_values_prefix out ret src n ∧
  (∀ i, (0 ≤ i ∧ i < n) → ∃ r, (0 ≤ r ∧ r < ret) ∧ Znth r out 0 = Znth i src 0) ∧
  (∀ r, (0 ≤ r ∧ r < ret) → ∃ i, (0 ≤ i ∧ i < n) ∧ Znth r out 0 = Znth i src 0) ∧
  ∀ i j ri rj, (0 ≤ i ∧ i < n) → (0 ≤ j ∧ j < n) → (0 ≤ ri ∧ ri < ret) → (0 ≤ rj ∧ rj < ret) →
    Znth ri out 0 = Znth i src 0 → Znth rj out 0 = Znth j src 0 →
    (Znth i src 0 = Znth j src 0 → ri = rj) ∧ (Znth i src 0 < Znth j src 0 → ri < rj)

end Algorithms.discretize.lean
