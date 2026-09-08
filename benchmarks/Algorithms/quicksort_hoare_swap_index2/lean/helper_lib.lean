import AUXLib.Sorting
import SimpleC.SL.SeparationLogic

namespace Algorithms.quicksort_hoare_swap_index2.lean

open AUXLib

def same_outside_range (l l1 : List Int) (left right : Int) : Prop :=
  Zlength l = Zlength l1 ∧ ∀ k, (0 ≤ k ∧ k < Zlength l) →
    (k < left ∨ right < k) → Znth k l1 0 = Znth k l 0

def partitioned_at (l : List Int) (low high p : Int) : Prop :=
  (low ≤ p ∧ p ≤ high) ∧
  Forall (fun x => x ≤ Znth p l 0) (sublist low p l) ∧
  Forall (fun x => Znth p l 0 ≤ x) (sublist (p + 1) (high + 1) l)

def range_nondecreasing (l : List Int) (left right : Int) : Prop :=
  ∀ i j, left ≤ i → i ≤ j → j ≤ right → Znth i l 0 ≤ Znth j l 0

end Algorithms.quicksort_hoare_swap_index2.lean
