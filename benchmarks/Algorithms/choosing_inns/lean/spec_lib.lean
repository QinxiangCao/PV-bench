import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic

namespace Algorithms.choosing_inns.lean

open AUXLib

def zrange (n : Int) : List Int := (List.range n.toNat).map Int.ofNat

def zrange_between (lo hi : Int) : List Int :=
  (List.range (hi - lo + 1).toNat).map (fun t : Nat => lo + (t : Int))

def affordable_betweenb (costs : List Int) (p lo hi : Int) : Bool :=
  (zrange_between lo hi).any (fun idx => decide (Znth idx costs 0 ≤ p))

def same_colorb (colors : List Int) (a b : Int) : Bool :=
  decide (Znth a colors 0 = Znth b colors 0)

def choosing_pairb (colors costs : List Int) (p : Int) (pair : Int × Int) : Bool :=
  same_colorb colors pair.1 pair.2 && affordable_betweenb costs p pair.1 pair.2

def choosing_pairs_up_to (n : Int) : List (Int × Int) :=
  (zrange n).flatMap (fun right => (zrange right).map (fun left => (left, right)))

def choosing_pair_count (colors costs : List Int) (p n : Int) : Int :=
  Int.ofNat ((choosing_pairs_up_to n).filter (choosing_pairb colors costs p)).length

def ChoosingInputSafe (colors costs : List Int) (n k p : Int) : Prop :=
  (0 ≤ n ∧ n ≤ 200000) ∧ (1 ≤ k ∧ k ≤ 50) ∧ (0 ≤ p ∧ p ≤ 100) ∧
  Zlength colors = n ∧ Zlength costs = n ∧
  (∀ idx, (0 ≤ idx ∧ idx < n) → 0 ≤ Znth idx colors 0 ∧ Znth idx colors 0 < k) ∧
  (∀ idx, (0 ≤ idx ∧ idx < n) → 0 ≤ Znth idx costs 0 ∧ Znth idx costs 0 ≤ 100)

def ChoosingInnsAnswer (colors costs : List Int) (n k p answer : Int) : Prop :=
  answer = choosing_pair_count colors costs p n

end Algorithms.choosing_inns.lean
