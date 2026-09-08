import Algorithms.sort_point.lean.spec_lib

namespace Algorithms.sort_point.lean

open AUXLib

def PolarLt (gp a b : point) : Prop := PolarCmpResult gp a b (-1)

def PointSortedRange (gp : point) (l : List point) (left right : Int) : Prop :=
  ∀ i j, left ≤ i → i ≤ j → j ≤ right → PolarLe gp (Znth i l default_point) (Znth j l default_point)

def PointSameOutsideRange (l l1 : List point) (left right : Int) : Prop :=
  Zlength l = Zlength l1 ∧ ∀ k, (0 ≤ k ∧ k < Zlength l) → (k < left ∨ right < k) → Znth k l1 default_point = Znth k l default_point

def PointMemoryModel (gp : point) (flat : List Int) (n : Int) : Prop :=
  ∃ pts, Zlength pts = n ∧ FlatPoints flat pts ∧ PointCoordsBound (gp :: pts)

def PointRangeSortResult (gp : point) (flat_in : List Int) (pts_out : List point) (left right : Int) : Prop :=
  ∀ pts_in, FlatPoints flat_in pts_in → PointCoordsBound (gp :: pts_in) →
    PointPermutation pts_in pts_out ∧ PointSameOutsideRange pts_in pts_out left right ∧ PointSortedRange gp pts_out left right

def PointPartitionedAt (gp : point) (l : List point) (low high p : Int) : Prop :=
  (low ≤ p ∧ p ≤ high) ∧ Forall (fun x => PolarLe gp x (Znth p l default_point)) (sublist low p l) ∧
    Forall (fun x => PolarLt gp (Znth p l default_point) x) (sublist (p+1) (high+1) l)

def PointPartitionScanInv (gp : point) (before cur : List point) (low high : Int) (pivot : point) (i j : Int) : Prop :=
  PointPermutation before cur ∧ PointSameOutsideRange before cur low high ∧ Znth high cur default_point = pivot ∧
    (∀ k, (low ≤ k ∧ k ≤ i) → PolarLe gp (Znth k cur default_point) pivot) ∧
    ∀ k, (i < k ∧ k < j) → PolarLt gp pivot (Znth k cur default_point)

def point_swap_points (l : List point) (i j : Int) : List point :=
  replace_Znth j (Znth i l default_point) (replace_Znth i (Znth j l default_point) l)

def point_swap_flat (flat : List Int) (i j : Int) : List Int :=
  let xi := Znth (2*i) flat 0
  let yi := Znth (2*i+1) flat 0
  let xj := Znth (2*j) flat 0
  let yj := Znth (2*j+1) flat 0
  replace_Znth (2*j+1) yi (replace_Znth (2*j) xi (replace_Znth (2*i+1) yj (replace_Znth (2*i) xj flat)))

end Algorithms.sort_point.lean
