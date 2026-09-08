import Algorithms.discretize.lean.spec_lib

namespace Algorithms.discretize.lean

open AUXLib

def permutation : List Int → List Int → Prop := Permutation

def increasing_aux : List Int → Int → Prop
  | [], _ => True
  | y :: l, x => x ≤ y ∧ increasing_aux l y

def increasing : List Int → Prop
  | [] => True
  | x :: l => increasing_aux l x

def same_outside_range (l l1 : List Int) (left right : Int) : Prop :=
  Zlength l = Zlength l1 ∧ ∀ k, (0 ≤ k ∧ k < Zlength l) → (k < left ∨ right < k) → Znth k l1 0 = Znth k l 0

def partitioned_at (l : List Int) (low high p : Int) : Prop :=
  (low ≤ p ∧ p ≤ high) ∧ Forall (fun x => x ≤ Znth p l 0) (sublist low p l) ∧
    Forall (fun x => Znth p l 0 < x) (sublist (p+1) (high+1) l)

def partition_scan_inv (l l1 : List Int) (low high pivot i j : Int) : Prop :=
  permutation l l1 ∧ same_outside_range l l1 low high ∧ Znth high l1 0 = pivot ∧
    (∀ k, (low ≤ k ∧ k ≤ i) → Znth k l1 0 ≤ pivot) ∧
    ∀ k, (i < k ∧ k < j) → pivot < Znth k l1 0

inductive sorted_range (l : List Int) : Int → Int → Prop where
  | sorted_range_base (left right : Int) : left ≥ right → sorted_range l left right
  | sorted_range_from_left (left right p : Int) :
      p ≥ right → partitioned_at l left right p → sorted_range l left (p-1) → sorted_range l left right
  | sorted_range_from_right (left right p : Int) :
      p ≤ left → partitioned_at l left right p → sorted_range l (p+1) right → sorted_range l left right
  | sorted_range_from_both (left right p : Int) :
      (left ≤ p ∧ p ≤ right) → partitioned_at l left right p →
        sorted_range l left (p-1) → sorted_range l (p+1) right → sorted_range l left right

@[match_pattern] abbrev sorted_range_base (l : List Int) (left right : Int) (h : left ≥ right) :=
  sorted_range.sorted_range_base (l := l) left right h

@[match_pattern] abbrev sorted_range_from_left (l : List Int) (left right p : Int) (h : p ≥ right)
    (hp : partitioned_at l left right p) (hs : sorted_range l left (p-1)) :=
  sorted_range.sorted_range_from_left (l := l) left right p h hp hs

@[match_pattern] abbrev sorted_range_from_right (l : List Int) (left right p : Int) (h : p ≤ left)
    (hp : partitioned_at l left right p) (hs : sorted_range l (p+1) right) :=
  sorted_range.sorted_range_from_right (l := l) left right p h hp hs

@[match_pattern] abbrev sorted_range_from_both (l : List Int) (left right p : Int) (h : left ≤ p ∧ p ≤ right)
    (hp : partitioned_at l left right p) (hl : sorted_range l left (p-1)) (hr : sorted_range l (p+1) right) :=
  sorted_range.sorted_range_from_both (l := l) left right p h hp hl hr

def strict_increasing (l : List Int) : Prop := strict_increasing_prefix l (Zlength l)

def dedup_scan_inv (src sorted cur : List Int) (slow fast : Int) : Prop :=
  Zlength src = Zlength sorted ∧ Zlength cur = Zlength sorted ∧ permutation src sorted ∧ increasing sorted ∧
  (1 ≤ fast ∧ fast ≤ Zlength sorted) ∧ (0 ≤ slow ∧ slow < fast) ∧ strict_increasing_prefix cur (slow+1) ∧
  same_values_prefix cur (slow+1) sorted fast ∧
  (∀ k, (fast ≤ k ∧ k < Zlength sorted) → Znth k cur 0 = Znth k sorted 0) ∧
  Znth slow cur 0 = Znth (fast-1) sorted 0

def query_forward_result (map : List Int) (map_size target ret : Int) : Prop :=
  ((∃ i, (0 ≤ i ∧ i < map_size) ∧ Znth i map 0 = target ∧ ret=i) ∧
    (∀ j, (0 ≤ j ∧ j < map_size) → Znth j map 0 = target → ret=j)) ∨
  ((∀ i, (0 ≤ i ∧ i < map_size) → Znth i map 0 ≠ target) ∧ ret = -1)

def query_forward_search_inv (map : List Int) (map_size target low high : Int) : Prop :=
  0 ≤ low ∧ high < map_size ∧ low ≤ high+1 ∧
  (∀ i, (0 ≤ i ∧ i < low) → Znth i map 0 < target) ∧
  ∀ i, (high < i ∧ i < map_size) → target < Znth i map 0

end Algorithms.discretize.lean
