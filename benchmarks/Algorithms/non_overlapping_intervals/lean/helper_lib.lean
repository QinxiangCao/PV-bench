import Algorithms.non_overlapping_intervals.lean.spec_lib

namespace Algorithms.non_overlapping_intervals.lean

open AUXLib MaxMinLib

def interval_swap (ps : List interval) (i j : Int) : List interval :=
  replace_Znth j (Znth i ps default_interval) (replace_Znth i (Znth j ps default_interval) ps)

def IntervalSwappedAt (before after : List interval) (i j : Int) : Prop := after = interval_swap before i j

def IntervalSameOutsideRange (before after : List interval) (left right : Int) : Prop :=
  Zlength before = Zlength after ∧ ∀ k, (0 ≤ k ∧ k < Zlength before) → (k < left ∨ right < k) →
    Znth k after default_interval = Znth k before default_interval

def IntervalPartitionedAt (ps : List interval) (low high pivot : Int) : Prop :=
  (low ≤ pivot ∧ pivot ≤ high) ∧
    (∀ k, (low ≤ k ∧ k < pivot) → interval_end (Znth k ps default_interval) ≤ interval_end (Znth pivot ps default_interval)) ∧
    (∀ k, (pivot < k ∧ k ≤ high) → interval_end (Znth pivot ps default_interval) < interval_end (Znth k ps default_interval))

def IntervalsEndSortedRange (ps : List interval) (left right : Int) : Prop :=
  ∀ i j, left ≤ i → i ≤ j → j ≤ right → interval_end (Znth i ps default_interval) ≤ interval_end (Znth j ps default_interval)

def LomutoScanState (before current : List interval) (low high placed scanned pivot_end : Int) : Prop :=
  IntervalPermutation before current ∧ IntervalSameOutsideRange before current low high ∧
    interval_end (Znth high current default_interval) = pivot_end ∧
    (∀ k, (low ≤ k ∧ k ≤ placed) → interval_end (Znth k current default_interval) ≤ pivot_end) ∧
    (∀ k, (placed < k ∧ k < scanned) → pivot_end < interval_end (Znth k current default_interval))

def schedule_finish (kept : List interval) : Int := interval_end (Znth (Zlength kept - 1) kept default_interval)

def GreedyPrefixState (ps : List interval) (processed kept_count last_finish : Int) : Prop :=
  ∃ kept, IntervalSelection (sublist 0 processed ps) kept ∧ NonOverlappingSchedule kept ∧
    Zlength kept = kept_count ∧ 0 < Zlength kept ∧ last_finish = schedule_finish kept ∧
    (∀ alternative, IntervalSelection (sublist 0 processed ps) alternative → NonOverlappingSchedule alternative → Zlength alternative ≤ kept_count) ∧
    (∀ alternative, IntervalSelection (sublist 0 processed ps) alternative → NonOverlappingSchedule alternative → Zlength alternative = kept_count → last_finish ≤ schedule_finish alternative)

end Algorithms.non_overlapping_intervals.lean
