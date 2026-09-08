import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

namespace Algorithms.non_overlapping_intervals.lean

open AUXLib MaxMinLib

def interval : Type := Int × Int

def mk_interval (start finish : Int) : interval := (start, finish)

def interval_start (p : interval) : Int := p.1

def interval_end (p : interval) : Int := p.2

def default_interval : interval := mk_interval 0 1

def PairIntervals (starts ends : List Int) (ps : List interval) : Prop :=
  Zlength starts = Zlength ends ∧ Zlength ps = Zlength starts ∧ ∀ k, (0 ≤ k ∧ k < Zlength starts) →
    Znth k ps default_interval = mk_interval (Znth k starts 0) (Znth k ends 0)

def IntervalBounds (ps : List interval) : Prop :=
  Forall (fun p => -10000 ≤ interval_start p ∧ interval_start p < interval_end p ∧ interval_end p ≤ 10000) ps

def IntervalPermutation : List interval → List interval → Prop := List.Perm

def IntervalsEndSorted (ps : List interval) : Prop :=
  ∀ i j, 0 ≤ i → i ≤ j → j < Zlength ps → interval_end (Znth i ps default_interval) ≤ interval_end (Znth j ps default_interval)

def NonOverlappingSchedule (kept : List interval) : Prop :=
  ∀ i j, 0 ≤ i → i < j → j < Zlength kept → interval_end (Znth i kept default_interval) ≤ interval_start (Znth j kept default_interval)

def IntervalSelection (input kept : List interval) : Prop := ∃ removed, List.Perm input (kept ++ removed)

def FeasibleRemovalCount (input : List interval) (removed_count : Int) : Prop :=
  ∃ kept, IntervalSelection input kept ∧ NonOverlappingSchedule kept ∧ removed_count = Zlength input - Zlength kept

def MinimumRemovals (input : List interval) (answer : Int) : Prop :=
  min_value_of_subset (· ≤ ·) (FeasibleRemovalCount input) (fun removed_count => removed_count) answer

end Algorithms.non_overlapping_intervals.lean
