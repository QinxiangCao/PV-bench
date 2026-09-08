import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import MaxMinLib.Interface

namespace Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe.lean

open AUXLib
open MaxMinLib

def SegmentMex (a : List Int) (l r w : Int) : Prop :=
  min_value_of_subset (· ≤ ·) (fun candidate : Int => 0 ≤ candidate ∧
    ∀ i, (l ≤ i ∧ i ≤ r) → Znth i a 0 ≠ candidate) (fun candidate => candidate) w

def OneSnap (before after : List Int) : Prop :=
  ∃ l r w, (0 ≤ l ∧ l ≤ r) ∧ r < Zlength before ∧ SegmentMex before l r w ∧
    Zlength after = Zlength before ∧ ∀ i, (0 ≤ i ∧ i < Zlength before) →
      Znth i after 0 = if l ≤ i ∧ i ≤ r then w else Znth i before 0

def SnapTrace (initial : List Int) (states : List (List Int)) : Prop :=
  0 < Zlength states ∧ Znth 0 states [] = initial ∧
  (∀ k, (0 ≤ k ∧ k < Zlength states - 1) → OneSnap (Znth k states []) (Znth (k + 1) states [])) ∧
  Forall (fun x => x = 0) (Znth (Zlength states - 1) states [])

def Pre (a : List Int) : Prop :=
  (1 ≤ Zlength a ∧ Zlength a ≤ 100000) ∧ Forall (fun x => 0 ≤ x ∧ x ≤ 1000000000) a

def Spec (a : List Int) (out : Int) : Prop :=
  min_value_of_subset (· ≤ ·) (SnapTrace a) (fun states => Zlength states - 1) out

end Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe.lean
