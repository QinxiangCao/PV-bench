import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import AUXLib.ZParity
import ListLib.General.Length

namespace Codeforces.examples_shard01.P022_705B_spider_man.lean

open AUXLib

def SplitMove (a b : List Int) : Prop :=
  ∃ i p x, (0 ≤ i ∧ i < Zlength a) ∧ x = Znth i a 0 ∧ (1 ≤ p ∧ p < x) ∧
    List.Perm b (p :: (x - p) :: sublist 0 i a ++ sublist (i + 1) (Zlength a) a)

def SplitPlay (init : List Int) (p : List (List Int)) : Prop :=
  p ≠ [] ∧ Znth 0 p [] = init ∧
    (∀ i, (0 ≤ i ∧ i < Zlength p - 1) → SplitMove (Znth i p []) (Znth (i+1) p [])) ∧
    Forall (fun x => x = 1) (Znth (Zlength p-1) p []) ∧
    (∀ i, (0 ≤ i ∧ i < Zlength p-1) → ∃ x, x ∈ Znth i p [] ∧ x ≥ 2)

def SplitFirstFollows (f : List (List Int) → List Int) (p : List (List Int)) : Prop :=
  ∀ i, (0 ≤ i ∧ i < Zlength p-1) → Z.even i = true → Znth (i+1) p [] = f (sublist 0 (i+1) p)

def SplitFirstWins (a : List Int) : Prop :=
  ∃ f, (∀ hist, hist ≠ [] → (∃ x, x ∈ Znth (Zlength hist-1) hist [] ∧ x ≥ 2) →
    SplitMove (Znth (Zlength hist-1) hist []) (f hist)) ∧
    ∀ p, SplitPlay a p → SplitFirstFollows f p → Z.even (Zlength p) = true

def Pre (added : List Int) : Prop := True

def Spec (added out : List Int) : Prop :=
  Zlength out = Zlength added ∧ ∀ i, (0 ≤ i ∧ i < Zlength added) →
    ((Znth i out 0 = 1 ∧ SplitFirstWins (sublist 0 (i+1) added)) ∨
      (Znth i out 0 = 2 ∧ ¬ SplitFirstWins (sublist 0 (i+1) added)))

end Codeforces.examples_shard01.P022_705B_spider_man.lean
