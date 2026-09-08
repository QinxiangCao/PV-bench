import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import ListLib.General.Presuffix
import AUXLib.ZParity

namespace Codeforces.examples_shard01.P030_1220C_substring_game_in_the_lesson.lean

open AUXLib

def LexLt (a b : List Int) : Prop :=
  (∃ i, (0 ≤ i ∧ i < min (Zlength a) (Zlength b)) ∧
    (∀ j, (0 ≤ j ∧ j < i) → Znth j a 0 = Znth j b 0) ∧ Znth i a 0 < Znth i b 0) ∨
  (Zlength a < Zlength b ∧ ListLib.is_prefix a b)

def IntervalMove (s : List Int) (a b : Int × Int) : Prop :=
  b.1 ≤ a.1 ∧ a.2 ≤ b.2 ∧ (0 ≤ b.1 ∧ b.1 ≤ b.2) ∧ b.2 < Zlength s ∧
    LexLt (sublist b.1 (b.2+1) s) (sublist a.1 (a.2+1) s)

def IntervalPlay (s : List Int) (k : Int) (p : List (Int × Int)) : Prop :=
  p ≠ [] ∧ Znth 0 p (0,0) = (k,k) ∧
    (∀ i, (0 ≤ i ∧ i < Zlength p - 1) → IntervalMove s (Znth i p (0,0)) (Znth (i+1) p (0,0))) ∧
    ¬ ∃ q, IntervalMove s (Znth (Zlength p-1) p (0,0)) q

def AnnFollows (f : List (Int × Int) → Int × Int) (p : List (Int × Int)) : Prop :=
  ∀ i, (0 ≤ i ∧ i < Zlength p - 1) → Z.even i = true → Znth (i+1) p (0,0) = f (sublist 0 (i+1) p)

def AnnWins (s : List Int) (k : Int) : Prop :=
  ∃ f, (∀ hist, hist ≠ [] → (∃ q, IntervalMove s (Znth (Zlength hist-1) hist (0,0)) q) →
    IntervalMove s (Znth (Zlength hist-1) hist (0,0)) (f hist)) ∧
    ∀ p, IntervalPlay s k p → AnnFollows f p → Z.even (Zlength p) = true

def Pre (s : List Int) : Prop := True

def Spec (s : List Int) (out : List Int) : Prop :=
  Zlength out = Zlength s ∧ ∀ k, (0 ≤ k ∧ k < Zlength s) →
    ((Znth k out 0 = 1 ∧ AnnWins s k) ∨ (Znth k out 0 = 0 ∧ ¬ AnnWins s k))

end Codeforces.examples_shard01.P030_1220C_substring_game_in_the_lesson.lean
