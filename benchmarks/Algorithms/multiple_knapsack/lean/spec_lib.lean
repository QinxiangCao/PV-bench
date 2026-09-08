import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

namespace Algorithms.multiple_knapsack.lean

open AUXLib MaxMinLib

def PairwiseWeightValue (xs : List (Int × Int)) : Int :=
  sum (List.map (fun wp => Prod.fst wp * Prod.snd wp) xs)

def PickWeight (weights picks : List Int) : Int :=
  PairwiseWeightValue (List.zip weights picks)

def PickValue (values picks : List Int) : Int :=
  PairwiseWeightValue (List.zip values picks)

def BoundedPickList
    (weights values counts : List Int) (capacity : Int) (picks : List Int) : Prop :=
  Zlength weights = Zlength values ∧
  Zlength weights = Zlength counts ∧
  Zlength picks = Zlength weights ∧
  0 ≤ capacity ∧
  List.Forall₂ (fun pick cnt => (0 ≤ pick ∧ pick ≤ cnt) ) picks counts ∧
  0 ≤ PickWeight weights picks ∧
  PickWeight weights picks ≤ capacity

def MultipleKnapsackAnswer
    (weights values counts : List Int) (capacity answer : Int) : Prop :=
  max_value_of_subset (· ≤ ·)
    (fun picks => BoundedPickList weights values counts capacity picks)
    (fun picks => PickValue values picks)
    answer

def MultipleKnapsackPrefixAnswer
    (weights values counts : List Int) (i capacity answer : Int) : Prop :=
  max_value_of_subset (· ≤ ·)
    (fun picks =>
       BoundedPickList
         (sublist 0 i weights)
         (sublist 0 i values)
         (sublist 0 i counts)
         capacity
         picks)
    (fun picks => PickValue (sublist 0 i values) picks)
    answer

def MKScratchArraysSafety
    (old q_idx q_val : List Int) (capacity : Int) : Prop :=
  Zlength old = capacity + 1 ∧
  Zlength q_idx = capacity + 1 ∧
  Zlength q_val = capacity + 1

def MKDPTableSafety
    (weights : List Int) (i capacity : Int) (dp : List Int) : Prop :=
  (0 ≤ i ∧ i ≤ Zlength weights) ∧
  0 ≤ capacity ∧
  Zlength dp = capacity + 1

def MKDPTableSemantics
    (weights values counts : List Int) (i capacity : Int) (dp : List Int) : Prop :=
  forall cap,
    (0 ≤ cap ∧ cap ≤ capacity) →
    MultipleKnapsackPrefixAnswer weights values counts i cap (Znth cap dp 0)

end Algorithms.multiple_knapsack.lean
