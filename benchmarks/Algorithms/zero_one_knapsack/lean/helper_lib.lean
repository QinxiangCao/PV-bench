import Algorithms.zero_one_knapsack.lean.spec_lib

namespace Algorithms.zero_one_knapsack.lean

open AUXLib MaxMinLib

def KnapsackStaticSafety (weights values : List Int) (item_count capacity width : Int) : Prop :=
  (0 ≤ item_count ∧ item_count ≤ 300) ∧ (0 ≤ capacity ∧ capacity ≤ 300) ∧
  width = capacity + 1 ∧ (1 ≤ width ∧ width ≤ 301) ∧ KnapsackInputsBounded weights values item_count capacity

def KnapsackRowProgress (weights values : List Int) (capacity : Int) (dp : List Int) (row col : Int) : Prop :=
  KnapsackTablePrefix weights values capacity dp (row * (capacity + 1) + col)

def KnapsackRowsAnnotationState (weights values : List Int) (item_count capacity width : Int)
    (dp : List Int) (rows_done : Int) : Prop :=
  KnapsackStaticSafety weights values item_count capacity width ∧
  (0 ≤ rows_done ∧ rows_done ≤ item_count + 1) ∧
  (0 ≤ rows_done * width ∧ rows_done * width ≤ (item_count + 1) * (capacity + 1)) ∧
  KnapsackTablePrefixShape dp (rows_done * width) ∧ KnapsackTableValuesBounded dp ∧
  KnapsackRowsDone weights values capacity dp rows_done

def KnapsackRowAnnotationState (weights values : List Int) (item_count capacity width : Int)
    (dp : List Int) (row col : Int) : Prop :=
  KnapsackStaticSafety weights values item_count capacity width ∧ (0 ≤ row ∧ row ≤ item_count) ∧
  (0 ≤ col ∧ col ≤ capacity + 1) ∧
  (0 ≤ row * width + col ∧ row * width + col ≤ (item_count + 1) * (capacity + 1)) ∧
  KnapsackTablePrefixShape dp (row * width + col) ∧ KnapsackTableValuesBounded dp ∧
  KnapsackRowProgress weights values capacity dp row col

end Algorithms.zero_one_knapsack.lean
