import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

namespace Algorithms.zero_one_knapsack.lean

open AUXLib MaxMinLib

def KnapsackInputsBounded (weights values : List Int) (item_count capacity : Int) : Prop :=
  Zlength weights = item_count ∧ Zlength values = item_count ∧
  (∀ k : Int, (0 ≤ k ∧ k < item_count) → (1 ≤ Znth k weights 0 ∧ Znth k weights 0 ≤ capacity + 1)) ∧
  (∀ k : Int, (0 ≤ k ∧ k < item_count) → (0 ≤ Znth k values 0 ∧ Znth k values 0 ≤ 10000))

def KnapsackTableValuesBounded (dp : List Int) : Prop :=
  ∀ k : Int, (0 ≤ k ∧ k < Zlength dp) → (0 ≤ Znth k dp 0 ∧ Znth k dp 0 ≤ 4000000)

def KnapsackTablePrefixShape (dp : List Int) (written : Int) : Prop := 0 ≤ written ∧ Zlength dp = written

def KnapsackPlanWeight (weights picks : List Int) (weight : Int) : Prop :=
  weight = sum (picks.map (fun i => Znth i weights 0))

def KnapsackPlanValue (weights values picks : List Int) (value : Int) : Prop :=
  Zlength weights = Zlength values ∧ value = sum (picks.map (fun i => Znth i values 0))

def KnapsackPlan (weights values : List Int) (item_count cap value : Int) : Prop :=
  (0 ≤ item_count ∧ item_count ≤ Zlength weights) ∧ Zlength weights = Zlength values ∧ 0 ≤ cap ∧
  ∃ (picks : List Int) (weight : Int), NoDup picks ∧
    Forall (fun i => 0 ≤ i ∧ i < item_count) picks ∧ KnapsackPlanWeight weights picks weight ∧
    weight ≤ cap ∧ KnapsackPlanValue weights values picks value

def KnapsackMaxValue (weights values : List Int) (item_count cap answer : Int) : Prop :=
  MaxMinLib.max_value_of_subset (· ≤ ·) (fun value => KnapsackPlan weights values item_count cap value)
    (fun value => value) answer

def KnapsackCellCorrect (weights values : List Int) (row col value : Int) : Prop :=
  KnapsackMaxValue weights values row col value

def KnapsackCellIndex (capacity row col : Int) : Int := row * (capacity + 1) + col

def KnapsackTablePrefix (weights values : List Int) (capacity : Int) (dp : List Int) (written : Int) : Prop :=
  ∀ row col : Int, 0 ≤ row → (0 ≤ col ∧ col ≤ capacity) →
    (0 ≤ KnapsackCellIndex capacity row col ∧ KnapsackCellIndex capacity row col < written) →
    KnapsackCellCorrect weights values row col (Znth (KnapsackCellIndex capacity row col) dp 0)

def KnapsackRowsDone (weights values : List Int) (capacity : Int) (dp : List Int) (rows_done : Int) : Prop :=
  KnapsackTablePrefix weights values capacity dp (rows_done * (capacity + 1))

def KnapsackResultState (weights values : List Int) (item_count capacity : Int) (dp : List Int) (answer : Int) : Prop :=
  KnapsackMaxValue weights values item_count capacity answer ∧ (0 ≤ answer ∧ answer ≤ 4000000) ∧
  KnapsackTablePrefixShape dp ((item_count + 1) * (capacity + 1)) ∧ KnapsackTableValuesBounded dp ∧
  KnapsackRowsDone weights values capacity dp (item_count + 1)

end Algorithms.zero_one_knapsack.lean
