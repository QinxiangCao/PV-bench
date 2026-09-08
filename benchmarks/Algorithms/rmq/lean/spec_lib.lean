import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

namespace Algorithms.rmq.lean

open AUXLib MaxMinLib

def Power2 (j : Int) : Int := Z.pow 2 j

def RMQSizeSafe (n K : Int) : Prop :=
  1 ≤ n ∧ n ≤ 100000 ∧ 1 ≤ K ∧ K ≤ 30 ∧ n * K ≤ 1000000 ∧ n < Power2 K

def STTableShape (st_ls : List Int) (K n : Int) : Prop := Zlength st_ls = n * K

def STBuiltBeforeLevelBounds (K level : Int) : Prop := 0 ≤ level ∧ level ≤ K

def RangeMaxValue (l : List Int) (lo hi ans : Int) : Prop :=
  0 ≤ lo ∧ lo < hi ∧ hi ≤ Zlength l ∧
    max_value_of_subset (· ≤ ·) (fun k => lo ≤ k ∧ k < hi) (fun k => Znth k l 0) ans

def STCellRangeMax (l st_ls : List Int) (K i j : Int) : Prop :=
  RangeMaxValue l i (i + Power2 j) (Znth (i * K + j) st_ls 0)

def STBuiltBeforeLevel (l st_ls : List Int) (K n level : Int) : Prop :=
  ∀ i j, (0 ≤ i ∧ 0 ≤ j ∧ j < level ∧ i + Power2 j ≤ n) → STCellRangeMax l st_ls K i j

def STBuilt (l st_ls : List Int) (K n : Int) : Prop := STBuiltBeforeLevel l st_ls K n K

def QueryIntervalBounds (n left right : Int) : Prop := 0 ≤ left ∧ left ≤ right ∧ right < n

end Algorithms.rmq.lean
