import Algorithms.rmq.lean.spec_lib

namespace Algorithms.rmq.lean

open AUXLib MaxMinLib

def RMQInputValues (l : List Int) (n : Int) : Prop :=
  Zlength l = n ∧ ∀ i, (0 ≤ i ∧ i < n) → (-2147483648 ≤ Znth i l 0 ∧ Znth i l 0 ≤ 2147483647)

def STCellBounds (st_ls : List Int) (K i j : Int) : Prop :=
  0 < K ∧ 0 ≤ i ∧ 0 ≤ j ∧ j < K ∧ (0 ≤ i * K + j ∧ i * K + j < Zlength st_ls)

def STZeroPrefixBounds (st_ls : List Int) (upto : Int) : Prop := 0 ≤ upto ∧ upto ≤ Zlength st_ls

def STBasePrefixBounds (n upto : Int) : Prop := 0 ≤ upto ∧ upto ≤ n

def STLevelPrefixBounds (K n j upto : Int) : Prop := 0 ≤ j ∧ j < K ∧ 0 ≤ upto ∧ upto ≤ n

def STZeroPrefix (st_ls : List Int) (upto : Int) : Prop :=
  ∀ p, (0 ≤ p ∧ p < upto) → Znth p st_ls 0 = 0

def STBasePrefix (l st_ls : List Int) (K n upto : Int) : Prop :=
  ∀ i, (0 ≤ i ∧ i < upto) → STCellRangeMax l st_ls K i 0

def STLevelPrefix (l st_ls : List Int) (K n j upto : Int) : Prop :=
  ∀ i, (0 ≤ i ∧ i < upto ∧ i + Power2 j ≤ n) → STCellRangeMax l st_ls K i j

def QueryLogBounds (K n len k pow : Int) : Prop :=
  1 ≤ len ∧ len ≤ n ∧ 1 ≤ K ∧ n < Power2 K ∧ 0 ≤ k ∧ k < K ∧ 1 ≤ pow

def QueryLogLoopState (len k pow : Int) : Prop := 0 ≤ k ∧ pow = Power2 k ∧ Power2 k ≤ len

def QueryLogFinalState (len k pow : Int) : Prop := QueryLogLoopState len k pow ∧ len < Power2 (k + 1)

end Algorithms.rmq.lean
