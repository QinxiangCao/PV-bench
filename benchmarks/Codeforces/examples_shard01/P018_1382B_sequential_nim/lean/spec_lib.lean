import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ZParity
import AUXLib.ListLib.LengthCompat
import MaxMinLib.Interface

namespace Codeforces.examples_shard01.P018_1382B_sequential_nim.lean

open AUXLib

def LeadingOnes (piles : List Int) (k : Int) : Prop :=
  (0 ≤ k ∧ k ≤ Zlength piles) ∧
  (∀ i : Int, (0 ≤ i ∧ i < k) → Znth i piles 0 = 1) ∧
  (k = Zlength piles ∨ Znth k piles 0 ≠ 1)

def FirstWins (piles : List Int) : Prop :=
  ∃ k, LeadingOnes piles k ∧
    ((k = Zlength piles ∧ Z.even k = false) ∨ (k < Zlength piles ∧ Z.even k = true))

def Pre (piles : List Int) : Prop := True

def Spec (piles : List Int) (out : Int) : Prop :=
  (out = 1 ∧ FirstWins piles) ∨ (out = 0 ∧ ¬ FirstWins piles)

def SolverReturnBridge (out ret : Int) : Prop :=
  (out = 1 ∧ ret = 1) ∨ (out = 0 ∧ ret = 0)

end Codeforces.examples_shard01.P018_1382B_sequential_nim.lean
