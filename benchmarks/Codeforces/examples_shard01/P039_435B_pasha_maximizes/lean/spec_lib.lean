import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import ListLib.General.Presuffix

namespace Codeforces.examples_shard01.P039_435B_pasha_maximizes.lean

open AUXLib

def AdjacentSwap (a b : List Int) : Prop :=
  ∃ i, (0 ≤ i ∧ i < Zlength a - 1) ∧ b = replace_Znth (i+1) (Znth i a 0) (replace_Znth i (Znth (i+1) a 0) a)

def SwapReach (a b : List Int) (k : Int) : Prop :=
  ∃ st : List (List Int), (1 ≤ Zlength st ∧ Zlength st ≤ k + 1) ∧ Znth 0 st [] = a ∧
    Znth (Zlength st - 1) st [] = b ∧ ∀ i, (0 ≤ i ∧ i < Zlength st - 1) → AdjacentSwap (Znth i st []) (Znth (i+1) st [])

def Pre (digits : List Int) (k : Int) : Prop := True

def Spec (digits : List Int) (k : Int) (out : List Int) : Prop :=
  SwapReach digits out k ∧ ∀ q, SwapReach digits q k →
    (q = out ∨ ((∃ i, (0 ≤ i ∧ i < min (Zlength q) (Zlength out)) ∧
      (∀ j, (0 ≤ j ∧ j < i) → Znth j q 0 = Znth j out 0) ∧ Znth i q 0 < Znth i out 0) ∨
      (Zlength q < Zlength out ∧ ListLib.is_prefix q out)))

end Codeforces.examples_shard01.P039_435B_pasha_maximizes.lean
