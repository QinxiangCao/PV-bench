import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import ListLib.General.Length

namespace Codeforces.examples_shard01.P040_81A_plug_in.lean

open AUXLib

def DeletePair (a b : List Int) : Prop :=
  ∃ i : Int, (0 ≤ i ∧ i < Zlength a - 1) ∧ Znth i a 0 = Znth (i + 1) a 0 ∧
    b = sublist 0 i a ++ sublist (i + 2) (Zlength a) a

def ReducedFrom (a b : List Int) : Prop :=
  ∃ st : List (List Int), st ≠ [] ∧ Znth 0 st [] = a ∧ Znth (Zlength st - 1) st [] = b ∧
    (∀ i : Int, (0 ≤ i ∧ i < Zlength st - 1) → DeletePair (Znth i st []) (Znth (i + 1) st [])) ∧
    ¬ ∃ q, DeletePair b q

def Pre (s : List Int) : Prop := True

def Spec (s out : List Int) : Prop := ReducedFrom s out

end Codeforces.examples_shard01.P040_81A_plug_in.lean
