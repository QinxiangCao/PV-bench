import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

namespace Codeforces.examples_shard01.P005_707A_brains_photos.lean

open AUXLib

-- QCP names the nested-list element type and Coq list concatenation here.
abbrev _List_Z := List Int
abbrev concat {A : Type u} (rows : List (List A)) : List A := rows.flatten

def Pixel (c : Int) : Prop := c = 67 ∨ c = 77 ∨ c = 89 ∨ c = 87 ∨ c = 71 ∨ c = 66

def Pre (photo : List (List Int)) : Prop := True

def HasColor (photo : List (List Int)) : Prop :=
  ∃ row c, row ∈ photo ∧ c ∈ row ∧ (c = 67 ∨ c = 77 ∨ c = 89)

def Spec (photo : List (List Int)) (out : Bool) : Prop :=
  (out = true ∧ HasColor photo) ∨ (out = false ∧ ¬ HasColor photo)

def SolverReturnBridge (out : Bool) (ret : Int) : Prop :=
  (out = true ∧ ret = 1) ∨ (out = false ∧ ret = 0)

end Codeforces.examples_shard01.P005_707A_brains_photos.lean
