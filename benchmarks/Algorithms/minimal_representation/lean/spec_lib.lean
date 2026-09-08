import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic

namespace Algorithms.minimal_representation.lean

open AUXLib

def MRRotation (l : List Int) (start : Int) : List Int :=
  sublist start (start + Zlength l) (l ++ l)

def MRValidStart (l : List Int) (start : Int) : Prop := 0 ≤ start ∧ start < Zlength l

def MRRotationValue (l : List Int) (start offset : Int) : Int := Znth (start + offset) (l ++ l) 0

def MRRotationPrefixEq (l : List Int) (left right prefix_len : Int) : Prop :=
  ∀ offset, (0 ≤ offset ∧ offset < prefix_len) →
    MRRotationValue l left offset = MRRotationValue l right offset

def MRRotationEq (l : List Int) (left right : Int) : Prop :=
  MRRotationPrefixEq l left right (Zlength l)

def MRRotationLt (l : List Int) (left right : Int) : Prop :=
  ∃ first_diff, (0 ≤ first_diff ∧ first_diff < Zlength l) ∧
    MRRotationPrefixEq l left right first_diff ∧
    MRRotationValue l left first_diff < MRRotationValue l right first_diff

def MRRotationLe (l : List Int) (left right : Int) : Prop :=
  MRRotationLt l left right ∨ MRRotationEq l left right

def MRMinimalRotationAt (l : List Int) (start : Int) : Prop :=
  MRValidStart l start ∧ ∀ other, MRValidStart l other → MRRotationLe l start other

def MRFirstMinimalRotationAt (l : List Int) (start : Int) : Prop :=
  MRMinimalRotationAt l start ∧
    ∀ other, MRValidStart l other → MRRotationEq l start other → start ≤ other

end Algorithms.minimal_representation.lean
