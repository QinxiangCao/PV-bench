import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

namespace Codeforces.examples_shard01.P044_837C_two_seals.lean

open AUXLib

open MaxMinLib

-- Names used by QCP when printing pairs in annotations.
abbrev _Prod_Z_Z := Int × Int
abbrev fst {A B : Type} (p : A × B) : A := p.1
abbrev snd {A B : Type} (p : A × B) : B := p.2

def Oriented (s o : Int × Int) : Prop := o = s ∨ o = (s.2,s.1)

def TwoFit (a b : Int) (x y : Int × Int) : Prop :=
  (x.1 + y.1 ≤ a ∧ max x.2 y.2 ≤ b) ∨ (max x.1 y.1 ≤ a ∧ x.2 + y.2 ≤ b)

def SealArea (paper : Int × Int) (seals : List (Int × Int)) (v : Int) : Prop :=
  v = 0 ∨ ∃ i j x y, (0 ≤ i ∧ i < j) ∧ j < Zlength seals ∧
    Oriented (Znth i seals (0,0)) x ∧ Oriented (Znth j seals (0,0)) y ∧
    TwoFit paper.1 paper.2 x y ∧ v = x.1 * x.2 + y.1 * y.2

def Pre (paper : Int × Int) (seals : List (Int × Int)) : Prop := True

def Spec (paper : Int × Int) (seals : List (Int × Int)) (out : Int) : Prop :=
  max_value_of_subset (· ≤ ·) (SealArea paper seals) (fun x => x) out

end Codeforces.examples_shard01.P044_837C_two_seals.lean
