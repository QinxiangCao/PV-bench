import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import MaxMinLib.Interface

namespace Codeforces.examples_shard01.P021_602A_two_bases.lean

open AUXLib

def numeral (base : Int) (digits : List Int) : Int :=
  digits.foldl (fun acc d => acc * base + d) 0

def Pre (bx basey : Int) (x y : List Int) : Prop :=
  bx ≠ basey ∧ Znth 0 x 0 ≠ 0 ∧ Znth 0 y 0 ≠ 0

def Spec (bx basey : Int) (x y : List Int) (out : Int) : Prop :=
  (out = 60 ∧ numeral bx x < numeral basey y) ∨
  (out = 62 ∧ numeral bx x > numeral basey y) ∨
  (out = 61 ∧ numeral bx x = numeral basey y)

end Codeforces.examples_shard01.P021_602A_two_bases.lean
