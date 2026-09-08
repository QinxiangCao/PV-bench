import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

namespace Codeforces.examples_shard01.P014_1765E_exchange.lean

open AUXLib

open MaxMinLib

def ExchangeStep (a b : Int) (s1 s2 : Int × Int) : Prop :=
  let (g,x) := s1
  let (g',x') := s2
  (g ≥ 1 ∧ g' = g - 1 ∧ x' = x + a) ∨ (x ≥ b ∧ g' = g + 1 ∧ x' = x - b)

def ReachesSilver (n a b q : Int) : Prop :=
  ∃ states : List (Int × Int),
    states ≠ [] ∧ Znth 0 states (0,0) = (q,0) ∧
    (∀ i, (0 ≤ i ∧ i < Zlength states - 1) →
      ExchangeStep a b (Znth i states (0,0)) (Znth (i+1) states (0,0))) ∧
    (let (g,x) := Znth (Zlength states-1) states (0,0); g ≥ 0 ∧ x ≥ n)

def Pre (n a b : Int) : Prop := True

def Spec (n a b out : Int) : Prop :=
  min_value_of_subset (· ≤ ·) (fun q => q ≥ 0 ∧ ReachesSilver n a b q) (fun x => x) out

end Codeforces.examples_shard01.P014_1765E_exchange.lean
