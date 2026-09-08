import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import MaxMinLib.Interface

namespace Codeforces.examples_shard00.P008_1537B_bad_boy.lean

open AUXLib
open MaxMinLib

abbrev fst {A : Type u} {B : Type v} (p : A × B) : A := p.1

abbrev snd {A : Type u} {B : Type v} (p : A × B) : B := p.2

def Manhattan (p q : Int × Int) : Int := Z.abs (p.1 - q.1) + Z.abs (p.2 - q.2)

def RoundTripThroughTwo (start p q : Int × Int) : Int :=
  Manhattan start p + Manhattan p q + Manhattan q start

def InRoom (n m : Int) (p : Int × Int) : Prop :=
  (1 ≤ p.1 ∧ p.1 ≤ n) ∧ (1 ≤ p.2 ∧ p.2 ≤ m)

def Pre (n m : Int) (start : Int × Int) : Prop :=
  (1 ≤ n ∧ n ≤ 1000000000) ∧ (1 ≤ m ∧ m ≤ 1000000000) ∧ InRoom n m start

def Spec (n m : Int) (start p q : Int × Int) : Prop :=
  MaxMinLib.max_value_of_subset (· ≤ ·)
    (fun candidate : (Int × Int) × (Int × Int) => InRoom n m candidate.1 ∧ InRoom n m candidate.2)
    (fun candidate => RoundTripThroughTwo start candidate.1 candidate.2)
    (RoundTripThroughTwo start p q) ∧ InRoom n m p ∧ InRoom n m q

end Codeforces.examples_shard00.P008_1537B_bad_boy.lean
