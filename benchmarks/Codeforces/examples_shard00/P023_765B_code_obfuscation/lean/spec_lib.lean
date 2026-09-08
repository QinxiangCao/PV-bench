import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import MaxMinLib.Interface

namespace Codeforces.examples_shard00.P023_765B_code_obfuscation.lean

open AUXLib
open MaxMinLib

def FirstOccurrence (s : List Int) (c i : Int) : Prop :=
  min_value_of_subset (· ≤ ·) (fun candidate : Int => (0 ≤ candidate ∧ candidate < Zlength s) ∧ Znth candidate s 0 = c)
    (fun candidate => candidate) i

def ValidObfuscatedNames (s : List Int) : Prop :=
  Forall (fun c => 97 ≤ c ∧ c ≤ 122) s ∧ ∀ c d j,
    97 ≤ c → c < d → d ≤ 122 → FirstOccurrence s d j → ∃ i, FirstOccurrence s c i ∧ i < j

def Pre (s : List Int) : Prop :=
  (1 ≤ Zlength s ∧ Zlength s ≤ 500) ∧ Forall (fun c => 97 ≤ c ∧ c ≤ 122) s

def Spec (s : List Int) (out : Int) : Prop :=
  (out = 0 ∨ out = 1) ∧ (out = 1 ↔ ValidObfuscatedNames s)

end Codeforces.examples_shard00.P023_765B_code_obfuscation.lean
