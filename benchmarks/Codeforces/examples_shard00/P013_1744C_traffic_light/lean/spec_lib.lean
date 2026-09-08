import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import MaxMinLib.Interface

namespace Codeforces.examples_shard00.P013_1744C_traffic_light.lean

open AUXLib
open MaxMinLib

def WaitsUntilGreen (s : List Int) (start wait : Int) : Prop :=
  (0 ≤ start ∧ start < Zlength s) ∧
  min_value_of_subset (· ≤ ·) (fun candidate : Int => (0 ≤ candidate ∧ candidate < Zlength s) ∧
    Znth (Z.modulo (start + candidate) (Zlength s)) s 0 = 103) (fun candidate => candidate) wait

def Pre (current : Int) (s : List Int) : Prop :=
  (1 ≤ Zlength s ∧ Zlength s ≤ 200000) ∧ (current = 114 ∨ current = 121 ∨ current = 103) ∧
  Forall (fun c => c = 114 ∨ c = 121 ∨ c = 103) s ∧ 103 ∈ s ∧ current ∈ s

def Spec (current : Int) (s : List Int) (out : Int) : Prop :=
  max_value_of_subset (· ≤ ·) (fun candidate : Int × Int => Znth candidate.1 s 0 = current ∧
    WaitsUntilGreen s candidate.1 candidate.2) Prod.snd out

end Codeforces.examples_shard00.P013_1744C_traffic_light.lean
