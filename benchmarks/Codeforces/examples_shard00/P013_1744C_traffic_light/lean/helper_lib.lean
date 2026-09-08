import Codeforces.examples_shard00.P013_1744C_traffic_light.lean.spec_lib

namespace Codeforces.examples_shard00.P013_1744C_traffic_light.lean

open AUXLib
open MaxMinLib

def DoubledTrafficChar (s : List Int) (index : Int) : Int := Znth (Z.modulo index (Zlength s)) s 0

def FirstProcessedGreen (s : List Int) (i next : Int) : Prop :=
  (next = -1 ∧ ∀ j, (i < j ∧ j < 2 * Zlength s) → DoubledTrafficChar s j ≠ 103) ∨
  ((i < next ∧ next < 2 * Zlength s) ∧ DoubledTrafficChar s next = 103 ∧
    ∀ j, (i < j ∧ j < next) → DoubledTrafficChar s j ≠ 103)

def ProcessedTrafficMaximum (current : Int) (s : List Int) (i ans : Int) : Prop :=
  max_value_of_subset_with_default (· ≤ ·)
    (fun candidate : Int × Int => i < candidate.1 ∧ Znth candidate.1 s 0 = current ∧
      WaitsUntilGreen s candidate.1 candidate.2) Prod.snd 0 ans

def TrafficScanState (current : Int) (s : List Int) (i ans next : Int) : Prop :=
  FirstProcessedGreen s i next ∧ ProcessedTrafficMaximum current s i ans

end Codeforces.examples_shard00.P013_1744C_traffic_light.lean
