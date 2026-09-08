import Codeforces.examples_shard01.P073_1799D2_hot_start_up.lean.spec_lib

namespace Codeforces.examples_shard01.P073_1799D2_hot_start_up.lean

open AUXLib

open MaxMinLib

def DP_INF : Int := 4557430888798830399

def OtherCpuLastProgram (prog cpu : List Int) (other : Int) : Prop :=
  0 < Zlength prog ∧ Zlength cpu = Zlength prog ∧
    (let active := Znth (Zlength prog - 1) cpu 0
     (other = 0 ∧ ∀ q, (0 ≤ q ∧ q < Zlength prog) → Znth q cpu 0 = active) ∨
     (∃ q, (0 ≤ q ∧ q < Zlength prog) ∧ Znth q cpu 0 ≠ active ∧ other = Znth q prog 0 ∧
       ∀ r, (q < r ∧ r < Zlength prog) → Znth r cpu 0 = active))

def PrefixStateCost (prog cold hot : List Int) (prefix_len other total : Int) : Prop :=
  ∃ cpu, RunCost (sublist 0 prefix_len prog) cold hot cpu total ∧ OtherCpuLastProgram (sublist 0 prefix_len prog) cpu other

def PrefixStateMinimum (prog cold hot : List Int) (prefix_len other total : Int) : Prop :=
  min_value_of_subset (· ≤ ·) (PrefixStateCost prog cold hot prefix_len other) (fun x => x) total

def NormalizedScheduleCell (prog cold hot : List Int) (prefix_len other off value : Int) : Prop :=
  (value < DP_INF ∧ PrefixStateMinimum prog cold hot prefix_len other (off + value)) ∨
    (value = DP_INF ∧ ¬ ∃ total, PrefixStateCost prog cold hot prefix_len other total)

def NormalizedScheduleState (prog cold hot : List Int) (prefix_len : Int) (dp : List Int) (off mind : Int) : Prop :=
  (∀ other, (0 ≤ other ∧ other ≤ Zlength cold) → NormalizedScheduleCell prog cold hot prefix_len other off (Znth other dp DP_INF)) ∧
    min_value_of_subset (· ≤ ·) (fun value => ∃ other, (0 ≤ other ∧ other ≤ Zlength cold) ∧ value = Znth other dp DP_INF ∧ value < DP_INF) (fun x => x) mind ∧
    Spec (sublist 0 prefix_len prog) cold hot (off + mind)

end Codeforces.examples_shard01.P073_1799D2_hot_start_up.lean
