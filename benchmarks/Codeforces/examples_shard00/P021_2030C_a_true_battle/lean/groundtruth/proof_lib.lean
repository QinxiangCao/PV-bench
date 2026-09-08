import Codeforces.examples_shard00.P021_2030C_a_true_battle.lean.spec_lib
import Codeforces.examples_shard00.P021_2030C_a_true_battle.lean.helper_lib
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import MaxMinLib.Interface

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace Codeforces.examples_shard00.P021_2030C_a_true_battle.lean.groundtruth.proof_lib

open Codeforces.examples_shard00.P021_2030C_a_true_battle.lean
open scoped SimpleC

open AUXLib

theorem no_adjacent_ones_before_succ__loop_transition (values : List Int) (i : Int)
    (hi : 0 ≤ i) (ho : NoAdjacentOnesBefore values i)
    (hn : Znth i values 0 ≠ 49 ∨ Znth (i + 1) values 0 ≠ 49) :
    NoAdjacentOnesBefore values (i + 1) := by
  intro k hk
  by_cases h : k < i
  · exact ho k ⟨hk.1, h⟩
  · have he : k = i := by omega
    simpa only [he] using hn

theorem spec_zero_from_completed_scan__final_results (values : List Int) (n i : Int)
    (hn : n = Zlength values) (hi0 : 0 ≤ i) (hi1 : i ≤ n - 1) (hi2 : i + 1 ≥ n)
    (hf : Znth 0 values 0 ≠ 49) (hl : Znth (Zlength values - 1) values 0 ≠ 49)
    (hs : NoAdjacentOnesBefore values i) : Spec values 0 := by
  refine ⟨Or.inl rfl, ⟨by intro h; omega, ?_⟩⟩
  rintro (hw | hw | ⟨j, hj0, hjn, hj, hj1⟩)
  · exact False.elim (hf hw)
  · exact False.elim (hl hw)
  · rcases hs j ⟨hj0, by omega⟩ with hh | hh
    · exact False.elim (hh hj)
    · exact False.elim (hh hj1)

end Codeforces.examples_shard00.P021_2030C_a_true_battle.lean.groundtruth.proof_lib
