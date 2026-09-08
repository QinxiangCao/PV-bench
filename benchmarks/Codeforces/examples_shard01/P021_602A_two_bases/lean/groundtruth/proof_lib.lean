import Codeforces.examples_shard01.P021_602A_two_bases.lean.spec_lib
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import MaxMinLib.Interface
import Mathlib.Tactic.IntervalCases

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace Codeforces.examples_shard01.P021_602A_two_bases.lean.groundtruth.proof_lib

open Codeforces.examples_shard01.P021_602A_two_bases.lean
open scoped SimpleC

open AUXLib

theorem numeral_sublist_succ__numeral_arithmetic (b i : Int) (digits : List Int)
    (hi : 0 ≤ i ∧ i < Zlength digits) :
    numeral b (sublist 0 (i + 1) digits) =
      numeral b (sublist 0 i digits) * b + Znth i digits 0 := by
  rw [sublist_split 0 (i + 1) i digits ⟨by omega, hi.1⟩ ⟨by omega, by omega⟩,
    sublist_single 0 i digits hi]
  simp only [numeral, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem pow40_successor_bound__numeral_arithmetic (i v b d : Int)
    (hi : 0 ≤ i) (hv : 0 ≤ v ∧ v ≤ Z.pow 40 i - 1)
    (hb : 2 ≤ b ∧ b ≤ 40) (hd : 0 ≤ d ∧ d < b) :
    v * b + d ≤ Z.pow 40 (i + 1) - 1 := by
  have hpow : Z.pow 40 (i + 1) = Z.pow 40 i * 40 := by
    cases i with
    | ofNat n => change (40 : Int) ^ (n + 1) = (40 : Int) ^ n * 40; exact pow_succ _ _
    | negSucc n => omega
  rw [hpow]
  have hmul := mul_nonneg hv.1 (show 0 ≤ 40 - b by omega)
  nlinarith

theorem pow40_int64_bound__numeral_arithmetic (i : Int) (hi : 0 ≤ i ∧ i ≤ 9) :
    Z.pow 40 (i + 1) - 1 ≤ 9223372036854775807 := by
  rcases hi with ⟨hi0, hi9⟩
  interval_cases i <;> decide

theorem numeral_sublist_full__numeral_endpoints (b : Int) (digits : List Int) :
    numeral b (sublist 0 (Zlength digits) digits) = numeral b digits := by
  rw [sublist_self digits (Zlength digits) rfl]

end Codeforces.examples_shard01.P021_602A_two_bases.lean.groundtruth.proof_lib

