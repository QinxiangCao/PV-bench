import Codeforces.examples_shard01.P018_1382B_sequential_nim.lean.spec_lib
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ZParity
import AUXLib.ListLib.LengthCompat
import MaxMinLib.Interface

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace Codeforces.examples_shard01.P018_1382B_sequential_nim.lean.groundtruth.proof_lib

open Codeforces.examples_shard01.P018_1382B_sequential_nim.lean
open scoped SimpleC

open AUXLib

theorem leading_ones_unique__return_semantics (piles : List Int) (k1 k2 : Int)
    (h1 : LeadingOnes piles k1) (h2 : LeadingOnes piles k2) : k1 = k2 := by
  rcases h1 with ⟨⟨h10, h1n⟩, hp1, he1⟩
  rcases h2 with ⟨⟨h20, h2n⟩, hp2, he2⟩
  by_cases hlt : k1 < k2
  · have hp := hp2 k1 ⟨h10, hlt⟩
    rcases he1 with he1 | he1
    · omega
    · exact False.elim (he1 hp)
  · by_cases hgt : k2 < k1
    · have hp := hp1 k2 ⟨h20, hgt⟩
      rcases he2 with he2 | he2
      · omega
      · exact False.elim (he2 hp)
    · omega

theorem even_of_nonnegative_rem_zero__return_semantics (n : Int)
    (hn : 0 ≤ n) (hr : Z.rem n 2 = 0) : Z.even n = true := by
  apply (Z.even_spec n).mpr
  rcases (Z.rem_divide n 2 (by decide)).mp hr with ⟨k, hk⟩
  exact ⟨k, by omega⟩

theorem odd_of_nonnegative_rem_nonzero__return_semantics (n : Int)
    (hn : 0 ≤ n) (hr : Z.rem n 2 ≠ 0) : Z.even n = false := by
  cases he : Z.even n with
  | false => rfl
  | true =>
    rcases (Z.even_spec n).mp he with ⟨k, hk⟩
    exact False.elim (hr ((Z.rem_divide n 2 (by decide)).mpr ⟨k, by omega⟩))

theorem even_of_nonnegative_rem_not_one__return_semantics (n : Int)
    (hn : 0 ≤ n) (hr : Z.rem n 2 ≠ 1) : Z.even n = true := by
  have hb := AUXLib.rem_nonneg_bounds n 2 hn (by omega)
  exact even_of_nonnegative_rem_zero__return_semantics n hn (by omega)

end Codeforces.examples_shard01.P018_1382B_sequential_nim.lean.groundtruth.proof_lib

