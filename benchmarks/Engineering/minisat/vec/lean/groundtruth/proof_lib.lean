import Engineering.minisat.vec.lean.spec_lib
import SimpleC.SL.SeparationLogic
import SimpleC.SL.CArch
import AUXLib.ListLib.LengthCompat

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace Engineering.minisat.vec.lean.groundtruth.proof_lib

open Engineering.minisat.vec.lean
open scoped SimpleC

open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion SimpleC.SL.SeparationLogic
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
export SimpleC.SL.CArch.Arch32 (ptr_size ptr_size_Z addr_max_unsigned)
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

theorem veci_buffer_truncate__resize_prefix (buf : addr) (xs : List Int) (cap k : Int)
    (hk : 0 ≤ k ∧ k ≤ Zlength xs) (hc : Zlength xs ≤ cap) :
    intArray.full buf (Zlength xs) xs ** intArray.undef_seg buf (Zlength xs) cap |--
    intArray.full buf k (sublist 0 k xs) ** intArray.undef_seg buf k cap := by
  sep_apply (intArray.full_split_to_seg buf k (Zlength xs) xs hk)
  sep_apply (intArray.seg_to_full buf 0 k (sublist 0 k xs))
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  sep_apply (intArray.seg_to_undef_seg buf k (Zlength xs) (sublist k (Zlength xs) xs))
  sep_apply (intArray.undef_seg_merge_to_undef_seg buf k (Zlength xs) cap (by omega))
  cancel

theorem vecp_buffer_truncate__resize_prefix (buf : addr) (xs : List Int) (cap k : Int)
    (hk : 0 ≤ k ∧ k ≤ Zlength xs) (hc : Zlength xs ≤ cap) :
    ptrArray.full buf (Zlength xs) xs ** ptrArray.undef_seg buf (Zlength xs) cap |--
    ptrArray.full buf k (sublist 0 k xs) ** ptrArray.undef_seg buf k cap := by
  sep_apply (ptrArray.full_split_to_seg buf k (Zlength xs) xs hk)
  sep_apply (ptrArray.seg_to_full buf 0 k (sublist 0 k xs))
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  sep_apply (ptrArray.seg_to_undef_seg buf k (Zlength xs) (sublist k (Zlength xs) xs))
  sep_apply (ptrArray.undef_seg_merge_to_undef_seg buf k (Zlength xs) cap (by omega))
  cancel

theorem reassociate_sepcon_7_entail__push_nongrowth {P1 P2 P3 P4 P5 P6 P7 Q : Assertion}
    (h : P1 ** P2 ** P3 ** P4 ** P5 ** P6 ** P7 |-- Q) :
    P1 ** (P2 ** (P3 ** (P4 ** (P5 ** (P6 ** P7))))) |-- Q := by
  sep_apply h
  cancel

theorem vec_push_result_from_branches__push_final (len oldbuf oldcap newbuf newcap : Int)
    (hle : len ≤ oldcap) (hnew : len < newcap)
    (hsame : len < oldcap → newbuf = oldbuf ∧ newcap = oldcap)
    (hgrow : len = oldcap → newcap = 2 * oldcap + 1) :
    vec_push_result len oldbuf oldcap newbuf newcap := by
  by_cases h : len < oldcap
  · exact Or.inl ⟨h, hsame h⟩
  · have he : len = oldcap := by omega
    exact Or.inr ⟨he, hgrow he⟩

end Engineering.minisat.vec.lean.groundtruth.proof_lib

