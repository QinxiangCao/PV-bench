import SimpleC.SL.SeparationLogic
import SimpleC.SL.CArch
import AUXLib.ListLib.LengthCompat

namespace Engineering.minisat.vec.lean

open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion SimpleC.SL.SeparationLogic

open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig

open scoped SimpleC SimpleC.SL.SAC

local instance : SacContext := ⟨naive_C_Rules⟩

export SimpleC.SL.CArch.Arch32 (ptr_size ptr_size_Z addr_max_unsigned)

private noncomputable abbrev intArray := naive_C_Rules.IntArray

private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

def vec_alloc_ok (stride cap : Int) : Prop :=
  0 < stride ∧ 0 ≤ cap ∧ (0 ≤ cap * stride ∧ cap * stride ≤ Int.max_unsigned)

def vec_growth_ok (stride cap : Int) : Prop :=
  0 < stride ∧ 0 ≤ cap ∧ 2 * cap ≤ Int.max_signed ∧
  2 * cap + 1 ≤ Int.max_signed ∧
  (0 ≤ (2 * cap + 1) * stride ∧ (2 * cap + 1) * stride ≤ Int.max_unsigned) ∧
  (2 * cap + 1) * stride ≤ addr_max_unsigned + 1

def vec_push_result (len oldbuf oldcap newbuf newcap : Int) : Prop :=
  (len < oldcap ∧ newbuf = oldbuf ∧ newcap = oldcap) ∨
  (len = oldcap ∧ newcap = 2 * oldcap + 1)

noncomputable def veci_buffer (buf : addr) (xs : List Int) (cap : Int) : Assertion :=
  intArray.full buf (Zlength xs) xs ** intArray.undef_seg buf (Zlength xs) cap

noncomputable def veci_header (v : addr) (len cap : Int) (buf : addr) : Assertion :=
  ((&((v # "veci_t") ->ₛ "size")) # INT |-> len) **
  ((&((v # "veci_t") ->ₛ "cap")) # INT |-> cap) **
  ((&((v # "veci_t") ->ₛ "ptr")) # PTR |-> buf)

noncomputable def veci_raw (v buf : addr) (cap : Int) (xs : List Int) : Assertion :=
  “ v ≠ 0 ∧ buf ≠ 0 ∧ 0 ≤ Zlength xs ∧ Zlength xs ≤ cap ∧
    4 ≤ cap ∧ cap ≤ Int.max_signed ∧ vec_alloc_ok (sizeof(INT)) cap ” &&
  (veci_header v (Zlength xs) cap buf ** veci_buffer buf xs cap)

noncomputable def store_veci (v : addr) (xs : List Int) : Assertion :=
  EX buf : addr, EX cap : Int, veci_raw v buf cap xs

noncomputable def veci_shell (v : addr) : Assertion :=
  “ v ≠ 0 ” &&
  (((&((v # "veci_t") ->ₛ "size")) # INT |->_) **
   ((&((v # "veci_t") ->ₛ "cap")) # INT |->_) **
   ((&((v # "veci_t") ->ₛ "ptr")) # PTR |->_))

noncomputable def vecp_buffer (buf : addr) (xs : List Int) (cap : Int) : Assertion :=
  ptrArray.full buf (Zlength xs) xs ** ptrArray.undef_seg buf (Zlength xs) cap

noncomputable def vecp_header (v : addr) (len cap : Int) (buf : addr) : Assertion :=
  ((&((v # "vecp_t") ->ₛ "size")) # INT |-> len) **
  ((&((v # "vecp_t") ->ₛ "cap")) # INT |-> cap) **
  ((&((v # "vecp_t") ->ₛ "ptr")) # PTR |-> buf)

noncomputable def vecp_raw (v buf : addr) (cap : Int) (xs : List Int) : Assertion :=
  “ v ≠ 0 ∧ buf ≠ 0 ∧ 0 ≤ Zlength xs ∧ Zlength xs ≤ cap ∧
    4 ≤ cap ∧ cap ≤ Int.max_signed ∧ vec_alloc_ok ptr_size_Z cap ” &&
  (vecp_header v (Zlength xs) cap buf ** vecp_buffer buf xs cap)

noncomputable def store_vecp (v : addr) (xs : List Int) : Assertion :=
  EX buf : addr, EX cap : Int, vecp_raw v buf cap xs

noncomputable def vecp_shell (v : addr) : Assertion :=
  “ v ≠ 0 ” &&
  (((&((v # "vecp_t") ->ₛ "size")) # INT |->_) **
   ((&((v # "vecp_t") ->ₛ "cap")) # INT |->_) **
   ((&((v # "vecp_t") ->ₛ "ptr")) # PTR |->_))

end Engineering.minisat.vec.lean
