import AUXLib.Sorting
import SimpleC.SL.SeparationLogic
import AUXLib.Arithmetic
import AUXLib.ListLib.LengthCompat
import AUXLib.Morphisms

namespace Data_structures.priority_queue.lean

open AUXLib AUXLib.Sorting

open SimpleC.SL.CNotation SimpleC.SL.CommonAssertion

open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig

open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic

open scoped SimpleC.SL.SAC

local instance : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev intArray := naive_C_Rules.IntArray

structure multiset (A : Type) where
  Build_multiset ::
  mlist : List A

export multiset (mlist)

@[match_pattern] abbrev Build_multiset (A : Type) (mlist : List A) : multiset A := multiset.Build_multiset mlist

def list_to_multiset {A : Type} (l : List A) : multiset A := ⟨l⟩

def multiset_empty {A : Type} : multiset A := list_to_multiset []

def multiset_size {A : Type} (S : multiset A) : Int := Zlength (mlist S)

def multiset_equiv {A : Type} (S1 S2 : multiset A) : Prop := Permutation (mlist S1) (mlist S2)

def multiset_insert {A : Type} (S : multiset A) (x : A) : multiset A := list_to_multiset (x :: mlist S)

def multiset_union {A : Type} (S1 S2 : multiset A) : multiset A := list_to_multiset (mlist S1 ++ mlist S2)

def multiset_map {A B : Type} (f : A → B) (S : multiset A) : multiset B := list_to_multiset ((mlist S).map f)

def multiset_member_by {A : Type} (eq_dec : DecidableEq A) (S : multiset A) (x : A) : Bool :=
  (mlist S).any (fun y => @ite Bool (x = y) (eq_dec x y) true false)

def multiset_count_by {A : Type} (eq_dec : DecidableEq A) (S : multiset A) (x : A) : Nat :=
  (mlist S).foldr (fun y n => @ite Nat (y = x) (eq_dec y x) (n + 1) n) 0

noncomputable def multiset_remove {A : Type} (S : multiset A) (x : A) : multiset A :=
  list_to_multiset (remove_one (mlist S))
where
  remove_one : List A → List A
    | [] => []
    | y :: ys => @ite (List A) (x = y) (Classical.propDecidable _) ys (y :: remove_one ys)

instance multiset_equiv_Equivalence (A : Type) : AUXLib.Equivalence (@multiset_equiv A) where
  refl _ := List.Perm.refl _
  symm _ _ h := h.symm
  trans _ _ _ h1 h2 := h1.trans h2

def multiset_max (S : multiset Int) : Int :=
  match mlist S with
  | [] => 0
  | x :: xs => xs.foldr max x

def multiset_maximum (S : multiset Int) (value : Int) : Prop :=
  value ∈ mlist S ∧ ∀ x, x ∈ mlist S → x ≤ value

def heap_capacity : Int := 100000

def heap_parent (child : Int) : Int := Z.quot (child - 1) 2

def heap_left_child (index : Int) : Int := index * 2 + 1

def heap_right_child (index : Int) : Int := index * 2 + 2

def heap_selected_child (concrete : List Int) (size index : Int) : Int :=
  let left := heap_left_child index
  let right := heap_right_child index
  if right < size then
    if Znth left concrete 0 < Znth right concrete 0 then right else left
  else left

def heap_ordered (concrete : List Int) (size : Int) : Prop :=
  ∀ child, (0 < child ∧ child < size) → Znth (heap_parent child) concrete 0 ≥ Znth child concrete 0

def heap_relation (S : multiset Int) (concrete : List Int) : Prop := Permutation (mlist S) concrete

def heap_representation (S : multiset Int) (concrete : List Int) (size : Int) : Prop :=
  0 ≤ size ∧ size ≤ heap_capacity ∧ multiset_size S = size ∧ Zlength concrete = size ∧
    heap_relation S concrete ∧ heap_ordered concrete size

noncomputable def store_heap (p : Int) (S : multiset Int) (size : Int) : Assertion :=
  EX concrete : List Int, “ heap_representation S concrete size ” && intArray.full p size concrete

noncomputable def heap_spare (p size : Int) : Assertion := intArray.undef_seg p size (size + 1)

noncomputable def heap_retired_cell (p index value : Int) : Assertion := intArray.seg p index (index + 1) [value]

def PrefixMaximum (concrete : List Int) (size value : Int) : Prop :=
  0 < size ∧ size ≤ Zlength concrete ∧ Znth 0 concrete 0 = value ∧
    ∀ i, (0 ≤ i ∧ i < size) → Znth i concrete 0 ≤ value

def HeapOrderExceptUp (concrete : List Int) (size child : Int) : Prop :=
  0 ≤ child ∧ child < size ∧ ∀ node, (0 < node ∧ node < size ∧ node ≠ child) →
    Znth (heap_parent node) concrete 0 ≥ Znth node concrete 0

def PushHoleChildrenPreserved (concrete : List Int) (size child : Int) : Prop :=
  ∀ node, (0 < node ∧ node < size ∧ heap_parent node = child) →
    Znth (heap_parent child) concrete 0 ≥ Znth node concrete 0

def PushSource (written : List Int) (before : multiset Int) (size x : Int) : Prop :=
  Zlength written = size + 1 ∧ Permutation written (x :: mlist before) ∧
    heap_ordered (sublist 0 size written) size

def PushLoopState (written current : List Int) (size child x : Int) : Prop :=
  0 ≤ size ∧ Zlength written = size + 1 ∧ Zlength current = size + 1 ∧
    0 ≤ child ∧ child ≤ size ∧ Znth child current 0 = x ∧ Permutation written current ∧
    HeapOrderExceptUp current (size + 1) child ∧ PushHoleChildrenPreserved current (size + 1) child

def PushResult (before : multiset Int) (result : List Int) (size x : Int) : Prop :=
  0 ≤ size ∧ Zlength result = size + 1 ∧ Permutation result (x :: mlist before) ∧ heap_ordered result (size + 1)

def BuildPrefixState («prefix» : multiset Int) (input : List Int) (processed : Int) : Prop :=
  1 ≤ processed ∧ processed ≤ Zlength input ∧ multiset_equiv «prefix» (list_to_multiset (sublist 0 processed input))

def HeapOrderExceptDown (concrete : List Int) (size index : Int) : Prop :=
  0 ≤ index ∧ index < size ∧ ∀ child, (0 < child ∧ child < size ∧ heap_parent child ≠ index) →
    Znth (heap_parent child) concrete 0 ≥ Znth child concrete 0

def PopHoleParentDominatesChildren (current : List Int) (size index : Int) : Prop :=
  index = 0 ∨ ∀ child, (0 < child ∧ child < size ∧ heap_parent child = index) →
    Znth (heap_parent index) current 0 ≥ Znth child current 0

def PopSelectedChild (current : List Int) (size index selected : Int) : Prop :=
  0 ≤ index ∧ index < size ∧ index < selected ∧ 0 ≤ selected ∧ selected < size ∧
    heap_parent selected = index ∧ selected = heap_selected_child current size index ∧
    ∀ child, (0 < child ∧ child < size ∧ heap_parent child = index) → Znth selected current 0 ≥ Znth child current 0

def PopRemainingElements (before current : List Int) (size : Int) : Prop :=
  1 ≤ size ∧ size ≤ Zlength before ∧ size ≤ Zlength current ∧
    Permutation (sublist 0 (size - 1) current) (sublist 1 size before)

def PopLoopState (before current : List Int) (size index : Int) : Prop :=
  1 < size ∧ Zlength before = size ∧ Zlength current = size ∧ 0 ≤ index ∧ index < size - 1 ∧
    heap_ordered before size ∧ Znth index current 0 = Znth (size - 1) before 0 ∧
    Znth (size - 1) current 0 = Znth (size - 1) before 0 ∧ PopRemainingElements before current size ∧
    HeapOrderExceptDown current (size - 1) index ∧ PopHoleParentDominatesChildren current (size - 1) index

def PopReadyState (before current : List Int) (size result : Int) : Prop :=
  1 < size ∧ Zlength before = size ∧ Zlength current = size ∧ heap_ordered before size ∧
    PrefixMaximum before size result ∧ Znth (size - 1) current 0 = Znth (size - 1) before 0 ∧
    PopRemainingElements before current size ∧ heap_ordered current (size - 1)

def PopResult (S : multiset Int) (before result : List Int) (size value : Int) : Prop :=
  1 ≤ size ∧ Zlength before = size ∧ Zlength result = size ∧ value = multiset_max S ∧
    heap_ordered (sublist 0 (size - 1) result) (size - 1) ∧
    Permutation (sublist 0 (size - 1) result) (mlist (multiset_remove S value))

def HeapSortState (input : List Int) (active : multiset Int) (suffix : List Int) : Prop :=
  Permutation input (mlist active ++ suffix) ∧ Sorting.increasing suffix ∧
    ∀ active_value suffix_value, active_value ∈ mlist active → suffix_value ∈ suffix → active_value ≤ suffix_value

export AUXLib.Sorting (increasing)

end Data_structures.priority_queue.lean
