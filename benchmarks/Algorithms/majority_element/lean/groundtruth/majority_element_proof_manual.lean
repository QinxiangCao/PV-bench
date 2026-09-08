import Algorithms.majority_element.lean.groundtruth.majority_element_goal
import Algorithms.majority_element.lean.groundtruth.majority_element_proof_auto
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace Algorithms.majority_element.lean.groundtruth.majority_element_proof_manual

open Algorithms.majority_element.lean
open scoped SimpleC

namespace ProofSupport

open AUXLib

theorem count_app (m : Int) (l1 l2 : List Int) :
    count m (l1 ++ l2) = count m l1 + count m l2 := by
  induction l1 with
  | nil => simp [count]
  | cons a l ih => simp only [List.cons_append, count, ih]; omega

theorem count_repeat_nat (m candidate : Int) (n : Nat) :
    count m (List.replicate n candidate) = if m = candidate then (n : Int) else 0 := by
  induction n with
  | zero => by_cases h : m = candidate <;> simp [count, h]
  | succ n ih =>
    by_cases h : m = candidate
    · subst m; simp [List.replicate_succ, count, ih]; omega
    · simp [List.replicate_succ, count, ih, h, Ne.symm h]

theorem repeated_nil (candidate : Int) : repeated candidate 0 = [] := rfl

theorem repeat_snoc (A : Type) (x : A) (n : Nat) :
    List.replicate (n + 1) x = List.replicate n x ++ [x] := by
  exact List.replicate_append_replicate.symm

theorem repeated_succ (candidate vote : Int) (h : 0 ≤ vote) :
    repeated candidate (vote + 1) = repeated candidate vote ++ [candidate] := by
  unfold repeated
  rw [show (vote + 1).toNat = vote.toNat + 1 by omega]
  exact repeat_snoc Int candidate vote.toNat

theorem repeated_pred (candidate vote : Int) (h : 0 < vote) :
    repeated candidate vote = repeated candidate (vote - 1) ++ [candidate] := by
  have := repeated_succ candidate (vote - 1) (by omega)
  simpa using this

theorem majority_on_reduced_init (major candidate : Int) (rest : List Int)
    (h : IsMajorityElement major rest) : MajorityOnReduced major candidate 0 rest := by
  exact ⟨by omega, h⟩

theorem majority_on_reduced_reset (major candidate a : Int) (rest : List Int)
    (h : IsMajorityElement major (repeated candidate 0 ++ a :: rest)) :
    MajorityOnReduced major a 1 rest := by
  exact ⟨by omega, h⟩

theorem majority_on_reduced_same (major candidate vote : Int) (rest : List Int)
    (hv : 0 ≤ vote)
    (h : IsMajorityElement major (repeated candidate vote ++ candidate :: rest)) :
    MajorityOnReduced major candidate (vote + 1) rest := by
  refine ⟨by omega, ?_⟩
  simpa only [repeated_succ candidate vote hv, List.append_assoc, List.singleton_append] using h

theorem majority_on_reduced_cancel (major candidate a vote : Int) (rest : List Int)
    (hv : 0 < vote) (hne : a ≠ candidate)
    (h : IsMajorityElement major (repeated candidate vote ++ a :: rest)) :
    MajorityOnReduced major candidate (vote - 1) rest := by
  refine ⟨by omega, ?_⟩
  unfold IsMajorityElement repeated at *
  simp only [count_app, count_repeat_nat, count, List.length_append,
    List.length_replicate, List.length_cons, Int.natCast_add, Int.natCast_one] at *
  split at h <;> split at h <;> split <;> omega

theorem majority_of_repeated_eq (major candidate vote : Int) (hv : 0 ≤ vote)
    (h : IsMajorityElement major (repeated candidate vote)) : major = candidate := by
  unfold IsMajorityElement repeated at h
  rw [count_repeat_nat, List.length_replicate] at h
  split at h
  · assumption
  · omega

theorem app_Znth_suffix_cons (l1 l2 : List Int) (i d : Int)
    (hi : i = Zlength l1) (hlt : i < Zlength (l1 ++ l2)) :
    ∃ h t, l2 = h :: t ∧ Znth i (l1 ++ l2) d = h := by
  cases l2 with
  | nil => simp only [List.append_nil] at hlt; omega
  | cons h t =>
    refine ⟨h, t, rfl, ?_⟩
    rw [app_Znth2 d l1 (h :: t) i (by omega), hi]
    simp [Znth]

end ProofSupport

open ProofSupport
open Algorithms.majority_element.lean.groundtruth.majority_element_goal

open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open Algorithms.majority_element.lean.groundtruth.majority_element_goal
open ProofSupport
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

-- Coq's proof-local `grab H pat` copies a hypothesis matching the given type.
scoped syntax (name := grab) "grab " ident term : tactic
macro_rules
  | `(tactic| grab $id:ident $pat:term) => `(tactic| have $id : $pat := by assumption)

-- The spatial branch retains the array-length invariant used by the Coq proof.
theorem proof_of_majorityElement_entail_wit_1 : majorityElement_entail_wit_1 := by
  unfold majorityElement_entail_wit_1
  left
  intro n p l x hmajor hlo hhi hlen
  Exists x ([] : List Int) l
  grab hmajorCopy (IsMajorityElement x l)
  have hm := majority_on_reduced_init x 0 l hmajorCopy
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | omega | simp [Zlength]

theorem proof_of_majorityElement_entail_wit_2_1 : majorityElement_entail_wit_2_1 := by
  unfold majorityElement_entail_wit_2_1
  left
  intro n p l candidate x vote i l1 l2 hv hi hl hlen1 hi0 hin hn0 hnmax hv0 hvi hmajor hreduced
  prop_apply naive_C_Rules.IntArray.full_Zlength
  Intros_p hlen
  have hlt : i < Zlength (l1 ++ l2) := by rw [← hl, hlen]; exact hi
  obtain ⟨a, rest, hl2, hz⟩ := app_Znth_suffix_cons l1 l2 i 0 hlen1 hlt
  have hzl : Znth i l 0 = a := by rw [hl]; exact hz
  have hred : MajorityOnReduced x (Znth i l 0) (vote + 1) rest := by
    rw [hzl, hv]
    apply majority_on_reduced_reset x candidate a rest
    simpa only [hl2, hv] using hreduced.2
  Exists x (l1 ++ [a]) rest
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | (solve | simp [hl, hl2, List.append_assoc])
      | (simp only [Zlength_app, Zlength_cons, Zlength_nil]; omega)

theorem proof_of_majorityElement_entail_wit_2_2 : majorityElement_entail_wit_2_2 := by
  unfold majorityElement_entail_wit_2_2
  left
  intro n p l candidate x vote i l1 l2 heq hv hi hl hlen1 hi0 hin hn0 hnmax hv0 hvi hmajor hreduced
  prop_apply naive_C_Rules.IntArray.full_Zlength
  Intros_p hlen
  have hlt : i < Zlength (l1 ++ l2) := by rw [← hl, hlen]; exact hi
  obtain ⟨a, rest, hl2, hz⟩ := app_Znth_suffix_cons l1 l2 i 0 hlen1 hlt
  have hac : a = candidate := by rw [hl, hz] at heq; exact heq
  have hred : MajorityOnReduced x candidate (vote + 1) rest := by
    apply majority_on_reduced_same x candidate vote rest hv0
    simpa only [hl2, hac] using hreduced.2
  Exists x (l1 ++ [a]) rest
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | (solve | simp [hl, hl2, List.append_assoc])
      | (simp only [Zlength_app, Zlength_cons, Zlength_nil]; omega)

theorem proof_of_majorityElement_entail_wit_2_3 : majorityElement_entail_wit_2_3 := by
  unfold majorityElement_entail_wit_2_3
  left
  intro n p l candidate x vote i l1 l2 hne hv hi hl hlen1 hi0 hin hn0 hnmax hv0 hvi hmajor hreduced
  prop_apply naive_C_Rules.IntArray.full_Zlength
  Intros_p hlen
  have hlt : i < Zlength (l1 ++ l2) := by rw [← hl, hlen]; exact hi
  obtain ⟨a, rest, hl2, hz⟩ := app_Znth_suffix_cons l1 l2 i 0 hlen1 hlt
  have hac : a ≠ candidate := by rw [hl, hz] at hne; exact hne
  have hred : MajorityOnReduced x candidate (vote + (-1)) rest := by
    apply majority_on_reduced_cancel x candidate a vote rest (by omega) hac
    simpa only [hl2] using hreduced.2
  Exists x (l1 ++ [a]) rest
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | (solve | simp [hl, hl2, List.append_assoc])
      | (simp only [Zlength_app, Zlength_cons, Zlength_nil]; omega)

theorem proof_of_majorityElement_return_wit_1 : majorityElement_return_wit_1 := by
  unfold majorityElement_return_wit_1
  left
  intro n p l candidate x vote i l1 l2 hi hl hlen1 hi0 hin hn0 hnmax hv0 hvi hmajor hreduced
  prop_apply naive_C_Rules.IntArray.full_Zlength
  Intros_p hlen
  have hlen2 : Zlength l2 = 0 := by
    rw [hl, Zlength_app] at hlen
    omega
  have hl2 : l2 = [] := by
    apply List.length_eq_zero_iff.mp
    simp only [Zlength, Int.ofNat_eq_coe] at hlen2
    omega
  have hxc : x = candidate := by
    apply majority_of_repeated_eq x candidate vote hv0
    simpa only [hl2, List.append_nil] using hreduced.2
  have hresult : IsMajorityElement candidate l := by rw [← hxc]; exact hmajor
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact hresult

end Algorithms.majority_element.lean.groundtruth.majority_element_proof_manual
