import Algorithms.minimal_representation.lean.groundtruth.minimal_representation_goal
import Algorithms.minimal_representation.lean.groundtruth.minimal_representation_proof_auto
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace Algorithms.minimal_representation.lean.groundtruth.minimal_representation_proof_manual

open Algorithms.minimal_representation.lean
open scoped SimpleC

namespace ProofSupport

open AUXLib

/-- The length-l segment starting at start in the doubled input. -/
private theorem getD_append_left (l1 l2 : List Int) (d : Int) (n : Nat) (hn : n < l1.length) :
    (l1 ++ l2).getD n d = l1.getD n d := by
  induction l1 generalizing n with
  | nil => simp at hn
  | cons x xs ih =>
    cases n with
    | zero => rfl
    | succ n => exact ih n (by simpa using hn)

private theorem app_Znth1 (d : Int) (l1 l2 : List Int) (i : Int)
    (hi : 0 ≤ i ∧ i < Zlength l1) : Znth i (l1 ++ l2) d = Znth i l1 d := by
  unfold Znth
  exact getD_append_left l1 l2 d i.toNat (by simp only [Zlength, Int.ofNat_eq_coe] at hi; omega)

theorem Znth_double_add_length__candidate_transitions (l : List Int) (z : Int)
    (hz : 0 ≤ z ∧ z < Zlength l) :
    Znth (z + Zlength l) (l ++ l) 0 = Znth z (l ++ l) 0 := by
  rw [app_Znth2 0 l l (z+Zlength l) (by omega), app_Znth1 0 l l z hz]
  congr 1
  omega

theorem MRRotationValue_sub_length__candidate_transitions (l : List Int) (start offset : Int)
    (hs : Zlength l ≤ start) (ho : 0 ≤ offset) (hu : start+offset < 2*Zlength l) :
    MRRotationValue l (start-Zlength l) offset = MRRotationValue l start offset := by
  unfold MRRotationValue
  rw [show start+offset = (start-Zlength l+offset)+Zlength l by omega]
  exact (Znth_double_add_length__candidate_transitions l (start-Zlength l+offset) (by omega)).symm

theorem MRRotationEq_sym__candidate_transitions (l : List Int) (a b : Int)
    (h : MRRotationEq l a b) : MRRotationEq l b a := by
  intro offset ho
  exact (h offset ho).symm

theorem MRRotationPrefixEq_sym__candidate_transitions (l : List Int) (a b k : Int)
    (h : MRRotationPrefixEq l a b k) : MRRotationPrefixEq l b a k := by
  intro offset ho
  exact (h offset ho).symm

theorem MRRotationEq_shift__candidate_transitions (l : List Int) (a b shift : Int)
    (hl : 0 < Zlength l) (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 ≤ shift)
    (has : a+shift < Zlength l) (hbs : b+shift < Zlength l)
    (heq : MRRotationEq l a b) : MRRotationEq l (a+shift) (b+shift) := by
  intro offset ho
  by_cases hn : shift+offset < Zlength l
  · have h := heq (shift+offset) (by omega)
    simpa only [MRRotationValue, Int.add_assoc] using h
  · have h := heq (shift+offset-Zlength l) (by omega)
    unfold MRRotationValue at h ⊢
    rw [show a+shift+offset = (a+(shift+offset-Zlength l))+Zlength l by omega,
        show b+shift+offset = (b+(shift+offset-Zlength l))+Zlength l by omega,
        Znth_double_add_length__candidate_transitions l _ (by omega),
        Znth_double_add_length__candidate_transitions l _ (by omega)]
    exact h

theorem MRRotationLt_not_le_rev__candidate_transitions (l : List Int) (a b : Int)
    (hlt : MRRotationLt l a b) : ¬ MRRotationLe l b a := by
  rcases hlt with ⟨da, hda, hab, hlt⟩
  rintro (⟨db, hdb, hba, hgt⟩ | heq)
  · by_cases hd : da < db
    · have := hba da (by omega); omega
    · by_cases hd2 : db < da
      · have := hab db (by omega); omega
      · have hd : db = da := by omega
        subst db
        omega
  · have := heq da hda
    omega

theorem MRRotationEq_frontier_neq__candidate_transitions (l : List Int) (best x y : Int)
    (hf : MRFirstMinimalRotationAt l best) (hx : MRValidStart l x) (hy : MRValidStart l y)
    (hfront : max x y ≤ best) (hxy : x ≠ y) : ¬ MRRotationEq l x y := by
  intro heq
  have hbest := hf.1.1
  dsimp only [MRValidStart] at hx hy hbest
  by_cases hlt : x < y
  · have hshift := MRRotationEq_shift__candidate_transitions l x y (best-y)
      (by omega) hx.1 hy.1 (by omega) (by omega) (by omega) heq
    have ht := hf.2 (x+(best-y)) (by constructor <;> omega)
      (by simpa only [show y+(best-y) = best by omega] using
        MRRotationEq_sym__candidate_transitions l _ _ hshift)
    omega
  · have hshift := MRRotationEq_shift__candidate_transitions l y x (best-x)
      (by omega) hy.1 hx.1 (by omega) (by omega) (by omega)
      (MRRotationEq_sym__candidate_transitions l x y heq)
    have ht := hf.2 (y+(best-x)) (by constructor <;> omega)
      (by simpa only [show x+(best-x) = best by omega] using
        MRRotationEq_sym__candidate_transitions l _ _ hshift)
    omega

theorem MRCandidateState_swap__candidate_transitions (l : List Int) (best i j : Int)
    (hs : MRCandidateState l best i j) : MRCandidateState l best j i := by
  rcases hs with hi | hj | ⟨hf, hne⟩
  · exact Or.inr (Or.inl hi)
  · exact Or.inl hj
  · exact Or.inr (Or.inr ⟨by simpa only [Int.max_comm] using hf,
      fun h => hne (MRRotationEq_sym__candidate_transitions l j i h)⟩)

theorem MRFirstMinimal_excludes_left_interval__candidate_transitions
    (l : List Int) (best i j k : Int) (hf : MRFirstMinimalRotationAt l best)
    (hi : MRValidStart l i) (hj : MRValidStart l j) (hk : 0 ≤ k ∧ k < Zlength l)
    (hp : MRRotationPrefixEq l i j k) (hm : MRRotationValue l j k < MRRotationValue l i k)
    (hib : i ≤ best) : i+k < best := by
  have hb : 0 ≤ best ∧ best < Zlength l := hf.1.1
  dsimp only [MRValidStart] at hi hj
  by_cases hd : i+k < best
  · exact hd
  · let d := best-i
    have hdb : 0 ≤ d ∧ d ≤ k := by dsimp [d]; omega
    have hrawprefix : MRRotationPrefixEq l (j+d) best (k-d) := by
      intro offset ho
      have h := hp (d+offset) (by omega)
      unfold MRRotationValue at h ⊢
      rw [show j+d+offset = j+(d+offset) by omega,
          show best+offset = i+(d+offset) by dsimp [d]; omega]
      exact h.symm
    have hrawlt : MRRotationValue l (j+d) (k-d) < MRRotationValue l best (k-d) := by
      unfold MRRotationValue at hm ⊢
      rw [show j+d+(k-d) = j+k by omega,
          show best+(k-d) = i+k by dsimp [d]; omega]
      exact hm
    by_cases hwrap : j+d < Zlength l
    · have hloses : MRRotationLt l (j+d) best := ⟨k-d, by omega, hrawprefix, hrawlt⟩
      exact False.elim (MRRotationLt_not_le_rev__candidate_transitions l (j+d) best hloses
        (hf.1.2 (j+d) (by constructor <;> omega)))
    · have hloses : MRRotationLt l (j+d-Zlength l) best := by
        refine ⟨k-d, by omega, ?_, ?_⟩
        · intro offset ho
          rw [MRRotationValue_sub_length__candidate_transitions l (j+d) offset (by omega) (by omega) (by omega)]
          exact hrawprefix offset ho
        · rw [MRRotationValue_sub_length__candidate_transitions l (j+d) (k-d) (by omega) (by omega) (by omega)]
          exact hrawlt
      exact False.elim (MRRotationLt_not_le_rev__candidate_transitions l (j+d-Zlength l) best hloses
        (hf.1.2 (j+d-Zlength l) (by constructor <;> omega)))

theorem MRCandidateState_advance_left__candidate_transitions
    (l : List Int) (best i j k : Int) (hf : MRFirstMinimalRotationAt l best)
    (hi : MRValidStart l i) (hj : MRValidStart l j) (hk : 0 ≤ k ∧ k < Zlength l)
    (hp : MRRotationPrefixEq l i j k) (hm : MRRotationValue l j k < MRRotationValue l i k)
    (hs : MRCandidateState l best i j) :
    (i+k+1 = j → MRCandidateState l best (i+k+2) j) ∧
    (i+k+1 ≠ j → MRCandidateState l best (i+k+1) j) := by
  have hb : 0 ≤ best ∧ best < Zlength l := hf.1.1
  dsimp only [MRValidStart] at hi hj
  rcases hs with hbi | hbj | ⟨hfront, hne⟩
  · have h := MRFirstMinimal_excludes_left_interval__candidate_transitions l best i j k hf hi hj hk hp hm (by omega)
    omega
  · exact ⟨fun _ => Or.inr (Or.inl hbj), fun _ => Or.inr (Or.inl hbj)⟩
  · have ha := MRFirstMinimal_excludes_left_interval__candidate_transitions l best i j k hf hi hj hk hp hm (by omega)
    constructor
    · intro hcollision
      by_cases hbj : best = j
      · exact Or.inr (Or.inl hbj)
      · exact Or.inr (Or.inr ⟨by omega,
          MRRotationEq_frontier_neq__candidate_transitions l best (i+k+2) j hf
            (by constructor <;> omega) hj (by omega) (by omega)⟩)
    · intro hcollision
      exact Or.inr (Or.inr ⟨by omega,
        MRRotationEq_frontier_neq__candidate_transitions l best (i+k+1) j hf
          (by constructor <;> omega) hj (by omega) hcollision⟩)

theorem MRCandidateState_advance_right__candidate_transitions
    (l : List Int) (best i j k : Int) (hf : MRFirstMinimalRotationAt l best)
    (hi : MRValidStart l i) (hj : MRValidStart l j) (hk : 0 ≤ k ∧ k < Zlength l)
    (hp : MRRotationPrefixEq l i j k) (hm : MRRotationValue l i k < MRRotationValue l j k)
    (hs : MRCandidateState l best i j) :
    (j+k+1 = i → MRCandidateState l best i (j+k+2)) ∧
    (j+k+1 ≠ i → MRCandidateState l best i (j+k+1)) := by
  have h := MRCandidateState_advance_left__candidate_transitions l best j i k hf hj hi hk
    (MRRotationPrefixEq_sym__candidate_transitions l i j k hp) hm
    (MRCandidateState_swap__candidate_transitions l best i j hs)
  exact ⟨fun hc => MRCandidateState_swap__candidate_transitions l best _ _ (h.1 hc),
    fun hn => MRCandidateState_swap__candidate_transitions l best _ _ (h.2 hn)⟩

theorem MRRotationEq_sym__candidate_boundaries (l : List Int) (i j : Int)
    (h : MRRotationEq l i j) : MRRotationEq l j i := by
  exact MRRotationEq_sym__candidate_transitions l i j h

theorem MRRotationEq_zero_one_all__candidate_boundaries (l : List Int)
    (hl : 1 ≤ Zlength l) (heq : MRRotationEq l 0 1) (start : Int) (hs : MRValidStart l start) :
    MRRotationEq l start 0 := by
  dsimp only [MRValidStart] at hs
  have hchainN (m : Nat) : (m : Int) ≤ Zlength l → Znth (m : Int) (l++l) 0 = Znth 0 (l++l) 0 := by
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      have he := heq (m : Int) (by omega)
      simp only [MRRotationValue, Int.zero_add] at he
      rw [show (m.succ : Int) = 1+(m : Int) by omega, ← he]
      exact ih (by omega)
  have hchain (z : Int) (hz : 0 ≤ z ∧ z ≤ Zlength l) : Znth z (l++l) 0 = Znth 0 (l++l) 0 := by
    have h := hchainN z.toNat (by omega)
    simpa only [Int.toNat_of_nonneg hz.1] using h
  have hall (z : Int) (hz : 0 ≤ z ∧ z < 2*Zlength l) : Znth z (l++l) 0 = Znth 0 (l++l) 0 := by
    by_cases hn : z < Zlength l
    · exact hchain z (by omega)
    · rw [show z = (z-Zlength l)+Zlength l by omega,
        Znth_double_add_length__candidate_transitions l _ (by omega)]
      exact hchain (z-Zlength l) (by omega)
  intro offset ho
  unfold MRRotationValue
  exact (hall (start+offset) (by omega)).trans (hall (0+offset) (by omega)).symm

theorem MRCandidateState_initial__candidate_boundaries (l : List Int) (best : Int)
    (hl : 1 ≤ Zlength l) (hf : MRFirstMinimalRotationAt l best) : MRCandidateState l best 0 1 := by
  have hb : 0 ≤ best ∧ best < Zlength l := hf.1.1
  by_cases h0 : best = 0
  · exact Or.inl h0
  · by_cases h1 : best = 1
    · exact Or.inr (Or.inl h1)
    · refine Or.inr (Or.inr ⟨by omega, ?_⟩)
      intro heq
      have he := MRRotationEq_zero_one_all__candidate_boundaries l hl heq best hb
      have ht := hf.2 0 (by constructor <;> omega) he
      omega

theorem MRCandidateState_equal_exit__candidate_boundaries (l : List Int) (best i j : Int)
    (hi : MRValidStart l i) (hj : MRValidStart l j) (hne : i ≠ j)
    (hf : MRFirstMinimalRotationAt l best) (hs : MRCandidateState l best i j)
    (heq : MRRotationEq l i j) : (i < j → i = best) ∧ (i ≥ j → j = best) := by
  rcases hs with hbi | hbj | ⟨_, hneq⟩
  · have ht := hf.2 j hj (by rw [hbi]; exact heq)
    constructor <;> intro h <;> omega
  · have ht := hf.2 i hi (by rw [hbj]; exact MRRotationEq_sym__candidate_boundaries l i j heq)
    constructor <;> intro h <;> omega
  · exact False.elim (hneq heq)

theorem MRRotation_Zlength__output_finalization (l : List Int) (start : Int)
    (hs : MRValidStart l start) : Zlength (MRRotation l start) = Zlength l := by
  dsimp only [MRValidStart] at hs
  change Int.ofNat (sublist start (start+Zlength l) (l++l)).length = Zlength l
  rw [sublist_length start (start+Zlength l) (l++l) (by have := Zlength_nonneg l; omega)
    (by rw [Zlength_app]; omega)]
  have hn := Zlength_nonneg l
  rw [show start+Zlength l-start = Zlength l by omega]
  exact Int.toNat_of_nonneg hn

theorem MRRotation_Znth__output_finalization (l : List Int) (start offset : Int)
    (hs : MRValidStart l start) (ho : 0 ≤ offset ∧ offset < Zlength l) :
    Znth offset (MRRotation l start) 0 = Znth (start+offset) (l++l) 0 := by
  unfold MRRotation
  rw [Znth_sublist 0 start offset (start+Zlength l) (l++l) hs.1 (by omega)]
  congr 1
  omega

end ProofSupport

open ProofSupport
open Algorithms.minimal_representation.lean.groundtruth.minimal_representation_goal

open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open Algorithms.minimal_representation.lean.groundtruth.minimal_representation_goal
open ProofSupport
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

-- Preserve the source SL tactics and generated residual VCs. The current
-- Goal_apply needs explicit arguments; pure propositions additionally require
-- dump_spatial_left, while spatial split lemmas retain their heap assertions.
theorem proof_of_minimal_representation_entail_wit_1_split_goal_1 : minimal_representation_entail_wit_1_split_goal_1 := by
  unfold minimal_representation_entail_wit_1_split_goal_1
  intro b_pre n_pre best l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  dump_pre_spatial
  simp [sublist]

theorem proof_of_minimal_representation_entail_wit_1_split_goal_spatial : minimal_representation_entail_wit_1_split_goal_spatial := by
  unfold minimal_representation_entail_wit_1_split_goal_spatial
  intro b_pre n_pre best l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  change _ |-- naive_C_Rules.IntArray.undef_seg b_pre 0 n_pre **
    naive_C_Rules.IntArray.seg b_pre n_pre (n_pre+0) ([] : List Int) **
    naive_C_Rules.IntArray.undef_seg b_pre (n_pre+0) (2*n_pre)
  simp only [Int.add_zero]
  sep_apply_l_atomic (naive_C_Rules.IntArray.undef_full_split_to_undef_seg b_pre n_pre (2*n_pre) (by omega))
  sep_apply_right (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp
    (naive_C_Rules.IntArray.seg_empty b_pre n_pre n_pre)).2)
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    rfl

theorem proof_of_minimal_representation_entail_wit_1 : minimal_representation_entail_wit_1 := by
  unfold minimal_representation_entail_wit_1
  right
  intro b_pre n_pre best l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_1_split_goal_1 b_pre n_pre best l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6))
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_1_split_goal_spatial b_pre n_pre best l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6))
    | exact (proof_of_minimal_representation_entail_wit_1_split_goal_1 b_pre n_pre best l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
    | exact (proof_of_minimal_representation_entail_wit_1_split_goal_spatial b_pre n_pre best l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)

theorem proof_of_minimal_representation_entail_wit_2_split_goal_1 : minimal_representation_entail_wit_2_split_goal_1 := by
  unfold minimal_representation_entail_wit_2_split_goal_1
  intro b_pre n_pre best l p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  dump_pre_spatial
  rw [sublist_split 0 (p+1) p l (by omega) (by omega), sublist_single 0 p l (by omega)]

theorem proof_of_minimal_representation_entail_wit_2_split_goal_spatial : minimal_representation_entail_wit_2_split_goal_spatial := by
  unfold minimal_representation_entail_wit_2_split_goal_spatial
  intro b_pre n_pre best l p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  rw [sublist_split 0 (p+1) p l (by omega) (by omega), sublist_single 0 p l (by omega)]
  rw [show n_pre+(p+1) = n_pre+p+1 by omega]
  cancel

theorem proof_of_minimal_representation_entail_wit_2 : minimal_representation_entail_wit_2 := by
  unfold minimal_representation_entail_wit_2
  right
  intro b_pre n_pre best l p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_2_split_goal_1 b_pre n_pre best l p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9))
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_2_split_goal_spatial b_pre n_pre best l p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9))
    | exact (proof_of_minimal_representation_entail_wit_2_split_goal_1 b_pre n_pre best l p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)
    | exact (proof_of_minimal_representation_entail_wit_2_split_goal_spatial b_pre n_pre best l p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)

theorem proof_of_minimal_representation_entail_wit_3_split_goal_spatial : minimal_representation_entail_wit_3_split_goal_spatial := by
  unfold minimal_representation_entail_wit_3_split_goal_spatial
  intro b_pre n_pre best l p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have hp : p = n_pre := by omega
  rw [hp, sublist_self l n_pre PreH4.symm, show n_pre+n_pre = 2*n_pre by omega]
  sep_apply_l_atomic (naive_C_Rules.IntArray.seg_merge_to_full b_pre 0 n_pre (2*n_pre) l l (by omega))
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  cancel

theorem proof_of_minimal_representation_entail_wit_3 : minimal_representation_entail_wit_3 := by
  unfold minimal_representation_entail_wit_3
  right
  intro b_pre n_pre best l p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_3_split_goal_spatial b_pre n_pre best l p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9))
    | exact (proof_of_minimal_representation_entail_wit_3_split_goal_spatial b_pre n_pre best l p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)

theorem proof_of_minimal_representation_entail_wit_4 : minimal_representation_entail_wit_4 := by
  unfold minimal_representation_entail_wit_4
  intro out_pre b_pre n_pre a_pre best l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  have Hstate := MRCandidateState_initial__candidate_boundaries l best (by omega) PreH6
  Left
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega

theorem proof_of_minimal_representation_entail_wit_5_1_split_goal_1 : minimal_representation_entail_wit_5_1_split_goal_1 := by
  unfold minimal_representation_entail_wit_5_1_split_goal_1
  intro n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  intro offset ho
  omega

theorem proof_of_minimal_representation_entail_wit_5_1 : minimal_representation_entail_wit_5_1 := by
  unfold minimal_representation_entail_wit_5_1
  right
  intro n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_5_1_split_goal_1 n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_minimal_representation_entail_wit_5_1_split_goal_1 n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_minimal_representation_entail_wit_5_2_split_goal_1 : minimal_representation_entail_wit_5_2_split_goal_1 := by
  unfold minimal_representation_entail_wit_5_2_split_goal_1
  intro n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  intro offset ho
  omega

theorem proof_of_minimal_representation_entail_wit_5_2 : minimal_representation_entail_wit_5_2 := by
  unfold minimal_representation_entail_wit_5_2
  right
  intro n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_5_2_split_goal_1 n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_minimal_representation_entail_wit_5_2_split_goal_1 n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_minimal_representation_entail_wit_6_split_goal_1 : minimal_representation_entail_wit_6_split_goal_1 := by
  unfold minimal_representation_entail_wit_6_split_goal_1
  intro n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  intro offset ho
  by_cases hk : offset < k
  · exact PreH17 offset (by omega)
  · have heq : offset = k := by omega
    subst offset
    exact PreH1

theorem proof_of_minimal_representation_entail_wit_6 : minimal_representation_entail_wit_6 := by
  unfold minimal_representation_entail_wit_6
  right
  intro n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_6_split_goal_1 n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_minimal_representation_entail_wit_6_split_goal_1 n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_minimal_representation_entail_wit_7_1 : minimal_representation_entail_wit_7_1 := by
  unfold minimal_representation_entail_wit_7_1
  intro out_pre b_pre n_pre a_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have Hstate : MRCandidateState l best (i+k+2) j := by
    have ht := MRCandidateState_advance_left__candidate_transitions l best i j k PreH18
      (by constructor <;> omega) (by constructor <;> omega) (by omega) PreH20
      (by unfold MRRotationValue; omega) PreH19
    exact ht.1 (by omega)
  Right
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first
      | assumption
      | trivial
      | omega
      | (simpa only [Int.add_assoc] using Hstate)

theorem proof_of_minimal_representation_entail_wit_7_2 : minimal_representation_entail_wit_7_2 := by
  unfold minimal_representation_entail_wit_7_2
  intro out_pre b_pre n_pre a_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have Hstate : MRCandidateState l best (i+k+1) j := by
    have ht := MRCandidateState_advance_left__candidate_transitions l best i j k PreH18
      (by constructor <;> omega) (by constructor <;> omega) (by omega) PreH20
      (by unfold MRRotationValue; omega) PreH19
    exact ht.2 (by omega)
  Right
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first
      | assumption
      | trivial
      | omega
      | (simpa only [Int.add_assoc] using Hstate)

theorem proof_of_minimal_representation_entail_wit_7_3 : minimal_representation_entail_wit_7_3 := by
  unfold minimal_representation_entail_wit_7_3
  intro out_pre b_pre n_pre a_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have Hstate : MRCandidateState l best i (j+k+2) := by
    have ht := MRCandidateState_advance_right__candidate_transitions l best i j k PreH18
      (by constructor <;> omega) (by constructor <;> omega) (by omega) PreH20
      (by unfold MRRotationValue; omega) PreH19
    exact ht.1 (by omega)
  Left
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first
      | assumption
      | trivial
      | omega
      | (simpa only [Int.add_assoc] using Hstate)

theorem proof_of_minimal_representation_entail_wit_7_4 : minimal_representation_entail_wit_7_4 := by
  unfold minimal_representation_entail_wit_7_4
  intro out_pre b_pre n_pre a_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have Hstate : MRCandidateState l best i (j+k+1) := by
    have ht := MRCandidateState_advance_right__candidate_transitions l best i j k PreH18
      (by constructor <;> omega) (by constructor <;> omega) (by omega) PreH20
      (by unfold MRRotationValue; omega) PreH19
    exact ht.2 (by omega)
  Left
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first
      | assumption
      | trivial
      | omega
      | (simpa only [Int.add_assoc] using Hstate)

theorem proof_of_minimal_representation_entail_wit_8_1_split_goal_1 : minimal_representation_entail_wit_8_1_split_goal_1 := by
  unfold minimal_representation_entail_wit_8_1_split_goal_1
  intro n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  intro h
  rcases PreH16 with hb | hb | ⟨hf, _⟩ <;> omega

theorem proof_of_minimal_representation_entail_wit_8_1 : minimal_representation_entail_wit_8_1 := by
  unfold minimal_representation_entail_wit_8_1
  right
  intro n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_8_1_split_goal_1 n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_minimal_representation_entail_wit_8_1_split_goal_1 n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)

theorem proof_of_minimal_representation_entail_wit_8_2_split_goal_1 : minimal_representation_entail_wit_8_2_split_goal_1 := by
  unfold minimal_representation_entail_wit_8_2_split_goal_1
  intro n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  intro h
  rcases PreH17 with hb | hb | ⟨hf, _⟩ <;> omega

theorem proof_of_minimal_representation_entail_wit_8_2 : minimal_representation_entail_wit_8_2 := by
  unfold minimal_representation_entail_wit_8_2
  right
  intro n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_8_2_split_goal_1 n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_minimal_representation_entail_wit_8_2_split_goal_1 n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_minimal_representation_entail_wit_8_3 : minimal_representation_entail_wit_8_3 := by
  unfold minimal_representation_entail_wit_8_3
  intro out_pre b_pre n_pre a_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hi : MRValidStart l i := by constructor <;> omega
  have hj : MRValidStart l j := by constructor <;> omega
  have heq : MRRotationEq l i j := by
    unfold MRRotationEq
    rw [PreH5, ← PreH1]
    exact PreH17
  obtain ⟨hlt, hge⟩ := MRCandidateState_equal_exit__candidate_boundaries l best i j hi hj PreH12 PreH15 PreH16 heq
  Left
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega

theorem proof_of_minimal_representation_entail_wit_9_1_split_goal_1 : minimal_representation_entail_wit_9_1_split_goal_1 := by
  unfold minimal_representation_entail_wit_9_1_split_goal_1
  intro n_pre best l i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  simp [sublist]

theorem proof_of_minimal_representation_entail_wit_9_1 : minimal_representation_entail_wit_9_1 := by
  unfold minimal_representation_entail_wit_9_1
  right
  intro n_pre best l i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_9_1_split_goal_1 n_pre best l i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_minimal_representation_entail_wit_9_1_split_goal_1 n_pre best l i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_minimal_representation_entail_wit_9_2_split_goal_1 : minimal_representation_entail_wit_9_2_split_goal_1 := by
  unfold minimal_representation_entail_wit_9_2_split_goal_1
  intro n_pre best l i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  simp [sublist]

theorem proof_of_minimal_representation_entail_wit_9_2 : minimal_representation_entail_wit_9_2 := by
  unfold minimal_representation_entail_wit_9_2
  right
  intro n_pre best l i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_9_2_split_goal_1 n_pre best l i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_minimal_representation_entail_wit_9_2_split_goal_1 n_pre best l i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_minimal_representation_entail_wit_9_3_split_goal_1 : minimal_representation_entail_wit_9_3_split_goal_1 := by
  unfold minimal_representation_entail_wit_9_3_split_goal_1
  intro n_pre best l i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  simp [sublist]

theorem proof_of_minimal_representation_entail_wit_9_3 : minimal_representation_entail_wit_9_3 := by
  unfold minimal_representation_entail_wit_9_3
  right
  intro n_pre best l i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_9_3_split_goal_1 n_pre best l i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_minimal_representation_entail_wit_9_3_split_goal_1 n_pre best l i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_minimal_representation_entail_wit_9_4_split_goal_1 : minimal_representation_entail_wit_9_4_split_goal_1 := by
  unfold minimal_representation_entail_wit_9_4_split_goal_1
  intro n_pre best l i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  simp [sublist]

theorem proof_of_minimal_representation_entail_wit_9_4 : minimal_representation_entail_wit_9_4 := by
  unfold minimal_representation_entail_wit_9_4
  right
  intro n_pre best l i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_9_4_split_goal_1 n_pre best l i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_minimal_representation_entail_wit_9_4_split_goal_1 n_pre best l i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_minimal_representation_entail_wit_10_split_goal_1 : minimal_representation_entail_wit_10_split_goal_1 := by
  unfold minimal_representation_entail_wit_10_split_goal_1
  intro n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have hs : MRValidStart l best := by constructor <;> omega
  have hn := MRRotation_Zlength__output_finalization l best hs
  rw [← MRRotation_Znth__output_finalization l best k hs (by omega),
    sublist_split 0 (k+1) k (MRRotation l best) (by omega) (by omega),
    sublist_single 0 k (MRRotation l best) (by omega)]

theorem proof_of_minimal_representation_entail_wit_10 : minimal_representation_entail_wit_10 := by
  unfold minimal_representation_entail_wit_10
  right
  intro n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_10_split_goal_1 n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_minimal_representation_entail_wit_10_split_goal_1 n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)

theorem proof_of_minimal_representation_return_wit_1_split_goal_spatial : minimal_representation_return_wit_1_split_goal_spatial := by
  unfold minimal_representation_return_wit_1_split_goal_spatial
  intro out_pre n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have hs : MRValidStart l best := by constructor <;> omega
  have hn := MRRotation_Zlength__output_finalization l best hs
  have hk : k = n_pre := by omega
  rw [hk, sublist_self (MRRotation l best) n_pre (by omega)]
  sep_apply_l_atomic (naive_C_Rules.IntArray.seg_to_full out_pre 0 n_pre (MRRotation l best))
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  cancel

theorem proof_of_minimal_representation_return_wit_1 : minimal_representation_return_wit_1 := by
  unfold minimal_representation_return_wit_1
  right
  intro out_pre n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_return_wit_1_split_goal_spatial out_pre n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_minimal_representation_return_wit_1_split_goal_spatial out_pre n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)

end Algorithms.minimal_representation.lean.groundtruth.minimal_representation_proof_manual
