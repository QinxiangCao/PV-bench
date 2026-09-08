import Algorithms.matrix_chain_multiplication.lean.groundtruth.matrix_chain_multiplication_goal
import Algorithms.matrix_chain_multiplication.lean.groundtruth.matrix_chain_multiplication_proof_auto
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import ListLib.General.Length

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace Algorithms.matrix_chain_multiplication.lean.groundtruth.matrix_chain_multiplication_proof_manual

open Algorithms.matrix_chain_multiplication.lean
open scoped SimpleC

namespace ProofSupport

open AUXLib

private theorem minimum_iff (P : Int → Prop) (v : Int) :
    MaxMinLib.min_value_of_subset (· ≤ ·) P id v ↔ P v ∧ ∀ x, P x → v ≤ x := by
  constructor
  · rintro ⟨x, ⟨hx, hleast⟩, rfl⟩
    exact ⟨hx, hleast⟩
  · rintro ⟨hv, hleast⟩
    exact ⟨v, ⟨hv, hleast⟩, rfl⟩

theorem matrix_chain_index_bounds (n i j : Int) (hn : 1 ≤ n)
    (hi : 0 ≤ i ∧ i < n) (hj : 0 ≤ j ∧ j < n) : 0 ≤ i*n+j ∧ i*n+j < n*n := by
  constructor
  · exact add_nonneg (mul_nonneg hi.1 (by omega)) hj.1
  · nlinarith

theorem matrix_chain_dimensions_product_bound (a b c : Int)
    (ha : 1 ≤ a ∧ a ≤ 100) (hb : 1 ≤ b ∧ b ≤ 100) (hc : 1 ≤ c ∧ c ≤ 100) :
    a*b*c ≤ 1000000 := by
  have hab : a*b ≤ 10000 := by nlinarith
  have ht := mul_le_mul_of_nonneg_right hab (show 0 ≤ c by omega)
  nlinarith

theorem matrix_chain_zero_table_lengths_done__initialization
    (dimensions table : List Int) (matrix_count : Int)
    (hcount : 1 ≤ matrix_count) (hdims : Zlength dimensions = matrix_count + 1)
    (hzero : MatrixChainZeroPrefix table (matrix_count * matrix_count)) :
    MatrixChainLengthsDone dimensions table matrix_count 2 := by
  refine ⟨by omega, ?_⟩
  intro length left right hl hr hleft hfits
  have he : length = 1 := by omega
  have her : right = left := by omega
  subst length right
  have hind := matrix_chain_index_bounds matrix_count left left hcount
    ⟨hleft, by omega⟩ ⟨hleft, by omega⟩
  rw [hzero.2 _ hind]
  apply (minimum_iff _ 0).mpr
  refine ⟨MatrixChainPlan_single left hleft (by omega), ?_⟩
  intro c hc
  cases hc with
  | MatrixChainPlan_single => omega
  | MatrixChainPlan_join l k r lc rc hleft hsplit => omega

theorem matrix_chain_plan_linear_upper_bound__candidate_progress
    (dimensions : List Int) (matrix_count left right : Int)
    (hdims : MatrixChainDimensionsBounded dimensions matrix_count)
    (hleft : 0 ≤ left) (horder : left ≤ right) (hright : right < matrix_count) :
    ∃ cost, MatrixChainPlan dimensions left right cost ∧ cost ≤ (right-left)*1000000 := by
  generalize hs : (right-left).toNat = span
  induction span generalizing left right with
  | zero =>
    have he : right = left := by omega
    subst right
    exact ⟨0, MatrixChainPlan_single left hleft (by have := hdims.1; omega), by omega⟩
  | succ span ih =>
    have hstrict : left < right := by omega
    obtain ⟨rc, hplan, hbound⟩ := ih (left+1) right (by omega) (by omega) hright (by omega)
    refine ⟨0+rc+Znth left dimensions 0*Znth (left+1) dimensions 0*Znth (right+1) dimensions 0, ?_, ?_⟩
    · exact MatrixChainPlan_join left left right 0 rc hleft ⟨le_refl _, hstrict⟩
        (by have := hdims.1; omega)
        (MatrixChainPlan_single left hleft (by have := hdims.1; omega)) hplan
    · have hb := matrix_chain_dimensions_product_bound _ _ _
        (hdims.2 left ⟨hleft, by omega⟩)
        (hdims.2 (left+1) ⟨by omega, by omega⟩)
        (hdims.2 (right+1) ⟨by omega, by omega⟩)
      omega

theorem matrix_chain_interval_minimum_upper_bound__candidate_progress
    (dimensions : List Int) (matrix_count left right answer : Int)
    (hdims : MatrixChainDimensionsBounded dimensions matrix_count)
    (hleft : 0 ≤ left) (horder : left ≤ right) (hright : right < matrix_count)
    (hmin : MatrixChainIntervalMinimum dimensions left right answer) :
    answer ≤ (right-left)*1000000 := by
  obtain ⟨cost, hp, hb⟩ := matrix_chain_plan_linear_upper_bound__candidate_progress
    dimensions matrix_count left right hdims hleft horder hright
  have hm := (minimum_iff _ answer).mp hmin
  exact le_trans (hm.2 cost hp) hb

theorem matrix_chain_split_progress_initial__candidate_progress
    (dimensions table : List Int) (matrix_count width length left : Int)
    (hp : MatrixChainLeftProgress dimensions table matrix_count length left) :
    MatrixChainSplitProgress dimensions table matrix_count width length left (left+1)
      (Znth (left*width+left) table 0 + Znth ((left+1)*width+(left+length-1)) table 0 +
       Znth left dimensions 0*Znth (left+1) dimensions 0*Znth ((left+length-1)+1) dimensions 0) := by
  refine ⟨hp, ?_⟩
  apply (minimum_iff _ _).mpr
  refine ⟨⟨left, ⟨by omega, by omega⟩, rfl⟩, ?_⟩
  rintro candidate ⟨split, hb, hc⟩
  have he : split = left := by omega
  subst split
  exact le_of_eq hc.symm

private theorem split_progress_extend
    (dimensions table : List Int) (matrix_count width length left split best candidate : Int)
    (hleft : left ≤ split)
    (hc : MatrixChainSplitCandidate dimensions table width left (left+length-1) split candidate)
    (hp : MatrixChainSplitProgress dimensions table matrix_count width length left split best) :
    MatrixChainSplitProgress dimensions table matrix_count width length left (split+1) (min best candidate) := by
  refine ⟨hp.1, ?_⟩
  have hm := (minimum_iff _ best).mp hp.2
  apply (minimum_iff _ _).mpr
  constructor
  · by_cases h : best ≤ candidate
    · rw [min_eq_left h]
      obtain ⟨root, hb, hr⟩ := hm.1
      exact ⟨root, ⟨hb.1, by omega⟩, hr⟩
    · rw [min_eq_right (by omega : candidate ≤ best)]
      exact ⟨split, ⟨hleft, by omega⟩, hc⟩
  · rintro value ⟨root, hb, hr⟩
    by_cases h : root < split
    · exact le_trans (min_le_left _ _) (hm.2 value ⟨root, ⟨hb.1, h⟩, hr⟩)
    · have he : root = split := by omega
      subst root
      have hv : value = candidate := hr.trans hc.symm
      rw [hv]
      exact min_le_right _ _

theorem matrix_chain_split_progress_better__min_update
    (dimensions table : List Int) (matrix_count width length left split best candidate : Int)
    (hleft : left ≤ split) (hbetter : candidate < best)
    (hc : MatrixChainSplitCandidate dimensions table width left (left+length-1) split candidate)
    (hp : MatrixChainSplitProgress dimensions table matrix_count width length left split best) :
    MatrixChainSplitProgress dimensions table matrix_count width length left (split+1) candidate := by
  simpa only [min_eq_right (le_of_lt hbetter)] using
    split_progress_extend dimensions table matrix_count width length left split best candidate hleft hc hp

theorem matrix_chain_split_progress_not_better__min_update
    (dimensions table : List Int) (matrix_count width length left split best candidate : Int)
    (hleft : left ≤ split) (hbetter : best ≤ candidate)
    (hc : MatrixChainSplitCandidate dimensions table width left (left+length-1) split candidate)
    (hp : MatrixChainSplitProgress dimensions table matrix_count width length left split best) :
    MatrixChainSplitProgress dimensions table matrix_count width length left (split+1) best := by
  simpa only [min_eq_left hbetter] using
    split_progress_extend dimensions table matrix_count width length left split best candidate hleft hc hp

theorem matrix_chain_split_progress_complete__min_update
    (dimensions table : List Int) (matrix_count length left right best : Int)
    (hlen : 2 ≤ length) (hleft : 0 ≤ left) (hr : right = left+length-1)
    (hrbound : right < matrix_count) (hdimbound : right+1 < Zlength dimensions)
    (hp : MatrixChainSplitProgress dimensions table matrix_count matrix_count length left right best) :
    MatrixChainIntervalMinimum dimensions left right best := by
  subst right
  have hdone := hp.1.1.2
  have hmin := (minimum_iff _ best).mp hp.2
  have subminimum (root : Int) (hroot : left ≤ root ∧ root < left+length-1) :=
    And.intro
      (hdone (root-left+1) left root ⟨by omega, by omega⟩ (by omega) hleft (by omega))
      (hdone (left+length-1-root) (root+1) (left+length-1) ⟨by omega, by omega⟩
        (by omega) (by omega) (by omega))
  apply (minimum_iff _ best).mpr
  constructor
  · obtain ⟨root, hb, hc⟩ := hmin.1
    have hm := subminimum root hb
    rw [hc]
    exact MatrixChainPlan_join left root (left+length-1) _ _ hleft hb hdimbound
      ((minimum_iff _ _).mp hm.1).1 ((minimum_iff _ _).mp hm.2).1
  · intro arbitrary hplan
    generalize he : left+length-1 = rr at hplan
    cases hplan with
    | MatrixChainPlan_single => omega
    | MatrixChainPlan_join l k r lc rc hl hb hd hpl hpr =>
      have hm := subminimum k ⟨hb.1, by omega⟩
      rw [← he] at hpr ⊢
      have hbl := ((minimum_iff _ _).mp hm.1).2 lc hpl
      have hbr := ((minimum_iff _ _).mp hm.2).2 rc hpr
      have hc := hmin.2 _ ⟨k, ⟨hb.1, by omega⟩, rfl⟩
      try dsimp at hbl hbr hc
      omega

end ProofSupport

open ProofSupport
open Algorithms.matrix_chain_multiplication.lean.groundtruth.matrix_chain_multiplication_goal

open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open Algorithms.matrix_chain_multiplication.lean.groundtruth.matrix_chain_multiplication_goal
open ProofSupport
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

private theorem candidate_upper (dims table : List Int) (n len l k : Int)
    (hn : n ≤ 8) (hlen : 2 ≤ len) (hl : 0 ≤ l) (hfit : l+len ≤ n)
    (hk : l ≤ k ∧ k < l+len-1)
    (hd : MatrixChainDimensionsBounded dims n)
    (hprogress : MatrixChainLengthsDone dims table n len) :
    Znth (l*n+k) table 0 + Znth ((k+1)*n+(l+len-1)) table 0 +
      Znth l dims 0*Znth (k+1) dims 0*Znth ((l+len-1)+1) dims 0 ≤ 7000000 := by
  have hml := hprogress.2 (k-l+1) l k ⟨by omega, by omega⟩ (by omega) hl (by omega)
  have hmr := hprogress.2 (l+len-1-k) (k+1) (l+len-1) ⟨by omega, by omega⟩
    (by omega) (by omega) (by omega)
  have hb1 := matrix_chain_interval_minimum_upper_bound__candidate_progress
    dims n l k _ hd hl hk.1 (by omega) hml
  have hb2 := matrix_chain_interval_minimum_upper_bound__candidate_progress
    dims n (k+1) (l+len-1) _ hd (by omega) (by omega) (by omega) hmr
  have hb3 := matrix_chain_dimensions_product_bound _ _ _
    (hd.2 l ⟨hl, by omega⟩) (hd.2 (k+1) ⟨by omega, by omega⟩)
    (hd.2 ((l+len-1)+1) ⟨by omega, by omega⟩)
  omega

private theorem matrix_index_injective (n i j k l : Int) (hn : 1 ≤ n)
    (hj : 0 ≤ j ∧ j < n) (hl : 0 ≤ l ∧ l < n)
    (he : i*n+j = k*n+l) : i = k ∧ j = l := by
  have hi : i = k := by
    rcases lt_trichotomy i k with h | h | h
    · have hp : (i+1)*n ≤ k*n := mul_le_mul_of_nonneg_right (by omega) (by omega)
      nlinarith
    · exact h
    · have hp : (k+1)*n ≤ i*n := mul_le_mul_of_nonneg_right (by omega) (by omega)
      nlinarith
  exact ⟨hi, by rw [hi] at he; omega⟩

theorem proof_of_matrixChainMinCost_entail_wit_1_split_goal_1 : matrixChainMinCost_entail_wit_1_split_goal_1 := by
  unfold matrixChainMinCost_entail_wit_1_split_goal_1
  intro matrix_count_pre dimensions_l PreH1 PreH2 PreH3 PreH4
  exact ⟨rfl, fun i hi => False.elim (by omega)⟩

theorem proof_of_matrixChainMinCost_entail_wit_2_split_goal_1 : matrixChainMinCost_entail_wit_2_split_goal_1 := by
  unfold matrixChainMinCost_entail_wit_2_split_goal_1
  intro matrix_count_pre dimensions_l cost_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  rcases PreH8 with ⟨hlen, hzero⟩
  constructor
  · rw [Zlength_app, Zlength_cons, Zlength_nil, hlen]
    omega
  · intro index hi
    by_cases hlt : index < i
    · have hn : Znth index (cost_l_2 ++ [0]) 0 = Znth index cost_l_2 0 :=
        ListLib.app_Znth1 0 cost_l_2 [0] index ⟨hi.1, by change index < Zlength cost_l_2; omega⟩
      rw [hn]
      exact hzero index ⟨hi.1, hlt⟩
    · have he : index = i := by omega
      subst index
      rw [app_Znth2 0 cost_l_2 [0] i (by omega), hlen, Int.sub_self]
      rfl

theorem proof_of_matrixChainMinCost_entail_wit_5_split_goal_1 : matrixChainMinCost_entail_wit_5_split_goal_1 := by
  unfold matrixChainMinCost_entail_wit_5_split_goal_1
  intro matrix_count_pre dimensions_l chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  exact ⟨PreH10, fun l r hl hr hfit => False.elim (by omega)⟩

theorem proof_of_matrixChainMinCost_entail_wit_6_split_goal_1 : matrixChainMinCost_entail_wit_6_split_goal_1 := by
  unfold matrixChainMinCost_entail_wit_6_split_goal_1
  intro matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  exact (PreH10.2 ((left+chain_length-1)+1) ⟨by omega, by omega⟩).2

theorem proof_of_matrixChainMinCost_entail_wit_6_split_goal_2 : matrixChainMinCost_entail_wit_6_split_goal_2 := by
  unfold matrixChainMinCost_entail_wit_6_split_goal_2
  intro matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  exact (PreH10.2 ((left+chain_length-1)+1) ⟨by omega, by omega⟩).1

theorem proof_of_matrixChainMinCost_entail_wit_6_split_goal_3 : matrixChainMinCost_entail_wit_6_split_goal_3 := by
  unfold matrixChainMinCost_entail_wit_6_split_goal_3
  intro matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  exact (PreH10.2 (left+1) ⟨by omega, by omega⟩).2

theorem proof_of_matrixChainMinCost_entail_wit_6_split_goal_4 : matrixChainMinCost_entail_wit_6_split_goal_4 := by
  unfold matrixChainMinCost_entail_wit_6_split_goal_4
  intro matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  exact (PreH10.2 (left+1) ⟨by omega, by omega⟩).1

theorem proof_of_matrixChainMinCost_entail_wit_6_split_goal_5 : matrixChainMinCost_entail_wit_6_split_goal_5 := by
  unfold matrixChainMinCost_entail_wit_6_split_goal_5
  intro matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  exact (PreH10.2 left ⟨by omega, by omega⟩).2

theorem proof_of_matrixChainMinCost_entail_wit_6_split_goal_6 : matrixChainMinCost_entail_wit_6_split_goal_6 := by
  unfold matrixChainMinCost_entail_wit_6_split_goal_6
  intro matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  exact (PreH10.2 left ⟨by omega, by omega⟩).1

theorem proof_of_matrixChainMinCost_entail_wit_6_split_goal_7 : matrixChainMinCost_entail_wit_6_split_goal_7 := by
  unfold matrixChainMinCost_entail_wit_6_split_goal_7
  intro matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hb := matrix_chain_index_bounds matrix_count_pre (left+1) (left+chain_length-1) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  exact (PreH11 ((left+1)*matrix_count_pre+(left+chain_length-1)) (by rw [PreH5]; exact hb)).2

theorem proof_of_matrixChainMinCost_entail_wit_6_split_goal_8 : matrixChainMinCost_entail_wit_6_split_goal_8 := by
  unfold matrixChainMinCost_entail_wit_6_split_goal_8
  intro matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hb := matrix_chain_index_bounds matrix_count_pre (left+1) (left+chain_length-1) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  exact (PreH11 ((left+1)*matrix_count_pre+(left+chain_length-1)) (by rw [PreH5]; exact hb)).1

theorem proof_of_matrixChainMinCost_entail_wit_6_split_goal_9 : matrixChainMinCost_entail_wit_6_split_goal_9 := by
  unfold matrixChainMinCost_entail_wit_6_split_goal_9
  intro matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hb := matrix_chain_index_bounds matrix_count_pre left left (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  exact (PreH11 (left*matrix_count_pre+left) (by rw [PreH5]; exact hb)).2

theorem proof_of_matrixChainMinCost_entail_wit_6_split_goal_10 : matrixChainMinCost_entail_wit_6_split_goal_10 := by
  unfold matrixChainMinCost_entail_wit_6_split_goal_10
  intro matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hb := matrix_chain_index_bounds matrix_count_pre left left (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  exact (PreH11 (left*matrix_count_pre+left) (by rw [PreH5]; exact hb)).1

theorem proof_of_matrixChainMinCost_entail_wit_6_split_goal_11 : matrixChainMinCost_entail_wit_6_split_goal_11 := by
  unfold matrixChainMinCost_entail_wit_6_split_goal_11
  intro matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hb := matrix_chain_index_bounds matrix_count_pre (left+1) (left+chain_length-1) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  exact hb.2

theorem proof_of_matrixChainMinCost_entail_wit_6_split_goal_12 : matrixChainMinCost_entail_wit_6_split_goal_12 := by
  unfold matrixChainMinCost_entail_wit_6_split_goal_12
  intro matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hb := matrix_chain_index_bounds matrix_count_pre left left (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  exact hb.2

theorem proof_of_matrixChainMinCost_entail_wit_7_split_goal_1 : matrixChainMinCost_entail_wit_7_split_goal_1 := by
  unfold matrixChainMinCost_entail_wit_7_split_goal_1
  intro matrix_count_pre dimensions_l cost_l chain_length left right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  exact matrix_chain_split_progress_initial__candidate_progress _ _ _ _ _ _ PreH34

theorem proof_of_matrixChainMinCost_entail_wit_7_split_goal_2 : matrixChainMinCost_entail_wit_7_split_goal_2 := by
  unfold matrixChainMinCost_entail_wit_7_split_goal_2
  intro matrix_count_pre dimensions_l cost_l chain_length left right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  exact candidate_upper dimensions_l cost_l matrix_count_pre chain_length left left
    (by omega) (by omega) (by omega) (by omega) ⟨by omega, by omega⟩ PreH32 PreH34.1

theorem proof_of_matrixChainMinCost_entail_wit_8_split_goal_1 : matrixChainMinCost_entail_wit_8_split_goal_1 := by
  unfold matrixChainMinCost_entail_wit_8_split_goal_1
  intro matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  exact (PreH17.2 ((left+chain_length-1)+1) ⟨by omega, by omega⟩).2

theorem proof_of_matrixChainMinCost_entail_wit_8_split_goal_2 : matrixChainMinCost_entail_wit_8_split_goal_2 := by
  unfold matrixChainMinCost_entail_wit_8_split_goal_2
  intro matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  exact (PreH17.2 ((left+chain_length-1)+1) ⟨by omega, by omega⟩).1

theorem proof_of_matrixChainMinCost_entail_wit_8_split_goal_3 : matrixChainMinCost_entail_wit_8_split_goal_3 := by
  unfold matrixChainMinCost_entail_wit_8_split_goal_3
  intro matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  exact (PreH17.2 (split+1) ⟨by omega, by omega⟩).2

theorem proof_of_matrixChainMinCost_entail_wit_8_split_goal_4 : matrixChainMinCost_entail_wit_8_split_goal_4 := by
  unfold matrixChainMinCost_entail_wit_8_split_goal_4
  intro matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  exact (PreH17.2 (split+1) ⟨by omega, by omega⟩).1

theorem proof_of_matrixChainMinCost_entail_wit_8_split_goal_5 : matrixChainMinCost_entail_wit_8_split_goal_5 := by
  unfold matrixChainMinCost_entail_wit_8_split_goal_5
  intro matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  exact (PreH17.2 left ⟨by omega, by omega⟩).2

theorem proof_of_matrixChainMinCost_entail_wit_8_split_goal_6 : matrixChainMinCost_entail_wit_8_split_goal_6 := by
  unfold matrixChainMinCost_entail_wit_8_split_goal_6
  intro matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  exact (PreH17.2 left ⟨by omega, by omega⟩).1

theorem proof_of_matrixChainMinCost_entail_wit_8_split_goal_7 : matrixChainMinCost_entail_wit_8_split_goal_7 := by
  unfold matrixChainMinCost_entail_wit_8_split_goal_7
  intro matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hb := matrix_chain_index_bounds matrix_count_pre (split+1) (left+chain_length-1) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  exact (PreH18 ((split+1)*matrix_count_pre+(left+chain_length-1)) (by rw [PreH16]; exact hb)).2

theorem proof_of_matrixChainMinCost_entail_wit_8_split_goal_8 : matrixChainMinCost_entail_wit_8_split_goal_8 := by
  unfold matrixChainMinCost_entail_wit_8_split_goal_8
  intro matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hb := matrix_chain_index_bounds matrix_count_pre (split+1) (left+chain_length-1) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  exact (PreH18 ((split+1)*matrix_count_pre+(left+chain_length-1)) (by rw [PreH16]; exact hb)).1

theorem proof_of_matrixChainMinCost_entail_wit_8_split_goal_9 : matrixChainMinCost_entail_wit_8_split_goal_9 := by
  unfold matrixChainMinCost_entail_wit_8_split_goal_9
  intro matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hb := matrix_chain_index_bounds matrix_count_pre left split (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  exact (PreH18 (left*matrix_count_pre+split) (by rw [PreH16]; exact hb)).2

theorem proof_of_matrixChainMinCost_entail_wit_8_split_goal_10 : matrixChainMinCost_entail_wit_8_split_goal_10 := by
  unfold matrixChainMinCost_entail_wit_8_split_goal_10
  intro matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hb := matrix_chain_index_bounds matrix_count_pre left split (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  exact (PreH18 (left*matrix_count_pre+split) (by rw [PreH16]; exact hb)).1

theorem proof_of_matrixChainMinCost_entail_wit_8_split_goal_11 : matrixChainMinCost_entail_wit_8_split_goal_11 := by
  unfold matrixChainMinCost_entail_wit_8_split_goal_11
  intro matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hb := matrix_chain_index_bounds matrix_count_pre (split+1) (left+chain_length-1) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  exact hb.2

theorem proof_of_matrixChainMinCost_entail_wit_8_split_goal_12 : matrixChainMinCost_entail_wit_8_split_goal_12 := by
  unfold matrixChainMinCost_entail_wit_8_split_goal_12
  intro matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hb := matrix_chain_index_bounds matrix_count_pre left split (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  exact hb.2

theorem proof_of_matrixChainMinCost_entail_wit_9_split_goal_1 : matrixChainMinCost_entail_wit_9_split_goal_1 := by
  unfold matrixChainMinCost_entail_wit_9_split_goal_1
  intro matrix_count_pre dimensions_l cost_l chain_length left right split best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  rfl

theorem proof_of_matrixChainMinCost_entail_wit_9_split_goal_2 : matrixChainMinCost_entail_wit_9_split_goal_2 := by
  unfold matrixChainMinCost_entail_wit_9_split_goal_2
  intro matrix_count_pre dimensions_l cost_l chain_length left right split best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  exact candidate_upper dimensions_l cost_l matrix_count_pre chain_length left split
    (by omega) (by omega) (by omega) (by omega) ⟨by omega, by omega⟩ PreH36 PreH38.1.1

theorem proof_of_matrixChainMinCost_entail_wit_10_1_split_goal_1 : matrixChainMinCost_entail_wit_10_1_split_goal_1 := by
  unfold matrixChainMinCost_entail_wit_10_1_split_goal_1
  intro matrix_count_pre dimensions_l cost_l_2 chain_length left right split best candidate PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  rw [PreH8] at PreH21
  exact matrix_chain_split_progress_better__min_update _ _ _ _ _ _ _ _ _
    (by omega) (by omega) PreH21 PreH22

theorem proof_of_matrixChainMinCost_entail_wit_10_2_split_goal_1 : matrixChainMinCost_entail_wit_10_2_split_goal_1 := by
  unfold matrixChainMinCost_entail_wit_10_2_split_goal_1
  intro matrix_count_pre dimensions_l cost_l_2 chain_length left right split best candidate PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  rw [PreH8] at PreH21
  exact matrix_chain_split_progress_not_better__min_update _ _ _ _ _ _ _ _ _
    (by omega) (by omega) PreH21 PreH22

theorem proof_of_matrixChainMinCost_entail_wit_11_split_goal_1 : matrixChainMinCost_entail_wit_11_split_goal_1 := by
  unfold matrixChainMinCost_entail_wit_11_split_goal_1
  intro matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  apply matrix_chain_split_progress_complete__min_update dimensions_l cost_l_2 matrix_count_pre
    chain_length left (left+chain_length-1) best (by omega) (by omega) rfl (by omega) (by omega)
  convert PreH19 using 1 <;> omega

theorem proof_of_matrixChainMinCost_entail_wit_11_split_goal_2 : matrixChainMinCost_entail_wit_11_split_goal_2 := by
  unfold matrixChainMinCost_entail_wit_11_split_goal_2
  intro matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  convert PreH19 using 1 <;> omega

theorem proof_of_matrixChainMinCost_entail_wit_11_split_goal_3 : matrixChainMinCost_entail_wit_11_split_goal_3 := by
  unfold matrixChainMinCost_entail_wit_11_split_goal_3
  intro matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  exact (matrix_chain_index_bounds matrix_count_pre left (left+chain_length-1) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩).2

theorem proof_of_matrixChainMinCost_entail_wit_12_split_goal_1 : matrixChainMinCost_entail_wit_12_split_goal_1 := by
  unfold matrixChainMinCost_entail_wit_12_split_goal_1
  intro matrix_count_pre dimensions_l cost_l_2 chain_length left right best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hcur : 0 ≤ left*matrix_count_pre+(left+chain_length-1) ∧
      left*matrix_count_pre+(left+chain_length-1) < Zlength cost_l_2 := by
    rw [PreH15]
    exact matrix_chain_index_bounds matrix_count_pre left (left+chain_length-1) (by omega)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  have hd := PreH18.1.1
  have hp := PreH18.1.2
  constructor
  · refine ⟨hd.1, ?_⟩
    intro len l r hlen hr hl hfit
    have hidx : 0 ≤ l*matrix_count_pre+r ∧ l*matrix_count_pre+r < Zlength cost_l_2 := by
      rw [PreH15]
      exact matrix_chain_index_bounds matrix_count_pre l r (by omega)
        ⟨hl, by omega⟩ ⟨by omega, by omega⟩
    have hneq : left*matrix_count_pre+(left+chain_length-1) ≠ l*matrix_count_pre+r := by
      intro he
      have hh := matrix_index_injective matrix_count_pre left (left+chain_length-1) l r
        (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ he
      omega
    rw [Znth_replace_Znth_Diff 0 cost_l_2 _ _ best hcur hidx hneq]
    exact hd.2 len l r hlen hr hl hfit
  · intro l r hl hr hfit
    by_cases he : l = left
    · subst l
      have her : r = left+chain_length-1 := by omega
      subst r
      rw [Znth_replace_Znth_Same 0 cost_l_2 _ best hcur]
      convert PreH19 using 1 <;> omega
    · have hidx : 0 ≤ l*matrix_count_pre+r ∧ l*matrix_count_pre+r < Zlength cost_l_2 := by
        rw [PreH15]
        exact matrix_chain_index_bounds matrix_count_pre l r (by omega)
          ⟨hl.1, by omega⟩ ⟨by omega, by omega⟩
      have hneq : left*matrix_count_pre+(left+chain_length-1) ≠ l*matrix_count_pre+r := by
        intro hi
        have hh := matrix_index_injective matrix_count_pre left (left+chain_length-1) l r
          (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hi
        omega
      rw [Znth_replace_Znth_Diff 0 cost_l_2 _ _ best hcur hidx hneq]
      exact hp l r ⟨hl.1, by omega⟩ hr hfit

theorem proof_of_matrixChainMinCost_entail_wit_12_split_goal_2 : matrixChainMinCost_entail_wit_12_split_goal_2 := by
  unfold matrixChainMinCost_entail_wit_12_split_goal_2
  intro matrix_count_pre dimensions_l cost_l_2 chain_length left right best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hcur : 0 ≤ left*matrix_count_pre+(left+chain_length-1) ∧
      left*matrix_count_pre+(left+chain_length-1) < Zlength cost_l_2 := by
    rw [PreH15]
    exact matrix_chain_index_bounds matrix_count_pre left (left+chain_length-1) (by omega)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  intro index hi
  rw [Zlength_replace_Znth] at hi
  by_cases he : left*matrix_count_pre+(left+chain_length-1) = index
  · rw [←he, Znth_replace_Znth_Same 0 cost_l_2 _ best hcur]
    exact ⟨by omega, by omega⟩
  · rw [Znth_replace_Znth_Diff 0 cost_l_2 _ index best hcur hi he]
    exact PreH17 index hi

theorem proof_of_matrixChainMinCost_entail_wit_12_split_goal_3 : matrixChainMinCost_entail_wit_12_split_goal_3 := by
  unfold matrixChainMinCost_entail_wit_12_split_goal_3
  intro matrix_count_pre dimensions_l cost_l_2 chain_length left right best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  rw [Zlength_replace_Znth]
  exact PreH15

theorem proof_of_matrixChainMinCost_entail_wit_13_split_goal_1 : matrixChainMinCost_entail_wit_13_split_goal_1 := by
  unfold matrixChainMinCost_entail_wit_13_split_goal_1
  intro matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  refine ⟨by omega, ?_⟩
  intro len l r hlen hr hl hfit
  by_cases hlt : len < chain_length
  · exact PreH12.1.2 len l r ⟨hlen.1, hlt⟩ hr hl hfit
  · have he : len = chain_length := by omega
    subst len
    exact PreH12.2 l r ⟨hl, by omega⟩ hr hfit

theorem proof_of_matrixChainMinCost_entail_wit_14_split_goal_1 : matrixChainMinCost_entail_wit_14_split_goal_1 := by
  unfold matrixChainMinCost_entail_wit_14_split_goal_1
  intro matrix_count_pre dimensions_l chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  refine ⟨PreH4, ?_⟩
  simpa only [Int.zero_mul, Int.zero_add] using PreH10.2 matrix_count_pre 0 (matrix_count_pre-1)
    ⟨by omega, by omega⟩ (by omega) (by omega) (by omega)

theorem proof_of_matrixChainMinCost_entail_wit_14_split_goal_2 : matrixChainMinCost_entail_wit_14_split_goal_2 := by
  unfold matrixChainMinCost_entail_wit_14_split_goal_2
  intro matrix_count_pre dimensions_l chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  refine ⟨PreH5, ?_⟩
  intro l r hr
  exact PreH10.2 (r-l+1) l r ⟨by omega, by omega⟩ (by omega) hr.1 (by omega)

theorem proof_of_matrixChainMinCost_entail_wit_14_split_goal_3 : matrixChainMinCost_entail_wit_14_split_goal_3 := by
  unfold matrixChainMinCost_entail_wit_14_split_goal_3
  intro matrix_count_pre dimensions_l chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  convert PreH10 using 1 <;> omega

theorem proof_of_matrixChainMinCost_entail_wit_14_split_goal_4 : matrixChainMinCost_entail_wit_14_split_goal_4 := by
  unfold matrixChainMinCost_entail_wit_14_split_goal_4
  intro matrix_count_pre dimensions_l chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hb := matrix_chain_index_bounds matrix_count_pre 0 (matrix_count_pre-1) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  simp only [Int.zero_mul, Int.zero_add] at hb
  exact (PreH9 (matrix_count_pre-1) (by rw [PreH5]; exact hb)).2

theorem proof_of_matrixChainMinCost_entail_wit_14_split_goal_5 : matrixChainMinCost_entail_wit_14_split_goal_5 := by
  unfold matrixChainMinCost_entail_wit_14_split_goal_5
  intro matrix_count_pre dimensions_l chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hb := matrix_chain_index_bounds matrix_count_pre 0 (matrix_count_pre-1) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  simp only [Int.zero_mul, Int.zero_add] at hb
  exact (PreH9 (matrix_count_pre-1) (by rw [PreH5]; exact hb)).1

theorem proof_of_matrixChainMinCost_entail_wit_1 : matrixChainMinCost_entail_wit_1 := by
  unfold matrixChainMinCost_entail_wit_1
  right
  intro matrix_count_pre dimensions_l PreH1 PreH2 PreH3 PreH4
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_matrixChainMinCost_entail_wit_1_split_goal_1 matrix_count_pre dimensions_l PreH1 PreH2 PreH3 PreH4

theorem proof_of_matrixChainMinCost_entail_wit_2 : matrixChainMinCost_entail_wit_2 := by
  unfold matrixChainMinCost_entail_wit_2
  right
  intro matrix_count_pre dimensions_l cost_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_matrixChainMinCost_entail_wit_2_split_goal_1 matrix_count_pre dimensions_l cost_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8

theorem proof_of_matrixChainMinCost_entail_wit_3 : matrixChainMinCost_entail_wit_3 := by
  unfold matrixChainMinCost_entail_wit_3
  right
  intro cost_pre matrix_count_pre dimensions_l cost_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have he : i = matrix_count_pre*matrix_count_pre := by omega
  subst i
  refine Automation.exp_right_rule (CRules := naive_C_Rules) cost_l_2 ?_
  split_pure_spatial
  · simpa only [Int.zero_mul, Int.add_zero, Int.sub_zero] using
      intArray.seg_to_full cost_pre 0 (matrix_count_pre*matrix_count_pre) cost_l_2
  · split_pures <;> dump_pre_spatial
    all_goals try first | assumption | exact PreH8.1
    · exact matrix_chain_zero_table_lengths_done__initialization _ _ _ PreH2 PreH4 PreH8
    · intro index hi
      rw [PreH8.2 index (by rw [←PreH8.1]; exact hi)]
      omega

theorem proof_of_matrixChainMinCost_entail_wit_5 : matrixChainMinCost_entail_wit_5 := by
  unfold matrixChainMinCost_entail_wit_5
  right
  intro matrix_count_pre dimensions_l chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_matrixChainMinCost_entail_wit_5_split_goal_1 matrix_count_pre dimensions_l chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10

theorem proof_of_matrixChainMinCost_entail_wit_6 : matrixChainMinCost_entail_wit_6 := by
  unfold matrixChainMinCost_entail_wit_6
  right
  intro matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_matrixChainMinCost_entail_wit_6_split_goal_1 matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_matrixChainMinCost_entail_wit_6_split_goal_2 matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_matrixChainMinCost_entail_wit_6_split_goal_3 matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_matrixChainMinCost_entail_wit_6_split_goal_4 matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_matrixChainMinCost_entail_wit_6_split_goal_5 matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_matrixChainMinCost_entail_wit_6_split_goal_6 matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_matrixChainMinCost_entail_wit_6_split_goal_7 matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_matrixChainMinCost_entail_wit_6_split_goal_8 matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_matrixChainMinCost_entail_wit_6_split_goal_9 matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_matrixChainMinCost_entail_wit_6_split_goal_10 matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_matrixChainMinCost_entail_wit_6_split_goal_11 matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_matrixChainMinCost_entail_wit_6_split_goal_12 matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_matrixChainMinCost_entail_wit_7 : matrixChainMinCost_entail_wit_7 := by
  unfold matrixChainMinCost_entail_wit_7
  right
  intro matrix_count_pre dimensions_l cost_l chain_length left right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_matrixChainMinCost_entail_wit_7_split_goal_1 matrix_count_pre dimensions_l cost_l chain_length left right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
      | exact proof_of_matrixChainMinCost_entail_wit_7_split_goal_2 matrix_count_pre dimensions_l cost_l chain_length left right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34

theorem proof_of_matrixChainMinCost_entail_wit_8 : matrixChainMinCost_entail_wit_8 := by
  unfold matrixChainMinCost_entail_wit_8
  right
  intro matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_matrixChainMinCost_entail_wit_8_split_goal_1 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
      | exact proof_of_matrixChainMinCost_entail_wit_8_split_goal_2 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
      | exact proof_of_matrixChainMinCost_entail_wit_8_split_goal_3 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
      | exact proof_of_matrixChainMinCost_entail_wit_8_split_goal_4 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
      | exact proof_of_matrixChainMinCost_entail_wit_8_split_goal_5 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
      | exact proof_of_matrixChainMinCost_entail_wit_8_split_goal_6 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
      | exact proof_of_matrixChainMinCost_entail_wit_8_split_goal_7 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
      | exact proof_of_matrixChainMinCost_entail_wit_8_split_goal_8 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
      | exact proof_of_matrixChainMinCost_entail_wit_8_split_goal_9 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
      | exact proof_of_matrixChainMinCost_entail_wit_8_split_goal_10 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
      | exact proof_of_matrixChainMinCost_entail_wit_8_split_goal_11 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
      | exact proof_of_matrixChainMinCost_entail_wit_8_split_goal_12 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19

theorem proof_of_matrixChainMinCost_entail_wit_9 : matrixChainMinCost_entail_wit_9 := by
  unfold matrixChainMinCost_entail_wit_9
  right
  intro matrix_count_pre dimensions_l cost_l chain_length left right split best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_matrixChainMinCost_entail_wit_9_split_goal_1 matrix_count_pre dimensions_l cost_l chain_length left right split best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
      | exact proof_of_matrixChainMinCost_entail_wit_9_split_goal_2 matrix_count_pre dimensions_l cost_l chain_length left right split best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38

theorem proof_of_matrixChainMinCost_entail_wit_10_1 : matrixChainMinCost_entail_wit_10_1 := by
  unfold matrixChainMinCost_entail_wit_10_1
  right
  intro matrix_count_pre dimensions_l cost_l_2 chain_length left right split best candidate PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_matrixChainMinCost_entail_wit_10_1_split_goal_1 matrix_count_pre dimensions_l cost_l_2 chain_length left right split best candidate PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22

theorem proof_of_matrixChainMinCost_entail_wit_10_2 : matrixChainMinCost_entail_wit_10_2 := by
  unfold matrixChainMinCost_entail_wit_10_2
  right
  intro matrix_count_pre dimensions_l cost_l_2 chain_length left right split best candidate PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_matrixChainMinCost_entail_wit_10_2_split_goal_1 matrix_count_pre dimensions_l cost_l_2 chain_length left right split best candidate PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22

theorem proof_of_matrixChainMinCost_entail_wit_11 : matrixChainMinCost_entail_wit_11 := by
  unfold matrixChainMinCost_entail_wit_11
  right
  intro matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_matrixChainMinCost_entail_wit_11_split_goal_1 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
      | exact proof_of_matrixChainMinCost_entail_wit_11_split_goal_2 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
      | exact proof_of_matrixChainMinCost_entail_wit_11_split_goal_3 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19

theorem proof_of_matrixChainMinCost_entail_wit_12 : matrixChainMinCost_entail_wit_12 := by
  unfold matrixChainMinCost_entail_wit_12
  right
  intro matrix_count_pre dimensions_l cost_l_2 chain_length left right best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_matrixChainMinCost_entail_wit_12_split_goal_1 matrix_count_pre dimensions_l cost_l_2 chain_length left right best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
      | exact proof_of_matrixChainMinCost_entail_wit_12_split_goal_2 matrix_count_pre dimensions_l cost_l_2 chain_length left right best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
      | exact proof_of_matrixChainMinCost_entail_wit_12_split_goal_3 matrix_count_pre dimensions_l cost_l_2 chain_length left right best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19

theorem proof_of_matrixChainMinCost_entail_wit_13 : matrixChainMinCost_entail_wit_13 := by
  unfold matrixChainMinCost_entail_wit_13
  right
  intro matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_matrixChainMinCost_entail_wit_13_split_goal_1 matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_matrixChainMinCost_entail_wit_14 : matrixChainMinCost_entail_wit_14 := by
  unfold matrixChainMinCost_entail_wit_14
  right
  intro matrix_count_pre dimensions_l chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_matrixChainMinCost_entail_wit_14_split_goal_1 matrix_count_pre dimensions_l chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
      | exact proof_of_matrixChainMinCost_entail_wit_14_split_goal_2 matrix_count_pre dimensions_l chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
      | exact proof_of_matrixChainMinCost_entail_wit_14_split_goal_3 matrix_count_pre dimensions_l chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
      | exact proof_of_matrixChainMinCost_entail_wit_14_split_goal_4 matrix_count_pre dimensions_l chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
      | exact proof_of_matrixChainMinCost_entail_wit_14_split_goal_5 matrix_count_pre dimensions_l chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10

end Algorithms.matrix_chain_multiplication.lean.groundtruth.matrix_chain_multiplication_proof_manual
