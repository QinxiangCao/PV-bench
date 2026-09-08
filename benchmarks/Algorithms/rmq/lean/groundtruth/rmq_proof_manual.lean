import Algorithms.rmq.lean.groundtruth.rmq_goal
import Algorithms.rmq.lean.groundtruth.rmq_proof_auto
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace Algorithms.rmq.lean.groundtruth.rmq_proof_manual

open Algorithms.rmq.lean
open scoped SimpleC

namespace ProofSupport

open AUXLib


open MaxMinLib

private theorem power_nat (j : Int) (hj : 0 ≤ j) : Power2 j = (2 : Int)^j.toNat := by
  cases j with
  | ofNat j => rfl
  | negSucc j => omega

theorem worker_Power2_nonneg (j : Int) : 0 ≤ Power2 j := by
  cases j with
  | ofNat j => exact pow_nonneg (by omega) j
  | negSucc j => exact le_refl _

theorem worker_Power2_bound_lt_30 (j K : Int) (hK : K ≤ 30) (hj : j < K) : Power2 j ≤ 536870912 := by
  by_cases hn : 0 ≤ j
  · rw [power_nat j hn]
    have h := pow_le_pow_right₀ (show (1 : Int) ≤ 2 by omega) (show j.toNat ≤ 29 by omega)
    have he : (2 : Int)^29 = 536870912 := by decide
    rw [he] at h
    exact h
  · cases j with
    | ofNat j => exact False.elim (hn (Int.natCast_nonneg j))
    | negSucc j => change (0 : Int) ≤ 536870912; omega

theorem worker_Power2_double_int_bound_30 (j K : Int) (hK : K ≤ 30) (hj : j < K) : Power2 j*2 ≤ 2147483647 := by
  have := worker_Power2_bound_lt_30 j K hK hj; omega

theorem worker_Power2_plus_n_int_bound_30 (j K n i : Int) (hK : K ≤ 30) (hj : j < K)
    (hn : n ≤ 100000) (hi : i ≤ n) : i+Power2 j ≤ 2147483647 := by
  have := worker_Power2_bound_lt_30 j K hK hj; omega

theorem STZeroPrefix_replace_zero_step (st_ls : List Int) (idx : Int)
    (hz : STZeroPrefix st_ls idx) (hi : idx < Zlength st_ls) :
    STZeroPrefix (replace_Znth idx 0 st_ls) (idx+1) := by
  intro p hp
  by_cases he : p = idx
  · rw [he,Znth_replace_Znth_Same 0 st_ls idx 0 ⟨by omega,hi⟩]
  · by_cases hidx : 0 ≤ idx
    · rw [Znth_replace_Znth_Diff 0 st_ls idx p 0 ⟨hidx,hi⟩ ⟨hp.1,by omega⟩ (Ne.symm he)]
      exact hz p ⟨hp.1,by omega⟩
    · omega

theorem worker_Power2_0_1 : Power2 0 = 1 := rfl

theorem worker_STBasePrefix_write_base_step (l st_ls : List Int) (K n i : Int)
    (hl : Zlength l = n) (hs : Zlength st_ls = n*K) (hK : 0 < K) (hi : 0 ≤ i) (hin : i < n)
    (hiK : 0 ≤ i*K) (hiKn : i*K < n*K) (hb : STBasePrefix l st_ls K n i) :
    STBasePrefix l (replace_Znth (i*K) (Znth i l 0) st_ls) K n (i+1) := by
  intro p hp
  unfold STCellRangeMax
  simp only [Int.add_zero]
  by_cases he : p = i
  · rw [he,Znth_replace_Znth_Same 0 st_ls (i*K) _ ⟨hiK,by omega⟩]
    refine ⟨hi,by rw [worker_Power2_0_1]; omega,by rw [worker_Power2_0_1]; omega,i,⟨?_,?_⟩,rfl⟩
    · rw [worker_Power2_0_1]; omega
    · intro k hk
      have he : k = i := by rw [worker_Power2_0_1] at hk; omega
      subst k; exact le_refl _
  · have hpi : p < i := by omega
    rw [Znth_replace_Znth_Diff 0 st_ls (i*K) (p*K) _ ⟨hiK,by omega⟩ ⟨by nlinarith [hp.1],by nlinarith [hp.1]⟩ (by nlinarith)]
    simpa only [STCellRangeMax,Int.add_zero] using hb p ⟨hp.1,by omega⟩

theorem worker_STBasePrefix_complete_level1 (l st_ls : List Int) (K n i : Int)
    (hg : i ≥ n) (hle : i ≤ n) (hb : STBasePrefix l st_ls K n i) : STBuiltBeforeLevel l st_ls K n 1 := by
  intro p j hj
  have he : j = 0 := by omega
  subst j
  have hh : p+1 ≤ n := by simpa only [worker_Power2_0_1] using hj.2.2.2
  exact hb p ⟨hj.1,by omega⟩

theorem Power2_pos (k : Int) (hk : 0 ≤ k) : 0 < Power2 k := by
  rw [power_nat k hk]; positivity

theorem Power2_step (j : Int) (hj : 0 ≤ j) : Power2 j*2 = Power2 (j+1) := by
  rw [power_nat j hj,power_nat (j+1) (by omega),show (j+1).toNat = j.toNat+1 by omega,pow_succ]

theorem Power2_sub1_double (j : Int) (hj : 1 ≤ j) : Power2 j = Power2 (j-1)+Power2 (j-1) := by
  have h := Power2_step (j-1) (by omega)
  rw [show j-1+1 = j by omega] at h
  omega

theorem cell_index_mod (row K col : Int) (hK : 0 < K) (hc : 0 ≤ col ∧ col < K) :
    (row*K+col) % K = col := by
  rw [Int.add_comm,Int.add_mul_emod_self_right,Int.emod_eq_of_lt hc.1 hc.2]

theorem cell_index_col_eq (row1 row2 K col1 col2 : Int) (hK : 0 < K)
    (hc1 : 0 ≤ col1 ∧ col1 < K) (hc2 : 0 ≤ col2 ∧ col2 < K)
    (he : row1*K+col1 = row2*K+col2) : col1 = col2 := by
  have h := congrArg (fun z : Int => z % K) he
  simpa only [cell_index_mod row1 K col1 hK hc1,cell_index_mod row2 K col2 hK hc2] using h

theorem cell_index_diff_col_neq (row1 row2 K col1 col2 : Int) (hK : 0 < K)
    (hc1 : 0 ≤ col1 ∧ col1 < K) (hc2 : 0 ≤ col2 ∧ col2 < K) (hn : col1 ≠ col2) :
    row1*K+col1 ≠ row2*K+col2 := fun he => hn (cell_index_col_eq row1 row2 K col1 col2 hK hc1 hc2 he)

theorem cell_index_same_col_eq (row1 row2 K col : Int) (hK : 0 < K)
    (he : row1*K+col = row2*K+col) : row1 = row2 := by nlinarith

theorem cell_index_same_col_neq (row1 row2 K col : Int) (hK : 0 < K) (hn : row1 ≠ row2) :
    row1*K+col ≠ row2*K+col := fun he => hn (cell_index_same_col_eq row1 row2 K col hK he)

theorem STCellRangeMax_replace_other (l st : List Int) (K row col idx v : Int)
    (hc : STCellRangeMax l st K row col) (hi : 0 ≤ idx ∧ idx < Zlength st)
    (hcell : 0 ≤ row*K+col ∧ row*K+col < Zlength st) (hne : idx ≠ row*K+col) :
    STCellRangeMax l (replace_Znth idx v st) K row col := by
  unfold STCellRangeMax
  rw [Znth_replace_Znth_Diff 0 st idx (row*K+col) v hi hcell hne]
  exact hc

theorem STBuiltBeforeLevel_replace_level_cell (l st : List Int) (K n level row v : Int)
    (hb : STBuiltBeforeLevel l st K n level) (hl : level < K)
    (hi : 0 ≤ row*K+level ∧ row*K+level < Zlength st)
    (hr : ∀ row0 col, (0 ≤ row0 ∧ 0 ≤ col ∧ col < level ∧ row0+Power2 col ≤ n) →
      0 ≤ row0*K+col ∧ row0*K+col < Zlength st) :
    STBuiltBeforeLevel l (replace_Znth (row*K+level) v st) K n level := by
  intro row0 col hc
  exact STCellRangeMax_replace_other l st K row0 col (row*K+level) v (hb row0 col hc) hi (hr row0 col hc)
    (cell_index_diff_col_neq row row0 K level col (by omega) ⟨by omega,hl⟩ ⟨hc.2.1,by omega⟩ (by omega))

private theorem max_union_cover {P Q R : Int → Prop} (f : Int → Int) (a b : Int)
    (ha : max_value_of_subset (· ≤ ·) P f a) (hb : max_value_of_subset (· ≤ ·) Q f b)
    (hc : ∀ x, (P x ∨ Q x) ↔ R x) : max_value_of_subset (· ≤ ·) R f (max a b) := by
  obtain ⟨x,⟨hxp,hxm⟩,hx⟩ := ha
  obtain ⟨y,⟨hyq,hym⟩,hy⟩ := hb
  by_cases he : b ≤ a
  · rw [max_eq_left he]
    refine ⟨x,⟨(hc x).mp (Or.inl hxp),?_⟩,hx⟩
    intro z hz
    rcases (hc z).mpr hz with hp | hq
    · exact hxm z hp
    · have hh := hym z hq; dsimp only at hh ⊢; omega
  · rw [max_eq_right (by omega : a ≤ b)]
    refine ⟨y,⟨(hc y).mp (Or.inr hyq),?_⟩,hy⟩
    intro z hz
    rcases (hc z).mpr hz with hp | hq
    · have hh := hxm z hp; dsimp only at hh ⊢; omega
    · exact hym z hq

theorem RangeMaxValue_join_max (l : List Int) (i j half a b : Int) (hj : 1 ≤ j)
    (hh : half = Power2 (j-1)) (hl : RangeMaxValue l i (i+Power2 (j-1)) a)
    (hr : RangeMaxValue l (i+half) (i+half+Power2 (j-1)) b) :
    RangeMaxValue l i (i+Power2 j) (max a b) := by
  have hd := Power2_sub1_double j hj
  have hp := Power2_pos j (by omega)
  refine ⟨hl.1,by omega,by have := hr.2.2.1; omega,?_⟩
  apply max_union_cover (fun k => Znth k l 0) a b hl.2.2.2 hr.2.2.2
  intro x
  constructor
  · intro hx; rcases hx with hx | hx <;> omega
  · intro hx
    by_cases hlt : x < i+half
    · left; omega
    · right; omega

theorem RangeMaxValue_join_left (l : List Int) (i j half a b : Int) (hj : 1 ≤ j)
    (hh : half = Power2 (j-1)) (hab : a ≥ b) (hl : RangeMaxValue l i (i+Power2 (j-1)) a)
    (hr : RangeMaxValue l (i+half) (i+half+Power2 (j-1)) b) : RangeMaxValue l i (i+Power2 j) a := by
  simpa only [max_eq_left hab] using RangeMaxValue_join_max l i j half a b hj hh hl hr

theorem RangeMaxValue_join_right (l : List Int) (i j half a b : Int) (hj : 1 ≤ j)
    (hh : half = Power2 (j-1)) (hab : a < b) (hl : RangeMaxValue l i (i+Power2 (j-1)) a)
    (hr : RangeMaxValue l (i+half) (i+half+Power2 (j-1)) b) : RangeMaxValue l i (i+Power2 j) b := by
  simpa only [max_eq_right (le_of_lt hab)] using RangeMaxValue_join_max l i j half a b hj hh hl hr

theorem STCellRangeMax_extend_by_left_max (l st : List Int) (K i j half a b : Int)
    (hj : 1 ≤ j) (hh : half = Power2 (j-1)) (hi : 0 ≤ i*K+j ∧ i*K+j < Zlength st)
    (ha : a = Znth (i*K+(j-1)) st 0) (hb : b = Znth ((i+half)*K+(j-1)) st 0)
    (hab : a ≥ b) (hl : STCellRangeMax l st K i (j-1)) (hr : STCellRangeMax l st K (i+half) (j-1)) :
    STCellRangeMax l (replace_Znth (i*K+j) a st) K i j := by
  unfold STCellRangeMax at hl hr ⊢
  rw [← ha] at hl
  rw [← hb] at hr
  rw [Znth_replace_Znth_Same 0 st (i*K+j) a hi]
  exact RangeMaxValue_join_left l i j half a b hj hh hab hl hr

theorem STLevelPrefix_extend_by_left_max (l st : List Int) (K n j i half a b : Int)
    (hj : 1 ≤ j) (hjK : j < K) (hh : half = Power2 (j-1)) (hi : 0 ≤ i*K+j ∧ i*K+j < Zlength st)
    (ha : a = Znth (i*K+(j-1)) st 0) (hb : b = Znth ((i+half)*K+(j-1)) st 0)
    (hab : a ≥ b) (hpref : STLevelPrefix l st K n j i)
    (hl : STCellRangeMax l st K i (j-1)) (hr : STCellRangeMax l st K (i+half) (j-1)) :
    STLevelPrefix l (replace_Znth (i*K+j) a st) K n j (i+1) := by
  intro row hrow
  by_cases he : row = i
  · rw [he]
    exact STCellRangeMax_extend_by_left_max l st K i j half a b hj hh hi ha hb hab hl hr
  · have hri : row < i := by omega
    exact STCellRangeMax_replace_other l st K row j (i*K+j) a
      (hpref row ⟨hrow.1,hri,hrow.2.2⟩) hi ⟨by nlinarith [hrow.1],by nlinarith⟩
      (cell_index_same_col_neq i row K j (by omega) (Ne.symm he))

theorem STCellRangeMax_extend_by_right_max (l st : List Int) (K i j half a b : Int)
    (hj : 1 ≤ j) (hh : half = Power2 (j-1)) (hi : 0 ≤ i*K+j ∧ i*K+j < Zlength st)
    (ha : a = Znth (i*K+(j-1)) st 0) (hb : b = Znth ((i+half)*K+(j-1)) st 0)
    (hab : a < b) (hl : STCellRangeMax l st K i (j-1)) (hr : STCellRangeMax l st K (i+half) (j-1)) :
    STCellRangeMax l (replace_Znth (i*K+j) b st) K i j := by
  unfold STCellRangeMax at hl hr ⊢
  rw [← ha] at hl
  rw [← hb] at hr
  rw [Znth_replace_Znth_Same 0 st (i*K+j) b hi]
  exact RangeMaxValue_join_right l i j half a b hj hh hab hl hr

theorem STLevelPrefix_extend_by_right_max (l st : List Int) (K n j i half a b : Int)
    (hj : 1 ≤ j) (hjK : j < K) (hh : half = Power2 (j-1)) (hi : 0 ≤ i*K+j ∧ i*K+j < Zlength st)
    (ha : a = Znth (i*K+(j-1)) st 0) (hb : b = Znth ((i+half)*K+(j-1)) st 0)
    (hab : a < b) (hpref : STLevelPrefix l st K n j i)
    (hl : STCellRangeMax l st K i (j-1)) (hr : STCellRangeMax l st K (i+half) (j-1)) :
    STLevelPrefix l (replace_Znth (i*K+j) b st) K n j (i+1) := by
  intro row hrow
  by_cases he : row = i
  · rw [he]
    exact STCellRangeMax_extend_by_right_max l st K i j half a b hj hh hi ha hb hab hl hr
  · have hri : row < i := by omega
    exact STCellRangeMax_replace_other l st K row j (i*K+j) b
      (hpref row ⟨hrow.1,hri,hrow.2.2⟩) hi ⟨by nlinarith [hrow.1],by nlinarith⟩
      (cell_index_same_col_neq i row K j (by omega) (Ne.symm he))

theorem STLevelPrefix_exit_to_built_step (l st_ls : List Int) (K n j upto len : Int)
    (hb : STBuiltBeforeLevel l st_ls K n j) (hp : STLevelPrefix l st_ls K n j upto)
    (he : len = Power2 j) (hex : upto+len > n) : STBuiltBeforeLevel l st_ls K n (j+1) := by
  intro p q hc
  by_cases hq : q < j
  · exact hb p q ⟨hc.1,hc.2.1,hq,hc.2.2.2⟩
  · have heq : q = j := by omega
    subst q
    exact hp p ⟨hc.1,by omega,hc.2.2.2⟩

theorem Power2_step_query (k : Int) (hk : 0 ≤ k) : Power2 (k+1) = Power2 k*2 :=
  (Power2_step k hk).symm

theorem QueryLogBounds_init (K n left right : Int) (hn : 1 ≤ n) (hK : 1 ≤ K)
    (hp : n < Power2 K) (hl : 0 ≤ left) (hlr : left ≤ right) (hr : right < n) :
    QueryLogBounds K n (right-left+1) 0 1 := ⟨by omega,by omega,hK,hp,by omega,by omega,by omega⟩

theorem QueryLogLoopState_init (left right : Int) (hl : 0 ≤ left) (hlr : left ≤ right) :
    QueryLogLoopState (right-left+1) 0 1 := ⟨by omega,rfl,by rw [worker_Power2_0_1]; omega⟩

theorem QueryLogBounds_step (K n len k pow : Int) (hp : pow*2 ≤ len)
    (hb : QueryLogBounds K n len k pow) (hs : QueryLogLoopState len k pow) :
    QueryLogBounds K n len (k+1) (pow*2) := by
  obtain ⟨hln,hll,hK,hn,hk,hkK,hpow⟩ := hb
  have hnext : Power2 (k+1) ≤ len := by rw [Power2_step_query k hk,← hs.2.1]; exact hp
  have hknew : k+1 < K := by
    by_contra hnot
    have he : k+1 = K := by omega
    rw [he] at hnext; omega
  exact ⟨hln,hll,hK,hn,by omega,hknew,by omega⟩

theorem QueryLogLoopState_step (len k pow : Int) (hp : pow*2 ≤ len)
    (hs : QueryLogLoopState len k pow) : QueryLogLoopState len (k+1) (pow*2) := by
  exact ⟨by have := hs.1; omega,by rw [Power2_step_query k hs.1,← hs.2.1],
    by rw [Power2_step_query k hs.1,← hs.2.1]; exact hp⟩

theorem RangeMaxValue_sparse_query_max (l st_l : List Int) (K n len left right j pow a b : Int)
    (hlen : len = right-left+1) (ha : a = Znth (left*K+j) st_l 0)
    (hb : b = Znth ((right-pow+1)*K+j) st_l 0) (hq : QueryLogFinalState len j pow)
    (hcl : STCellRangeMax l st_l K left j) (hcr : STCellRangeMax l st_l K (right-pow+1) j) :
    RangeMaxValue l left (right+1) (max a b) := by
  obtain ⟨⟨hj,hpow,hpowle⟩,hnext⟩ := hq
  have hd : Power2 (j+1) = 2*pow := by rw [Power2_step_query j hj,← hpow]; ring
  unfold STCellRangeMax at hcl hcr
  rw [← ha,← hpow] at hcl
  rw [← hb,← hpow] at hcr
  have hright : right-pow+1+pow = right+1 := by omega
  rw [hright] at hcr
  refine ⟨hcl.1,by have := hcl.2.1; omega,hcr.2.2.1,?_⟩
  apply max_union_cover (fun k => Znth k l 0) a b hcl.2.2.2 hcr.2.2.2
  intro x
  constructor
  · intro hx; rcases hx with hx | hx <;> omega
  · intro hx
    by_cases hlt : x < left+pow
    · left; omega
    · right; omega

theorem RangeMaxValue_sparse_query_left (l st_l : List Int) (K n len left right j pow a b : Int)
    (hlen : len = right-left+1) (ha : a = Znth (left*K+j) st_l 0)
    (hb : b = Znth ((right-pow+1)*K+j) st_l 0) (hq : QueryLogFinalState len j pow)
    (hcl : STCellRangeMax l st_l K left j) (hcr : STCellRangeMax l st_l K (right-pow+1) j) (hab : a ≥ b) :
    RangeMaxValue l left (right+1) a := by
  simpa only [max_eq_left hab] using RangeMaxValue_sparse_query_max l st_l K n len left right j pow a b hlen ha hb hq hcl hcr

theorem RangeMaxValue_sparse_query_right (l st_l : List Int) (K n len left right j pow a b : Int)
    (hlen : len = right-left+1) (ha : a = Znth (left*K+j) st_l 0)
    (hb : b = Znth ((right-pow+1)*K+j) st_l 0) (hq : QueryLogFinalState len j pow)
    (hcl : STCellRangeMax l st_l K left j) (hcr : STCellRangeMax l st_l K (right-pow+1) j) (hab : a < b) :
    RangeMaxValue l left (right+1) b := by
  simpa only [max_eq_right (le_of_lt hab)] using RangeMaxValue_sparse_query_max l st_l K n len left right j pow a b hlen ha hb hq hcl hcr

end ProofSupport

open ProofSupport
open Algorithms.rmq.lean.groundtruth.rmq_goal

open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open Algorithms.rmq.lean.groundtruth.rmq_goal
open ProofSupport
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

theorem proof_of_build_safety_wit_2_split_goal_1 : build_safety_wit_2_split_goal_1 := by
  unfold build_safety_wit_2_split_goal_1
  intro st_pre K_pre n_pre arr_pre l idx st_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_2_split_goal_2 : build_safety_wit_2_split_goal_2 := by
  unfold build_safety_wit_2_split_goal_2
  intro st_pre K_pre n_pre arr_pre l idx st_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_4_split_goal_1 : build_safety_wit_4_split_goal_1 := by
  unfold build_safety_wit_4_split_goal_1
  intro st_pre K_pre n_pre arr_pre l idx st_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_4_split_goal_2 : build_safety_wit_4_split_goal_2 := by
  unfold build_safety_wit_4_split_goal_2
  intro st_pre K_pre n_pre arr_pre l idx st_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_6_split_goal_1 : build_safety_wit_6_split_goal_1 := by
  unfold build_safety_wit_6_split_goal_1
  intro st_pre K_pre n_pre arr_pre l st_l i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_6_split_goal_2 : build_safety_wit_6_split_goal_2 := by
  unfold build_safety_wit_6_split_goal_2
  intro st_pre K_pre n_pre arr_pre l st_l i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_12_split_goal_1 : build_safety_wit_12_split_goal_1 := by
  unfold build_safety_wit_12_split_goal_1
  intro st_pre K_pre n_pre arr_pre l i len half j st_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_12_split_goal_2 : build_safety_wit_12_split_goal_2 := by
  unfold build_safety_wit_12_split_goal_2
  intro st_pre K_pre n_pre arr_pre l i len half j st_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_13_split_goal_1 : build_safety_wit_13_split_goal_1 := by
  unfold build_safety_wit_13_split_goal_1
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_13_split_goal_2 : build_safety_wit_13_split_goal_2 := by
  unfold build_safety_wit_13_split_goal_2
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_14_split_goal_1 : build_safety_wit_14_split_goal_1 := by
  unfold build_safety_wit_14_split_goal_1
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_14_split_goal_2 : build_safety_wit_14_split_goal_2 := by
  unfold build_safety_wit_14_split_goal_2
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_15_split_goal_1 : build_safety_wit_15_split_goal_1 := by
  unfold build_safety_wit_15_split_goal_1
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_15_split_goal_2 : build_safety_wit_15_split_goal_2 := by
  unfold build_safety_wit_15_split_goal_2
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_17_split_goal_1 : build_safety_wit_17_split_goal_1 := by
  unfold build_safety_wit_17_split_goal_1
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_17_split_goal_2 : build_safety_wit_17_split_goal_2 := by
  unfold build_safety_wit_17_split_goal_2
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_18_split_goal_1 : build_safety_wit_18_split_goal_1 := by
  unfold build_safety_wit_18_split_goal_1
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_18_split_goal_2 : build_safety_wit_18_split_goal_2 := by
  unfold build_safety_wit_18_split_goal_2
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_19_split_goal_1 : build_safety_wit_19_split_goal_1 := by
  unfold build_safety_wit_19_split_goal_1
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_19_split_goal_2 : build_safety_wit_19_split_goal_2 := by
  unfold build_safety_wit_19_split_goal_2
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_20_split_goal_1 : build_safety_wit_20_split_goal_1 := by
  unfold build_safety_wit_20_split_goal_1
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_20_split_goal_2 : build_safety_wit_20_split_goal_2 := by
  unfold build_safety_wit_20_split_goal_2
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_22_split_goal_1 : build_safety_wit_22_split_goal_1 := by
  unfold build_safety_wit_22_split_goal_1
  intro st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_22_split_goal_2 : build_safety_wit_22_split_goal_2 := by
  unfold build_safety_wit_22_split_goal_2
  intro st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_23_split_goal_1 : build_safety_wit_23_split_goal_1 := by
  unfold build_safety_wit_23_split_goal_1
  intro st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_23_split_goal_2 : build_safety_wit_23_split_goal_2 := by
  unfold build_safety_wit_23_split_goal_2
  intro st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_24_split_goal_1 : build_safety_wit_24_split_goal_1 := by
  unfold build_safety_wit_24_split_goal_1
  intro st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_24_split_goal_2 : build_safety_wit_24_split_goal_2 := by
  unfold build_safety_wit_24_split_goal_2
  intro st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_25_split_goal_1 : build_safety_wit_25_split_goal_1 := by
  unfold build_safety_wit_25_split_goal_1
  intro st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_25_split_goal_2 : build_safety_wit_25_split_goal_2 := by
  unfold build_safety_wit_25_split_goal_2
  intro st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_26_split_goal_1 : build_safety_wit_26_split_goal_1 := by
  unfold build_safety_wit_26_split_goal_1
  intro st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_26_split_goal_2 : build_safety_wit_26_split_goal_2 := by
  unfold build_safety_wit_26_split_goal_2
  intro st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_27_split_goal_1 : build_safety_wit_27_split_goal_1 := by
  unfold build_safety_wit_27_split_goal_1
  intro st_pre K_pre n_pre arr_pre l st_l j half len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_27_split_goal_2 : build_safety_wit_27_split_goal_2 := by
  unfold build_safety_wit_27_split_goal_2
  intro st_pre K_pre n_pre arr_pre l st_l j half len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_entail_wit_1_split_goal_1 : build_entail_wit_1_split_goal_1 := by
  unfold build_entail_wit_1_split_goal_1
  intro K_pre n_pre st0 l PreH1 PreH2 PreH3
  intro p hp
  omega

theorem proof_of_build_entail_wit_1_split_goal_2 : build_entail_wit_1_split_goal_2 := by
  unfold build_entail_wit_1_split_goal_2
  intro K_pre n_pre st0 l PreH1 PreH2 PreH3
  exact ⟨le_refl _,Zlength_nonneg st0⟩

theorem proof_of_build_entail_wit_1_split_goal_3 : build_entail_wit_1_split_goal_3 := by
  unfold build_entail_wit_1_split_goal_3
  intro K_pre n_pre st0 l PreH1 PreH2 PreH3
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_entail_wit_2_split_goal_1 : build_entail_wit_2_split_goal_1 := by
  unfold build_entail_wit_2_split_goal_1
  intro K_pre n_pre l idx st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  apply STZeroPrefix_replace_zero_step st_l_2 idx PreH8
  omega

theorem proof_of_build_entail_wit_2_split_goal_2 : build_entail_wit_2_split_goal_2 := by
  unfold build_entail_wit_2_split_goal_2
  intro K_pre n_pre l idx st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_entail_wit_2_split_goal_3 : build_entail_wit_2_split_goal_3 := by
  unfold build_entail_wit_2_split_goal_3
  intro K_pre n_pre l idx st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_entail_wit_3_split_goal_1 : build_entail_wit_3_split_goal_1 := by
  unfold build_entail_wit_3_split_goal_1
  intro K_pre n_pre l idx st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have he : idx = n_pre*K_pre := by omega
  exact he ▸ PreH8

theorem proof_of_build_entail_wit_3_split_goal_2 : build_entail_wit_3_split_goal_2 := by
  unfold build_entail_wit_3_split_goal_2
  intro K_pre n_pre l idx st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have he : idx = n_pre*K_pre := by omega
  exact he ▸ PreH7

theorem proof_of_build_entail_wit_4_split_goal_1 : build_entail_wit_4_split_goal_1 := by
  unfold build_entail_wit_4_split_goal_1
  intro K_pre n_pre l st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5
  intro i hi
  omega

theorem proof_of_build_entail_wit_4_split_goal_2 : build_entail_wit_4_split_goal_2 := by
  unfold build_entail_wit_4_split_goal_2
  intro K_pre n_pre l st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_entail_wit_5_split_goal_1 : build_entail_wit_5_split_goal_1 := by
  unfold build_entail_wit_5_split_goal_1
  intro K_pre n_pre l i st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_entail_wit_5_split_goal_2 : build_entail_wit_5_split_goal_2 := by
  unfold build_entail_wit_5_split_goal_2
  intro K_pre n_pre l i st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_entail_wit_5_split_goal_3 : build_entail_wit_5_split_goal_3 := by
  unfold build_entail_wit_5_split_goal_3
  intro K_pre n_pre l i st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_entail_wit_5_split_goal_4 : build_entail_wit_5_split_goal_4 := by
  unfold build_entail_wit_5_split_goal_4
  intro K_pre n_pre l i st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_entail_wit_6_split_goal_1 : build_entail_wit_6_split_goal_1 := by
  unfold build_entail_wit_6_split_goal_1
  intro K_pre n_pre l st_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  apply worker_STBasePrefix_write_base_step l st_l_2 K_pre n_pre i <;> first | assumption | omega | nlinarith

theorem proof_of_build_entail_wit_6_split_goal_2 : build_entail_wit_6_split_goal_2 := by
  unfold build_entail_wit_6_split_goal_2
  intro K_pre n_pre l st_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_entail_wit_6_split_goal_3 : build_entail_wit_6_split_goal_3 := by
  unfold build_entail_wit_6_split_goal_3
  intro K_pre n_pre l st_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_entail_wit_8_split_goal_1 : build_entail_wit_8_split_goal_1 := by
  unfold build_entail_wit_8_split_goal_1
  intro K_pre n_pre l i st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  apply worker_STBasePrefix_complete_level1 l st_l_2 K_pre n_pre i <;> first | assumption | omega

theorem proof_of_build_entail_wit_8_split_goal_2 : build_entail_wit_8_split_goal_2 := by
  unfold build_entail_wit_8_split_goal_2
  intro K_pre n_pre l i st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_entail_wit_9_split_goal_1 : build_entail_wit_9_split_goal_1 := by
  unfold build_entail_wit_9_split_goal_1
  intro K_pre n_pre l st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5
  rfl

theorem proof_of_build_entail_wit_9_split_goal_2 : build_entail_wit_9_split_goal_2 := by
  unfold build_entail_wit_9_split_goal_2
  intro K_pre n_pre l st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5
  rfl

theorem proof_of_build_entail_wit_9_split_goal_3 : build_entail_wit_9_split_goal_3 := by
  unfold build_entail_wit_9_split_goal_3
  intro K_pre n_pre l st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_entail_wit_10_split_goal_1 : build_entail_wit_10_split_goal_1 := by
  unfold build_entail_wit_10_split_goal_1
  intro K_pre n_pre l len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  intro i hi
  omega

theorem proof_of_build_entail_wit_10_split_goal_2 : build_entail_wit_10_split_goal_2 := by
  unfold build_entail_wit_10_split_goal_2
  intro K_pre n_pre l len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_entail_wit_11_split_goal_1 : build_entail_wit_11_split_goal_1 := by
  unfold build_entail_wit_11_split_goal_1
  intro K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  have hd := Power2_sub1_double j (by omega)
  apply PreH11
  (repeat' constructor) <;> nlinarith

theorem proof_of_build_entail_wit_11_split_goal_2 : build_entail_wit_11_split_goal_2 := by
  unfold build_entail_wit_11_split_goal_2
  intro K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  have hd := Power2_sub1_double j (by omega)
  apply PreH11
  (repeat' constructor) <;> nlinarith

theorem proof_of_build_entail_wit_11_split_goal_3 : build_entail_wit_11_split_goal_3 := by
  unfold build_entail_wit_11_split_goal_3
  intro K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  have hd := Power2_sub1_double j (by omega)
  (repeat' constructor) <;> nlinarith

theorem proof_of_build_entail_wit_11_split_goal_4 : build_entail_wit_11_split_goal_4 := by
  unfold build_entail_wit_11_split_goal_4
  intro K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  have hd := Power2_sub1_double j (by omega)
  (repeat' constructor) <;> nlinarith

theorem proof_of_build_entail_wit_11_split_goal_5 : build_entail_wit_11_split_goal_5 := by
  unfold build_entail_wit_11_split_goal_5
  intro K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  have hd := Power2_sub1_double j (by omega)
  (repeat' constructor) <;> nlinarith

theorem proof_of_build_entail_wit_11_split_goal_6 : build_entail_wit_11_split_goal_6 := by
  unfold build_entail_wit_11_split_goal_6
  intro K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  have hd := Power2_sub1_double j (by omega)
  (repeat' constructor) <;> nlinarith

theorem proof_of_build_entail_wit_11_split_goal_7 : build_entail_wit_11_split_goal_7 := by
  unfold build_entail_wit_11_split_goal_7
  intro K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  have hd := Power2_sub1_double j (by omega)
  (repeat' constructor) <;> nlinarith

theorem proof_of_build_entail_wit_11_split_goal_8 : build_entail_wit_11_split_goal_8 := by
  unfold build_entail_wit_11_split_goal_8
  intro K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  have hd := Power2_sub1_double j (by omega)
  (repeat' constructor) <;> nlinarith

theorem proof_of_build_entail_wit_11_split_goal_9 : build_entail_wit_11_split_goal_9 := by
  unfold build_entail_wit_11_split_goal_9
  intro K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  have hd := Power2_sub1_double j (by omega)
  (repeat' constructor) <;> nlinarith

theorem proof_of_build_entail_wit_11_split_goal_10 : build_entail_wit_11_split_goal_10 := by
  unfold build_entail_wit_11_split_goal_10
  intro K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  have hd := Power2_sub1_double j (by omega)
  (repeat' constructor) <;> nlinarith

theorem proof_of_build_entail_wit_11_split_goal_11 : build_entail_wit_11_split_goal_11 := by
  unfold build_entail_wit_11_split_goal_11
  intro K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  have hd := Power2_sub1_double j (by omega)
  (repeat' constructor) <;> nlinarith

theorem proof_of_build_entail_wit_11_split_goal_12 : build_entail_wit_11_split_goal_12 := by
  unfold build_entail_wit_11_split_goal_12
  intro K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  have hd := Power2_sub1_double j (by omega)
  (repeat' constructor) <;> nlinarith

theorem proof_of_build_entail_wit_13_1_split_goal_1 : build_entail_wit_13_1_split_goal_1 := by
  unfold build_entail_wit_13_1_split_goal_1
  intro K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  apply STLevelPrefix_extend_by_left_max l st_l_2 K_pre n_pre j i half a b
  all_goals first | assumption | omega | (simpa only [Int.add_sub_assoc] using PreH17) | (simpa only [Int.add_sub_assoc] using PreH18)

theorem proof_of_build_entail_wit_13_1_split_goal_2 : build_entail_wit_13_1_split_goal_2 := by
  unfold build_entail_wit_13_1_split_goal_2
  intro K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  apply STBuiltBeforeLevel_replace_level_cell l st_l_2 K_pre n_pre j i
  · exact PreH24
  · exact PreH6
  · constructor <;> omega
  · intro row col hc
    have hp := Power2_pos col hc.2.1
    constructor <;> nlinarith [hc.1,hc.2.1,hc.2.2.1,hc.2.2.2]

theorem proof_of_build_entail_wit_13_1_split_goal_3 : build_entail_wit_13_1_split_goal_3 := by
  unfold build_entail_wit_13_1_split_goal_3
  intro K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  (repeat' constructor) <;> nlinarith

theorem proof_of_build_entail_wit_13_1_split_goal_4 : build_entail_wit_13_1_split_goal_4 := by
  unfold build_entail_wit_13_1_split_goal_4
  intro K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  rw [Znth_replace_Znth_Diff 0 st_l_2 (i*K_pre+j) ((i+half)*K_pre+j-1) a ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by nlinarith)]
  exact PreH18

theorem proof_of_build_entail_wit_13_1_split_goal_5 : build_entail_wit_13_1_split_goal_5 := by
  unfold build_entail_wit_13_1_split_goal_5
  intro K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  rw [Znth_replace_Znth_Diff 0 st_l_2 (i*K_pre+j) (i*K_pre+j-1) a ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by nlinarith)]
  exact PreH17

theorem proof_of_build_entail_wit_13_1_split_goal_6 : build_entail_wit_13_1_split_goal_6 := by
  unfold build_entail_wit_13_1_split_goal_6
  intro K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  rw [Zlength_replace_Znth]
  exact PreH4

theorem proof_of_build_entail_wit_13_2_split_goal_1 : build_entail_wit_13_2_split_goal_1 := by
  unfold build_entail_wit_13_2_split_goal_1
  intro K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  apply STLevelPrefix_extend_by_right_max l st_l_2 K_pre n_pre j i half a b
  all_goals first | assumption | omega | (simpa only [Int.add_sub_assoc] using PreH17) | (simpa only [Int.add_sub_assoc] using PreH18)

theorem proof_of_build_entail_wit_13_2_split_goal_2 : build_entail_wit_13_2_split_goal_2 := by
  unfold build_entail_wit_13_2_split_goal_2
  intro K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  apply STBuiltBeforeLevel_replace_level_cell l st_l_2 K_pre n_pre j i
  · exact PreH24
  · exact PreH6
  · constructor <;> omega
  · intro row col hc
    have hp := Power2_pos col hc.2.1
    constructor <;> nlinarith [hc.1,hc.2.1,hc.2.2.1,hc.2.2.2]

theorem proof_of_build_entail_wit_13_2_split_goal_3 : build_entail_wit_13_2_split_goal_3 := by
  unfold build_entail_wit_13_2_split_goal_3
  intro K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  (repeat' constructor) <;> nlinarith

theorem proof_of_build_entail_wit_13_2_split_goal_4 : build_entail_wit_13_2_split_goal_4 := by
  unfold build_entail_wit_13_2_split_goal_4
  intro K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  rw [Znth_replace_Znth_Diff 0 st_l_2 (i*K_pre+j) ((i+half)*K_pre+j-1) b ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by nlinarith)]
  exact PreH18

theorem proof_of_build_entail_wit_13_2_split_goal_5 : build_entail_wit_13_2_split_goal_5 := by
  unfold build_entail_wit_13_2_split_goal_5
  intro K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  rw [Znth_replace_Znth_Diff 0 st_l_2 (i*K_pre+j) (i*K_pre+j-1) b ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by nlinarith)]
  exact PreH17

theorem proof_of_build_entail_wit_13_2_split_goal_6 : build_entail_wit_13_2_split_goal_6 := by
  unfold build_entail_wit_13_2_split_goal_6
  intro K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  rw [Zlength_replace_Znth]
  exact PreH4

theorem proof_of_build_entail_wit_15_split_goal_1 : build_entail_wit_15_split_goal_1 := by
  unfold build_entail_wit_15_split_goal_1
  intro K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  apply STLevelPrefix_exit_to_built_step l st_l_2 K_pre n_pre j i len <;> assumption

theorem proof_of_build_entail_wit_15_split_goal_2 : build_entail_wit_15_split_goal_2 := by
  unfold build_entail_wit_15_split_goal_2
  intro K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_entail_wit_16_split_goal_1 : build_entail_wit_16_split_goal_1 := by
  unfold build_entail_wit_16_split_goal_1
  intro K_pre n_pre l st_l_2 j half len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  rw [PreH7]
  exact Power2_step j (by omega)

theorem proof_of_build_entail_wit_16_split_goal_2 : build_entail_wit_16_split_goal_2 := by
  unfold build_entail_wit_16_split_goal_2
  intro K_pre n_pre l st_l_2 j half len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  simpa only [show j+1-1 = j by omega] using PreH7

theorem proof_of_build_return_wit_1_split_goal_1 : build_return_wit_1_split_goal_1 := by
  unfold build_return_wit_1_split_goal_1
  intro K_pre n_pre l len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have he : j = K_pre := by omega
  exact he ▸ PreH10

theorem proof_of_build_return_wit_1_split_goal_2 : build_return_wit_1_split_goal_2 := by
  unfold build_return_wit_1_split_goal_2
  intro K_pre n_pre l len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have he : j = K_pre := by omega
  exact he ▸ PreH9

theorem proof_of_query_safety_wit_1_split_goal_1 : query_safety_wit_1_split_goal_1 := by
  unfold query_safety_wit_1_split_goal_1
  intro right_pre left_pre K_pre n_pre st_pre st_l l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_1_split_goal_2 : query_safety_wit_1_split_goal_2 := by
  unfold query_safety_wit_1_split_goal_2
  intro right_pre left_pre K_pre n_pre st_pre st_l l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_2_split_goal_1 : query_safety_wit_2_split_goal_1 := by
  unfold query_safety_wit_2_split_goal_1
  intro right_pre left_pre K_pre n_pre st_pre st_l l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_2_split_goal_2 : query_safety_wit_2_split_goal_2 := by
  unfold query_safety_wit_2_split_goal_2
  intro right_pre left_pre K_pre n_pre st_pre st_l l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_6_split_goal_1 : query_safety_wit_6_split_goal_1 := by
  unfold query_safety_wit_6_split_goal_1
  intro right_pre left_pre K_pre n_pre st_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try have hpb := worker_Power2_double_int_bound_30 k K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_6_split_goal_2 : query_safety_wit_6_split_goal_2 := by
  unfold query_safety_wit_6_split_goal_2
  intro right_pre left_pre K_pre n_pre st_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try have hpb := worker_Power2_double_int_bound_30 k K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_8_split_goal_1 : query_safety_wit_8_split_goal_1 := by
  unfold query_safety_wit_8_split_goal_1
  intro right_pre left_pre K_pre n_pre st_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try have hpb := worker_Power2_double_int_bound_30 k K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_8_split_goal_2 : query_safety_wit_8_split_goal_2 := by
  unfold query_safety_wit_8_split_goal_2
  intro right_pre left_pre K_pre n_pre st_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try have hpb := worker_Power2_double_int_bound_30 k K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_10_split_goal_1 : query_safety_wit_10_split_goal_1 := by
  unfold query_safety_wit_10_split_goal_1
  intro right_pre left_pre K_pre n_pre st_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try have hpb := worker_Power2_double_int_bound_30 k K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_10_split_goal_2 : query_safety_wit_10_split_goal_2 := by
  unfold query_safety_wit_10_split_goal_2
  intro right_pre left_pre K_pre n_pre st_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try have hpb := worker_Power2_double_int_bound_30 k K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_11_split_goal_1 : query_safety_wit_11_split_goal_1 := by
  unfold query_safety_wit_11_split_goal_1
  intro right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try have hpb := worker_Power2_double_int_bound_30 k K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_11_split_goal_2 : query_safety_wit_11_split_goal_2 := by
  unfold query_safety_wit_11_split_goal_2
  intro right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try have hpb := worker_Power2_double_int_bound_30 k K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_12_split_goal_1 : query_safety_wit_12_split_goal_1 := by
  unfold query_safety_wit_12_split_goal_1
  intro right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try have hpb := worker_Power2_double_int_bound_30 k K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_12_split_goal_2 : query_safety_wit_12_split_goal_2 := by
  unfold query_safety_wit_12_split_goal_2
  intro right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try have hpb := worker_Power2_double_int_bound_30 k K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_13_split_goal_1 : query_safety_wit_13_split_goal_1 := by
  unfold query_safety_wit_13_split_goal_1
  intro right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try have hpb := worker_Power2_double_int_bound_30 k K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_13_split_goal_2 : query_safety_wit_13_split_goal_2 := by
  unfold query_safety_wit_13_split_goal_2
  intro right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try have hpb := worker_Power2_double_int_bound_30 k K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_14_split_goal_1 : query_safety_wit_14_split_goal_1 := by
  unfold query_safety_wit_14_split_goal_1
  intro right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try have hpb := worker_Power2_double_int_bound_30 k K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_14_split_goal_2 : query_safety_wit_14_split_goal_2 := by
  unfold query_safety_wit_14_split_goal_2
  intro right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try have hpb := worker_Power2_double_int_bound_30 k K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_15_split_goal_1 : query_safety_wit_15_split_goal_1 := by
  unfold query_safety_wit_15_split_goal_1
  intro right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try have hpb := worker_Power2_double_int_bound_30 k K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_15_split_goal_2 : query_safety_wit_15_split_goal_2 := by
  unfold query_safety_wit_15_split_goal_2
  intro right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try have hpb := worker_Power2_double_int_bound_30 k K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_16_split_goal_1 : query_safety_wit_16_split_goal_1 := by
  unfold query_safety_wit_16_split_goal_1
  intro right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try have hpb := worker_Power2_double_int_bound_30 k K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_16_split_goal_2 : query_safety_wit_16_split_goal_2 := by
  unfold query_safety_wit_16_split_goal_2
  intro right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try have hpb := worker_Power2_double_int_bound_30 k K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_entail_wit_1_split_goal_1 : query_entail_wit_1_split_goal_1 := by
  unfold query_entail_wit_1_split_goal_1
  intro right_pre left_pre K_pre n_pre st_l l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  apply QueryLogLoopState_init <;> omega

theorem proof_of_query_entail_wit_1_split_goal_2 : query_entail_wit_1_split_goal_2 := by
  unfold query_entail_wit_1_split_goal_2
  intro right_pre left_pre K_pre n_pre st_l l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  apply QueryLogBounds_init <;> omega

theorem proof_of_query_entail_wit_2_split_goal_1 : query_entail_wit_2_split_goal_1 := by
  unfold query_entail_wit_2_split_goal_1
  intro right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  rw [← PreH4]
  apply QueryLogLoopState_step <;> assumption

theorem proof_of_query_entail_wit_2_split_goal_2 : query_entail_wit_2_split_goal_2 := by
  unfold query_entail_wit_2_split_goal_2
  intro right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  rw [← PreH4]
  apply QueryLogBounds_step <;> assumption

theorem proof_of_query_entail_wit_3_split_goal_1 : query_entail_wit_3_split_goal_1 := by
  unfold query_entail_wit_3_split_goal_1
  intro right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  apply PreH8
  (repeat' constructor) <;> omega

theorem proof_of_query_entail_wit_3_split_goal_2 : query_entail_wit_3_split_goal_2 := by
  unfold query_entail_wit_3_split_goal_2
  intro right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  apply PreH8
  (repeat' constructor) <;> omega

theorem proof_of_query_entail_wit_3_split_goal_3 : query_entail_wit_3_split_goal_3 := by
  unfold query_entail_wit_3_split_goal_3
  intro right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_entail_wit_3_split_goal_4 : query_entail_wit_3_split_goal_4 := by
  unfold query_entail_wit_3_split_goal_4
  intro right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_entail_wit_3_split_goal_5 : query_entail_wit_3_split_goal_5 := by
  unfold query_entail_wit_3_split_goal_5
  intro right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_entail_wit_3_split_goal_6 : query_entail_wit_3_split_goal_6 := by
  unfold query_entail_wit_3_split_goal_6
  intro right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_entail_wit_3_split_goal_7 : query_entail_wit_3_split_goal_7 := by
  unfold query_entail_wit_3_split_goal_7
  intro right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_entail_wit_3_split_goal_8 : query_entail_wit_3_split_goal_8 := by
  unfold query_entail_wit_3_split_goal_8
  intro right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_entail_wit_3_split_goal_9 : query_entail_wit_3_split_goal_9 := by
  unfold query_entail_wit_3_split_goal_9
  intro right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  rw [← PreH4]
  refine ⟨PreH10,?_⟩
  have hd := Power2_step_query k PreH10.1
  have hp := PreH10.2.1
  omega

theorem proof_of_query_entail_wit_5_split_goal_1 : query_entail_wit_5_split_goal_1 := by
  unfold query_entail_wit_5_split_goal_1
  intro right_pre left_pre K_pre n_pre st_l l len a k b pow PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  apply RangeMaxValue_sparse_query_left l st_l K_pre n_pre len left_pre right_pre k pow a b <;> assumption

theorem proof_of_query_entail_wit_6_split_goal_1 : query_entail_wit_6_split_goal_1 := by
  unfold query_entail_wit_6_split_goal_1
  intro right_pre left_pre K_pre n_pre st_l l len a k b pow PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  apply RangeMaxValue_sparse_query_right l st_l K_pre n_pre len left_pre right_pre k pow a b <;> assumption

theorem proof_of_build_safety_wit_2 : build_safety_wit_2 := by
  unfold build_safety_wit_2
  right
  intro st_pre K_pre n_pre arr_pre l idx st_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  split_pures
  all_goals first
    | exact (proof_of_build_safety_wit_2_split_goal_1 st_pre K_pre n_pre arr_pre l idx st_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7)
    | exact (proof_of_build_safety_wit_2_split_goal_2 st_pre K_pre n_pre arr_pre l idx st_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7)

theorem proof_of_build_safety_wit_4 : build_safety_wit_4 := by
  unfold build_safety_wit_4
  right
  intro st_pre K_pre n_pre arr_pre l idx st_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  split_pures
  all_goals first
    | exact (proof_of_build_safety_wit_4_split_goal_1 st_pre K_pre n_pre arr_pre l idx st_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8)
    | exact (proof_of_build_safety_wit_4_split_goal_2 st_pre K_pre n_pre arr_pre l idx st_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8)

theorem proof_of_build_safety_wit_6 : build_safety_wit_6 := by
  unfold build_safety_wit_6
  right
  intro st_pre K_pre n_pre arr_pre l st_l i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pures
  all_goals first
    | exact (proof_of_build_safety_wit_6_split_goal_1 st_pre K_pre n_pre arr_pre l st_l i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
    | exact (proof_of_build_safety_wit_6_split_goal_2 st_pre K_pre n_pre arr_pre l st_l i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)

theorem proof_of_build_safety_wit_12 : build_safety_wit_12 := by
  unfold build_safety_wit_12
  right
  intro st_pre K_pre n_pre arr_pre l i len half j st_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pures
  all_goals first
    | exact (proof_of_build_safety_wit_12_split_goal_1 st_pre K_pre n_pre arr_pre l i len half j st_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11)
    | exact (proof_of_build_safety_wit_12_split_goal_2 st_pre K_pre n_pre arr_pre l i len half j st_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11)

theorem proof_of_build_safety_wit_13 : build_safety_wit_13 := by
  unfold build_safety_wit_13
  right
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pures
  all_goals first
    | exact (proof_of_build_safety_wit_13_split_goal_1 st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)
    | exact (proof_of_build_safety_wit_13_split_goal_2 st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)

theorem proof_of_build_safety_wit_14 : build_safety_wit_14 := by
  unfold build_safety_wit_14
  right
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pures
  all_goals first
    | exact (proof_of_build_safety_wit_14_split_goal_1 st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)
    | exact (proof_of_build_safety_wit_14_split_goal_2 st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)

theorem proof_of_build_safety_wit_15 : build_safety_wit_15 := by
  unfold build_safety_wit_15
  right
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pures
  all_goals first
    | exact (proof_of_build_safety_wit_15_split_goal_1 st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)
    | exact (proof_of_build_safety_wit_15_split_goal_2 st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)

theorem proof_of_build_safety_wit_17 : build_safety_wit_17 := by
  unfold build_safety_wit_17
  right
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pures
  all_goals first
    | exact (proof_of_build_safety_wit_17_split_goal_1 st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)
    | exact (proof_of_build_safety_wit_17_split_goal_2 st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)

theorem proof_of_build_safety_wit_18 : build_safety_wit_18 := by
  unfold build_safety_wit_18
  right
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pures
  all_goals first
    | exact (proof_of_build_safety_wit_18_split_goal_1 st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)
    | exact (proof_of_build_safety_wit_18_split_goal_2 st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)

theorem proof_of_build_safety_wit_19 : build_safety_wit_19 := by
  unfold build_safety_wit_19
  right
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pures
  all_goals first
    | exact (proof_of_build_safety_wit_19_split_goal_1 st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)
    | exact (proof_of_build_safety_wit_19_split_goal_2 st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)

theorem proof_of_build_safety_wit_20 : build_safety_wit_20 := by
  unfold build_safety_wit_20
  right
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pures
  all_goals first
    | exact (proof_of_build_safety_wit_20_split_goal_1 st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)
    | exact (proof_of_build_safety_wit_20_split_goal_2 st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)

theorem proof_of_build_safety_wit_22 : build_safety_wit_22 := by
  unfold build_safety_wit_22
  right
  intro st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pures
  all_goals first
    | exact (proof_of_build_safety_wit_22_split_goal_1 st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
    | exact (proof_of_build_safety_wit_22_split_goal_2 st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)

theorem proof_of_build_safety_wit_23 : build_safety_wit_23 := by
  unfold build_safety_wit_23
  right
  intro st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pures
  all_goals first
    | exact (proof_of_build_safety_wit_23_split_goal_1 st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
    | exact (proof_of_build_safety_wit_23_split_goal_2 st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)

theorem proof_of_build_safety_wit_24 : build_safety_wit_24 := by
  unfold build_safety_wit_24
  right
  intro st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pures
  all_goals first
    | exact (proof_of_build_safety_wit_24_split_goal_1 st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
    | exact (proof_of_build_safety_wit_24_split_goal_2 st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)

theorem proof_of_build_safety_wit_25 : build_safety_wit_25 := by
  unfold build_safety_wit_25
  right
  intro st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pures
  all_goals first
    | exact (proof_of_build_safety_wit_25_split_goal_1 st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
    | exact (proof_of_build_safety_wit_25_split_goal_2 st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)

theorem proof_of_build_safety_wit_26 : build_safety_wit_26 := by
  unfold build_safety_wit_26
  right
  intro st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pures
  all_goals first
    | exact (proof_of_build_safety_wit_26_split_goal_1 st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15)
    | exact (proof_of_build_safety_wit_26_split_goal_2 st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15)

theorem proof_of_build_safety_wit_27 : build_safety_wit_27 := by
  unfold build_safety_wit_27
  right
  intro st_pre K_pre n_pre arr_pre l st_l j half len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pures
  all_goals first
    | exact (proof_of_build_safety_wit_27_split_goal_1 st_pre K_pre n_pre arr_pre l st_l j half len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)
    | exact (proof_of_build_safety_wit_27_split_goal_2 st_pre K_pre n_pre arr_pre l st_l j half len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)

theorem proof_of_build_entail_wit_1 : build_entail_wit_1 := by
  unfold build_entail_wit_1
  right
  intro K_pre n_pre st0 l PreH1 PreH2 PreH3
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_build_entail_wit_1_split_goal_1 K_pre n_pre st0 l PreH1 PreH2 PreH3)
      | exact (proof_of_build_entail_wit_1_split_goal_2 K_pre n_pre st0 l PreH1 PreH2 PreH3)
      | exact (proof_of_build_entail_wit_1_split_goal_3 K_pre n_pre st0 l PreH1 PreH2 PreH3)

theorem proof_of_build_entail_wit_2 : build_entail_wit_2 := by
  unfold build_entail_wit_2
  right
  intro K_pre n_pre l idx st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_build_entail_wit_2_split_goal_1 K_pre n_pre l idx st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8)
      | exact (proof_of_build_entail_wit_2_split_goal_2 K_pre n_pre l idx st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8)
      | exact (proof_of_build_entail_wit_2_split_goal_3 K_pre n_pre l idx st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8)

theorem proof_of_build_entail_wit_3 : build_entail_wit_3 := by
  unfold build_entail_wit_3
  right
  intro K_pre n_pre l idx st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_build_entail_wit_3_split_goal_1 K_pre n_pre l idx st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8)
      | exact (proof_of_build_entail_wit_3_split_goal_2 K_pre n_pre l idx st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8)

theorem proof_of_build_entail_wit_4 : build_entail_wit_4 := by
  unfold build_entail_wit_4
  right
  intro K_pre n_pre l st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_build_entail_wit_4_split_goal_1 K_pre n_pre l st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5)
      | exact (proof_of_build_entail_wit_4_split_goal_2 K_pre n_pre l st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5)

theorem proof_of_build_entail_wit_5 : build_entail_wit_5 := by
  unfold build_entail_wit_5
  right
  intro K_pre n_pre l i st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_build_entail_wit_5_split_goal_1 K_pre n_pre l i st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
      | exact (proof_of_build_entail_wit_5_split_goal_2 K_pre n_pre l i st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
      | exact (proof_of_build_entail_wit_5_split_goal_3 K_pre n_pre l i st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
      | exact (proof_of_build_entail_wit_5_split_goal_4 K_pre n_pre l i st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)

theorem proof_of_build_entail_wit_6 : build_entail_wit_6 := by
  unfold build_entail_wit_6
  right
  intro K_pre n_pre l st_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_build_entail_wit_6_split_goal_1 K_pre n_pre l st_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
      | exact (proof_of_build_entail_wit_6_split_goal_2 K_pre n_pre l st_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
      | exact (proof_of_build_entail_wit_6_split_goal_3 K_pre n_pre l st_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)

theorem proof_of_build_entail_wit_8 : build_entail_wit_8 := by
  unfold build_entail_wit_8
  right
  intro K_pre n_pre l i st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_build_entail_wit_8_split_goal_1 K_pre n_pre l i st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
      | exact (proof_of_build_entail_wit_8_split_goal_2 K_pre n_pre l i st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)

theorem proof_of_build_entail_wit_9 : build_entail_wit_9 := by
  unfold build_entail_wit_9
  right
  intro K_pre n_pre l st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_build_entail_wit_9_split_goal_1 K_pre n_pre l st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5)
      | exact (proof_of_build_entail_wit_9_split_goal_2 K_pre n_pre l st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5)
      | exact (proof_of_build_entail_wit_9_split_goal_3 K_pre n_pre l st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5)

theorem proof_of_build_entail_wit_10 : build_entail_wit_10 := by
  unfold build_entail_wit_10
  right
  intro K_pre n_pre l len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_build_entail_wit_10_split_goal_1 K_pre n_pre l len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
      | exact (proof_of_build_entail_wit_10_split_goal_2 K_pre n_pre l len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)

theorem proof_of_build_entail_wit_11 : build_entail_wit_11 := by
  unfold build_entail_wit_11
  right
  intro K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_build_entail_wit_11_split_goal_1 K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)
      | exact (proof_of_build_entail_wit_11_split_goal_2 K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)
      | exact (proof_of_build_entail_wit_11_split_goal_3 K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)
      | exact (proof_of_build_entail_wit_11_split_goal_4 K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)
      | exact (proof_of_build_entail_wit_11_split_goal_5 K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)
      | exact (proof_of_build_entail_wit_11_split_goal_6 K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)
      | exact (proof_of_build_entail_wit_11_split_goal_7 K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)
      | exact (proof_of_build_entail_wit_11_split_goal_8 K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)
      | exact (proof_of_build_entail_wit_11_split_goal_9 K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)
      | exact (proof_of_build_entail_wit_11_split_goal_10 K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)
      | exact (proof_of_build_entail_wit_11_split_goal_11 K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)
      | exact (proof_of_build_entail_wit_11_split_goal_12 K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)

theorem proof_of_build_entail_wit_13_1 : build_entail_wit_13_1 := by
  unfold build_entail_wit_13_1
  right
  intro K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_build_entail_wit_13_1_split_goal_1 K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
      | exact (proof_of_build_entail_wit_13_1_split_goal_2 K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
      | exact (proof_of_build_entail_wit_13_1_split_goal_3 K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
      | exact (proof_of_build_entail_wit_13_1_split_goal_4 K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
      | exact (proof_of_build_entail_wit_13_1_split_goal_5 K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
      | exact (proof_of_build_entail_wit_13_1_split_goal_6 K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)

theorem proof_of_build_entail_wit_13_2 : build_entail_wit_13_2 := by
  unfold build_entail_wit_13_2
  right
  intro K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_build_entail_wit_13_2_split_goal_1 K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
      | exact (proof_of_build_entail_wit_13_2_split_goal_2 K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
      | exact (proof_of_build_entail_wit_13_2_split_goal_3 K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
      | exact (proof_of_build_entail_wit_13_2_split_goal_4 K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
      | exact (proof_of_build_entail_wit_13_2_split_goal_5 K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
      | exact (proof_of_build_entail_wit_13_2_split_goal_6 K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)

theorem proof_of_build_entail_wit_15 : build_entail_wit_15 := by
  unfold build_entail_wit_15
  right
  intro K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_build_entail_wit_15_split_goal_1 K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)
      | exact (proof_of_build_entail_wit_15_split_goal_2 K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)

theorem proof_of_build_entail_wit_16 : build_entail_wit_16 := by
  unfold build_entail_wit_16
  right
  intro K_pre n_pre l st_l_2 j half len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_build_entail_wit_16_split_goal_1 K_pre n_pre l st_l_2 j half len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)
      | exact (proof_of_build_entail_wit_16_split_goal_2 K_pre n_pre l st_l_2 j half len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)

theorem proof_of_build_return_wit_1 : build_return_wit_1 := by
  unfold build_return_wit_1
  right
  intro K_pre n_pre l len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_build_return_wit_1_split_goal_1 K_pre n_pre l len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
      | exact (proof_of_build_return_wit_1_split_goal_2 K_pre n_pre l len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)

theorem proof_of_query_safety_wit_1 : query_safety_wit_1 := by
  unfold query_safety_wit_1
  right
  intro right_pre left_pre K_pre n_pre st_pre st_l l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  split_pures
  all_goals first
    | exact (proof_of_query_safety_wit_1_split_goal_1 right_pre left_pre K_pre n_pre st_pre st_l l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
    | exact (proof_of_query_safety_wit_1_split_goal_2 right_pre left_pre K_pre n_pre st_pre st_l l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)

theorem proof_of_query_safety_wit_2 : query_safety_wit_2 := by
  unfold query_safety_wit_2
  right
  intro right_pre left_pre K_pre n_pre st_pre st_l l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  split_pures
  all_goals first
    | exact (proof_of_query_safety_wit_2_split_goal_1 right_pre left_pre K_pre n_pre st_pre st_l l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
    | exact (proof_of_query_safety_wit_2_split_goal_2 right_pre left_pre K_pre n_pre st_pre st_l l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)

theorem proof_of_query_safety_wit_6 : query_safety_wit_6 := by
  unfold query_safety_wit_6
  right
  intro right_pre left_pre K_pre n_pre st_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pures
  all_goals first
    | exact (proof_of_query_safety_wit_6_split_goal_1 right_pre left_pre K_pre n_pre st_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)
    | exact (proof_of_query_safety_wit_6_split_goal_2 right_pre left_pre K_pre n_pre st_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)

theorem proof_of_query_safety_wit_8 : query_safety_wit_8 := by
  unfold query_safety_wit_8
  right
  intro right_pre left_pre K_pre n_pre st_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pures
  all_goals first
    | exact (proof_of_query_safety_wit_8_split_goal_1 right_pre left_pre K_pre n_pre st_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
    | exact (proof_of_query_safety_wit_8_split_goal_2 right_pre left_pre K_pre n_pre st_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)

theorem proof_of_query_safety_wit_10 : query_safety_wit_10 := by
  unfold query_safety_wit_10
  right
  intro right_pre left_pre K_pre n_pre st_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pures
  all_goals first
    | exact (proof_of_query_safety_wit_10_split_goal_1 right_pre left_pre K_pre n_pre st_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
    | exact (proof_of_query_safety_wit_10_split_goal_2 right_pre left_pre K_pre n_pre st_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)

theorem proof_of_query_safety_wit_11 : query_safety_wit_11 := by
  unfold query_safety_wit_11
  right
  intro right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pures
  all_goals first
    | exact (proof_of_query_safety_wit_11_split_goal_1 right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
    | exact (proof_of_query_safety_wit_11_split_goal_2 right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_query_safety_wit_12 : query_safety_wit_12 := by
  unfold query_safety_wit_12
  right
  intro right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pures
  all_goals first
    | exact (proof_of_query_safety_wit_12_split_goal_1 right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
    | exact (proof_of_query_safety_wit_12_split_goal_2 right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_query_safety_wit_13 : query_safety_wit_13 := by
  unfold query_safety_wit_13
  right
  intro right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pures
  all_goals first
    | exact (proof_of_query_safety_wit_13_split_goal_1 right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
    | exact (proof_of_query_safety_wit_13_split_goal_2 right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_query_safety_wit_14 : query_safety_wit_14 := by
  unfold query_safety_wit_14
  right
  intro right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pures
  all_goals first
    | exact (proof_of_query_safety_wit_14_split_goal_1 right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
    | exact (proof_of_query_safety_wit_14_split_goal_2 right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_query_safety_wit_15 : query_safety_wit_15 := by
  unfold query_safety_wit_15
  right
  intro right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pures
  all_goals first
    | exact (proof_of_query_safety_wit_15_split_goal_1 right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
    | exact (proof_of_query_safety_wit_15_split_goal_2 right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_query_safety_wit_16 : query_safety_wit_16 := by
  unfold query_safety_wit_16
  right
  intro right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pures
  all_goals first
    | exact (proof_of_query_safety_wit_16_split_goal_1 right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
    | exact (proof_of_query_safety_wit_16_split_goal_2 right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_query_entail_wit_1 : query_entail_wit_1 := by
  unfold query_entail_wit_1
  right
  intro right_pre left_pre K_pre n_pre st_l l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_query_entail_wit_1_split_goal_1 right_pre left_pre K_pre n_pre st_l l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
      | exact (proof_of_query_entail_wit_1_split_goal_2 right_pre left_pre K_pre n_pre st_l l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)

theorem proof_of_query_entail_wit_2 : query_entail_wit_2 := by
  unfold query_entail_wit_2
  right
  intro right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_query_entail_wit_2_split_goal_1 right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
      | exact (proof_of_query_entail_wit_2_split_goal_2 right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)

theorem proof_of_query_entail_wit_3 : query_entail_wit_3 := by
  unfold query_entail_wit_3
  right
  intro right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_query_entail_wit_3_split_goal_1 right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
      | exact (proof_of_query_entail_wit_3_split_goal_2 right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
      | exact (proof_of_query_entail_wit_3_split_goal_3 right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
      | exact (proof_of_query_entail_wit_3_split_goal_4 right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
      | exact (proof_of_query_entail_wit_3_split_goal_5 right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
      | exact (proof_of_query_entail_wit_3_split_goal_6 right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
      | exact (proof_of_query_entail_wit_3_split_goal_7 right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
      | exact (proof_of_query_entail_wit_3_split_goal_8 right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
      | exact (proof_of_query_entail_wit_3_split_goal_9 right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)

theorem proof_of_query_entail_wit_5 : query_entail_wit_5 := by
  unfold query_entail_wit_5
  right
  intro right_pre left_pre K_pre n_pre st_l l len a k b pow PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_query_entail_wit_5_split_goal_1 right_pre left_pre K_pre n_pre st_l l len a k b pow PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)

theorem proof_of_query_entail_wit_6 : query_entail_wit_6 := by
  unfold query_entail_wit_6
  right
  intro right_pre left_pre K_pre n_pre st_l l len a k b pow PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_query_entail_wit_6_split_goal_1 right_pre left_pre K_pre n_pre st_l l len a k b pow PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)

end Algorithms.rmq.lean.groundtruth.rmq_proof_manual
