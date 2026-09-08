import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_goal
import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_auto
import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_helpers
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_manual_part2
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open stock_trading_goal stock_trading_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev intArray2 := naive_C_Rules.IntArray2

local macro "finish_entail" : tactic => `(tactic| (
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega | int_auto))

private theorem product_bounds (x p : Int) (hx : 0 ≤ x ∧ x ≤ 990)
    (hp : 0 ≤ p ∧ p ≤ 1000) : 0 ≤ x*p ∧ x*p ≤ 990000 :=
  ⟨Int.mul_nonneg hx.1 hp.1, Int.mul_le_mul hx.2 hp.2 hp.1 (by omega)⟩

theorem proof_of_maximum_profit_entail_wit_13_1 : maximum_profit_entail_wit_13_1 := by
  unfold maximum_profit_entail_wit_13_1
  left
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 j ask_price buy_cap i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have hlen := PreH24.1
  have hcur : 0 ≤ i ∧ i < Zlength dp_l_2 := by omega
  have he := Znth_indep dp_l_2 i __default__List_Z [] hcur
  have hc := PreH23.2.2.2.2 j (by omega)
  simp only [if_neg (show ¬ j < j by omega)] at hc
  have hmax : (-j*ask_price) = max (Znth j (Znth (i-1) dp_l_2 []) 0) (-j*Znth (i-1) ap_l 0) := by
    rw [he] at PreH1
    rw [← hc, ← PreH15]
    exact (Int.max_eq_right (by omega)).symm
  have hstep := stock_early_buy_update_step__early_buy ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i j (-j*ask_price) days_pre PreH22 PreH23 (by omega) (by omega) hmax
  obtain ⟨hp,hs⟩ := hstep
  rw [← he] at hp hs
  sep_apply (StockProofInternal.merge_cell dp_pre (days_pre+1) width i j (-j*ask_price) dp_l_2 __default__List_Z (by omega) (by omega))
  Exists queue_l_2 (replace_Znth i (replace_Znth j (-j*ask_price) (Znth i dp_l_2 __default__List_Z)) dp_l_2)
  finish_entail

theorem proof_of_maximum_profit_entail_wit_13_2 : maximum_profit_entail_wit_13_2 := by
  unfold maximum_profit_entail_wit_13_2
  left
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 j ask_price buy_cap i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have hlen := PreH24.1
  have hcur : 0 ≤ i ∧ i < Zlength dp_l_2 := by omega
  have he := Znth_indep dp_l_2 i __default__List_Z [] hcur
  have hc := PreH23.2.2.2.2 j (by omega)
  simp only [if_neg (show ¬ j < j by omega)] at hc
  have hmax : (Znth j (Znth i dp_l_2 __default__List_Z) 0) = max (Znth j (Znth (i-1) dp_l_2 []) 0) (-j*Znth (i-1) ap_l 0) := by
    rw [he] at PreH1
    rw [← hc, ← PreH15]
    rw [he]; exact (Int.max_eq_left (by omega)).symm
  have hstep := stock_early_buy_update_step__early_buy ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i j (Znth j (Znth i dp_l_2 __default__List_Z) 0) days_pre PreH22 PreH23 (by omega) (by omega) hmax
  obtain ⟨hp,hs⟩ := hstep
  rw [← he] at hp hs
  sep_apply (StockProofInternal.merge_cell dp_pre (days_pre+1) width i j (Znth j (Znth i dp_l_2 __default__List_Z) 0) dp_l_2 __default__List_Z (by omega) (by omega))
  Exists queue_l_2 (replace_Znth i (replace_Znth j (Znth j (Znth i dp_l_2 __default__List_Z) 0) (Znth i dp_l_2 __default__List_Z)) dp_l_2)
  finish_entail

theorem proof_of_maximum_profit_entail_wit_14_split_goal_1 : maximum_profit_entail_wit_14_split_goal_1 := by
  unfold maximum_profit_entail_wit_14_split_goal_1
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j ask_price buy_cap i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  apply stock_early_buy_complete__early_buy
  all_goals first | assumption | omega

theorem proof_of_maximum_profit_entail_wit_14 : maximum_profit_entail_wit_14 := by
  unfold maximum_profit_entail_wit_14
  right
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j ask_price buy_cap i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_14_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j ask_price buy_cap i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | trivial

theorem proof_of_maximum_profit_entail_wit_15_split_goal_1 : maximum_profit_entail_wit_15_split_goal_1 := by
  unfold maximum_profit_entail_wit_15_split_goal_1
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 j i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro pos hp; omega
  · intro l r hr; omega
  · intro candidate hc
    have hrow := PreH17.2 (i - wait_days_pre - 1) (by omega)
    rcases hc with ⟨hc0,hcl,hcf,hcr⟩
    omega

theorem proof_of_maximum_profit_entail_wit_15_split_goal_2 : maximum_profit_entail_wit_15_split_goal_2 := by
  unfold maximum_profit_entail_wit_15_split_goal_2
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hlen := PreH15.1
  rcases PreH16 with ⟨HD,Hi,Hcol,Hcells⟩
  refine ⟨HD, by omega, by omega, by omega, by omega, ?_, ?_, ?_⟩
  · intro stock hs; exact Hcells stock (by omega)
  · intro stock hs; omega
  · exact Hcells max_stock_pre (by omega)

theorem proof_of_maximum_profit_entail_wit_15_split_goal_3 : maximum_profit_entail_wit_15_split_goal_3 := by
  unfold maximum_profit_entail_wit_15_split_goal_3
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hdaily := PreH15.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega

theorem proof_of_maximum_profit_entail_wit_15_split_goal_4 : maximum_profit_entail_wit_15_split_goal_4 := by
  unfold maximum_profit_entail_wit_15_split_goal_4
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hdaily := PreH15.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega

theorem proof_of_maximum_profit_entail_wit_15_split_goal_5 : maximum_profit_entail_wit_15_split_goal_5 := by
  unfold maximum_profit_entail_wit_15_split_goal_5
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hdaily := PreH15.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega

theorem proof_of_maximum_profit_entail_wit_15_split_goal_6 : maximum_profit_entail_wit_15_split_goal_6 := by
  unfold maximum_profit_entail_wit_15_split_goal_6
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hdaily := PreH15.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega

theorem proof_of_maximum_profit_entail_wit_15 : maximum_profit_entail_wit_15 := by
  unfold maximum_profit_entail_wit_15
  right
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 j i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_15_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 j i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_15_split_goal_2 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_15_split_goal_3 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_15_split_goal_4 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_15_split_goal_5 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_15_split_goal_6 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | trivial

theorem proof_of_maximum_profit_entail_wit_16_split_goal_1 : maximum_profit_entail_wit_16_split_goal_1 := by
  unfold maximum_profit_entail_wit_16_split_goal_1
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  rw [← PreH13]
  left
  simpa only [show j + sell_cap + 1 = j + (sell_cap + 1) by omega] using PreH29

theorem proof_of_maximum_profit_entail_wit_16 : maximum_profit_entail_wit_16 := by
  unfold maximum_profit_entail_wit_16
  right
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_16_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30))
    | trivial

theorem proof_of_maximum_profit_entail_wit_17_split_goal_1 : maximum_profit_entail_wit_17_split_goal_1 := by
  unfold maximum_profit_entail_wit_17_split_goal_1
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 bid_price tail head sell_cap j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  rw [← PreH14]
  right
  apply StockSellQueue_drop_expired__sell_expire
  all_goals first | assumption | omega

theorem proof_of_maximum_profit_entail_wit_17 : maximum_profit_entail_wit_17 := by
  unfold maximum_profit_entail_wit_17
  right
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 bid_price tail head sell_cap j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_17_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 bid_price tail head sell_cap j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31))
    | trivial

theorem proof_of_maximum_profit_entail_wit_18_1_split_goal_1 : maximum_profit_entail_wit_18_1_split_goal_1 := by
  unfold maximum_profit_entail_wit_18_1_split_goal_1
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 bid_price tail head sell_cap j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  rw [← PreH13]
  apply StockSellQueueExpiring_empty__sell_expire
  all_goals first | assumption | omega

theorem proof_of_maximum_profit_entail_wit_18_1 : maximum_profit_entail_wit_18_1 := by
  unfold maximum_profit_entail_wit_18_1
  right
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 bid_price tail head sell_cap j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_18_1_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 bid_price tail head sell_cap j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30))
    | trivial

theorem proof_of_maximum_profit_entail_wit_18_2_split_goal_1 : maximum_profit_entail_wit_18_2_split_goal_1 := by
  unfold maximum_profit_entail_wit_18_2_split_goal_1
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 bid_price tail head sell_cap j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  rw [← PreH14]
  apply StockSellQueueExpiring_head_bounded__sell_expire
  all_goals first | assumption | omega

theorem proof_of_maximum_profit_entail_wit_18_2_split_goal_2 : maximum_profit_entail_wit_18_2_split_goal_2 := by
  unfold maximum_profit_entail_wit_18_2_split_goal_2
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 bid_price tail head sell_cap j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  rcases PreH30 with hq | hq
  all_goals
    have he := hq.2.1 head (by omega)
    have hi := he.2.2.2
    omega

theorem proof_of_maximum_profit_entail_wit_18_2 : maximum_profit_entail_wit_18_2 := by
  unfold maximum_profit_entail_wit_18_2
  right
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 bid_price tail head sell_cap j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_18_2_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 bid_price tail head sell_cap j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_18_2_split_goal_2 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 bid_price tail head sell_cap j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31))
    | trivial

theorem proof_of_maximum_profit_entail_wit_19_1 : maximum_profit_entail_wit_19_1 := by
  unfold maximum_profit_entail_wit_19_1
  left
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap j head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have hlen := PreH31.1
  have hrow := PreH31.2 source_day (by omega)
  have he := Znth_indep dp_l source_day __default__List_Z [] (by omega)
  have hn : Znth (j+1) (Znth source_day dp_l []) 0 ≠ STOCK_NEG_INF := by
    rw [he] at PreH2
    unfold STOCK_NEG_INF
    omega
  have hq : StockSellQueue dp_l queue_l source_day bid_price ((j+1)+1) (j+sell_cap) head tail := by
    simpa only [show j+1+1=j+2 by omega] using PreH30
  have hp := StockSellQueue_begin_popping__sell_pop_append dp_l queue_l source_day bid_price (j+1) (j+sell_cap) head tail (by omega) (by omega) hn hq
  have hb (pos : Int) (hpos : head ≤ pos ∧ pos < tail) : 0 ≤ Znth pos queue_l 0 ∧ Znth pos queue_l 0 ≤ max_stock_pre := by
    have helem := PreH30.2.1 pos hpos
    rcases helem with ⟨h0,hl,hv,hr⟩
    omega
  have hlast := hb (tail-1) (by omega)
  sep_apply (StockProofInternal.restore_cell dp_pre (days_pre+1) width source_day (j+1) dp_l __default__List_Z (by omega) (by omega))
  Exists queue_l dp_l
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega | (intros; first | assumption | trivial | omega)

theorem proof_of_maximum_profit_entail_wit_19_2 : maximum_profit_entail_wit_19_2 := by
  unfold maximum_profit_entail_wit_19_2
  left
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l neg_inf width i source_day bid_price sell_cap j head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have hlen := PreH31.1
  have hrow := PreH31.2 source_day (by omega)
  have he := Znth_indep dp_l source_day __default__List_Z [] (by omega)
  have hn : Znth (j+1) (Znth source_day dp_l []) 0 ≠ STOCK_NEG_INF := by
    rw [he] at PreH2
    unfold STOCK_NEG_INF
    omega
  have hq : StockSellQueue dp_l queue_l_2 source_day bid_price ((j+1)+1) (j+sell_cap) head tail := by
    simpa only [show j+1+1=j+2 by omega] using PreH30
  have hp := StockSellQueue_begin_popping__sell_pop_append dp_l queue_l_2 source_day bid_price (j+1) (j+sell_cap) head tail (by omega) (by omega) hn hq
  have hb (pos : Int) (hpos : head ≤ pos ∧ pos < tail) : 0 ≤ Znth pos queue_l_2 0 ∧ Znth pos queue_l_2 0 ≤ max_stock_pre := by
    have helem := PreH30.2.1 pos hpos
    rcases helem with ⟨h0,hl,hv,hr⟩
    omega

  sep_apply (StockProofInternal.restore_cell dp_pre (days_pre+1) width source_day (j+1) dp_l __default__List_Z (by omega) (by omega))
  Exists queue_l_2 dp_l
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | omega | (intros; first | assumption | omega)

theorem proof_of_maximum_profit_entail_wit_20_1 : maximum_profit_entail_wit_20_1 := by
  unfold maximum_profit_entail_wit_20_1
  left
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 incoming_score last_index tail head sell_cap bid_price source_day j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  have hlen := PreH33.1
  have he := Znth_indep dp_l_2 source_day __default__List_Z [] (by omega)
  have hscore : StockSellScore dp_l_2 source_day bid_price (Znth (tail-1) queue_l_2 0) ≤ StockSellScore dp_l_2 source_day bid_price (j+1) := by
    unfold StockSellScore
    rw [← PreH28 (by omega), ← he]
    omega
  have hp := StockSellQueuePopping_drop_tail__sell_pop_append dp_l_2 queue_l_2 source_day bid_price (j+1) (j+sell_cap) head tail PreH31 (by omega) hscore
  have hb (pos : Int) (hpos : head ≤ pos ∧ pos < tail-1) := PreH32 pos (show head ≤ pos ∧ pos < tail by omega)
  have hlast := hb (tail-1-1) (by omega)
  sep_apply (StockProofInternal.restore_cell dp_pre (days_pre+1) width source_day last_index dp_l_2 __default__List_Z (by omega) (by omega))
  Exists queue_l_2 dp_l_2
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega | (intros; first | assumption | trivial | omega)

theorem proof_of_maximum_profit_entail_wit_20_2 : maximum_profit_entail_wit_20_2 := by
  unfold maximum_profit_entail_wit_20_2
  left
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 incoming_score last_index tail head sell_cap bid_price source_day j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  have hlen := PreH33.1
  have he := Znth_indep dp_l_2 source_day __default__List_Z [] (by omega)
  have hscore : StockSellScore dp_l_2 source_day bid_price (Znth (tail-1) queue_l_2 0) ≤ StockSellScore dp_l_2 source_day bid_price (j+1) := by
    unfold StockSellScore
    rw [← PreH28 (by omega), ← he]
    omega
  have hp := StockSellQueuePopping_drop_tail__sell_pop_append dp_l_2 queue_l_2 source_day bid_price (j+1) (j+sell_cap) head tail PreH31 (by omega) hscore
  have hb (pos : Int) (hpos : head ≤ pos ∧ pos < tail-1) := PreH32 pos (show head ≤ pos ∧ pos < tail by omega)

  sep_apply (StockProofInternal.restore_cell dp_pre (days_pre+1) width source_day last_index dp_l_2 __default__List_Z (by omega) (by omega))
  Exists queue_l_2 dp_l_2
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | omega | (intros; first | assumption | omega)

theorem proof_of_maximum_profit_entail_wit_21_1 : maximum_profit_entail_wit_21_1 := by
  unfold maximum_profit_entail_wit_21_1
  left
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 incoming_score last_index tail head sell_cap bid_price source_day j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  prop_apply (intArray.full_Zlength queue_index_pre width queue_l_2)
  Intros_p hqlen
  have hp : StockSellQueuePending dp_l_2 queue_l_2 source_day bid_price (j+1) (j+sell_cap) head tail := by
    refine ⟨PreH29, by omega, ?_⟩
    intro hh
    omega
  Exists dp_l_2 queue_l_2
  finish_entail

theorem proof_of_maximum_profit_entail_wit_21_2 : maximum_profit_entail_wit_21_2 := by
  unfold maximum_profit_entail_wit_21_2
  left
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 incoming_score last_index tail head sell_cap bid_price source_day j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  prop_apply (intArray.full_Zlength queue_index_pre width queue_l_2)
  Intros_p hqlen
  have hp : StockSellQueuePending dp_l_2 queue_l_2 source_day bid_price (j+1) (j+sell_cap) head tail := by
    refine ⟨PreH30, by omega, ?_⟩
    intro hh
    have hlen := PreH32.1
    have he := Znth_indep dp_l_2 source_day __default__List_Z [] (by omega)
    unfold StockSellScore
    rw [← PreH27 hh, ← he]
    omega
  sep_apply (StockProofInternal.restore_cell dp_pre (days_pre+1) width source_day last_index dp_l_2 __default__List_Z (by omega) (by omega))
  Exists dp_l_2 queue_l_2
  finish_entail

theorem proof_of_maximum_profit_entail_wit_22_split_goal_1 : maximum_profit_entail_wit_22_split_goal_1 := by
  unfold maximum_profit_entail_wit_22_split_goal_1
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day bid_price sell_cap j head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have hdaily := PreH23.2.2.2.2.2.2 i (by omega)
  have hs := hdaily.2.2.2
  apply StockSellQueuePending_append__sell_pop_append
  · omega
  · exact PreH25

theorem proof_of_maximum_profit_entail_wit_22 : maximum_profit_entail_wit_22 := by
  unfold maximum_profit_entail_wit_22
  right
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day bid_price sell_cap j head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_22_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day bid_price sell_cap j head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26))
    | trivial

theorem proof_of_maximum_profit_entail_wit_23_1_split_goal_1 : maximum_profit_entail_wit_23_1_split_goal_1 := by
  unfold maximum_profit_entail_wit_23_1_split_goal_1
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j head tail bid_price sell_cap PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  rcases PreH21 with ⟨HD,Hi,Hsrc,Hsr,Hj,Hrest⟩
  omega

theorem proof_of_maximum_profit_entail_wit_23_1 : maximum_profit_entail_wit_23_1 := by
  unfold maximum_profit_entail_wit_23_1
  right
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j head tail bid_price sell_cap PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_23_1_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j head tail bid_price sell_cap PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | trivial

theorem proof_of_maximum_profit_entail_wit_23_2 : maximum_profit_entail_wit_23_2 := by
  unfold maximum_profit_entail_wit_23_2
  left
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day bid_price sell_cap j head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have hlen := PreH30.1
  have he := Znth_indep dp_l_2 source_day __default__List_Z [] (by omega)
  have hn : Znth (j+1) (Znth source_day dp_l_2 []) 0 = STOCK_NEG_INF := by
    rw [he] at PreH1
    unfold STOCK_NEG_INF
    omega
  have hp := stock_sell_queue_extend_lower_neg_inf__sell_cell_progress dp_l_2 queue_l_2 source_day bid_price (j+1) (j+sell_cap) head tail hn (by simpa only [show j+1+1=j+2 by omega] using PreH29)
  sep_apply (StockProofInternal.restore_cell dp_pre (days_pre+1) width source_day (j+1) dp_l_2 __default__List_Z (by omega) (by omega))
  Exists queue_l_2 dp_l_2
  finish_entail

theorem proof_of_maximum_profit_entail_wit_24_split_goal_1 : maximum_profit_entail_wit_24_split_goal_1 := by
  unfold maximum_profit_entail_wit_24_split_goal_1
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have he := PreH24.2.1 head (by omega)
  have hrow := PreH25.2 source_day (by omega)
  rcases he with ⟨he0,hel,hef,her⟩
  omega

theorem proof_of_maximum_profit_entail_wit_24_split_goal_2 : maximum_profit_entail_wit_24_split_goal_2 := by
  unfold maximum_profit_entail_wit_24_split_goal_2
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  exact (PreH24.2.1 head (by omega)).1

theorem proof_of_maximum_profit_entail_wit_24_split_goal_3 : maximum_profit_entail_wit_24_split_goal_3 := by
  unfold maximum_profit_entail_wit_24_split_goal_3
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hb := PreH22
  unfold StockInputsBounded at hb
  have hdaily := hb.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega

theorem proof_of_maximum_profit_entail_wit_24_split_goal_4 : maximum_profit_entail_wit_24_split_goal_4 := by
  unfold maximum_profit_entail_wit_24_split_goal_4
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hb := PreH22
  unfold StockInputsBounded at hb
  have hdaily := hb.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega

theorem proof_of_maximum_profit_entail_wit_24 : maximum_profit_entail_wit_24 := by
  unfold maximum_profit_entail_wit_24
  right
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_24_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_24_split_goal_2 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_24_split_goal_3 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_24_split_goal_4 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25))
    | trivial

theorem proof_of_maximum_profit_entail_wit_25 : maximum_profit_entail_wit_25 := by
  unfold maximum_profit_entail_wit_25
  left
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l neg_inf width i source_day bid_price sell_cap j best_index head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  sep_apply (StockProofInternal.restore_cell dp_pre (days_pre+1) width source_day best_index dp_l __default__List_Z (by omega) (by omega))
  Exists dp_l queue_l_2
  finish_entail

end SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_manual_part2
