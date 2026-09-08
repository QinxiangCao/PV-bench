import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_goal
import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_auto
import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_helpers
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_manual_part5
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

theorem proof_of_maximum_profit_entail_wit_36_split_goal_1 : maximum_profit_entail_wit_36_split_goal_1 := by
  unfold maximum_profit_entail_wit_36_split_goal_1
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have he := PreH25.2.1 head (by omega)
  rcases he with ⟨he0,hel,hef,her⟩
  omega

theorem proof_of_maximum_profit_entail_wit_36_split_goal_2 : maximum_profit_entail_wit_36_split_goal_2 := by
  unfold maximum_profit_entail_wit_36_split_goal_2
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  exact (PreH25.2.1 head (by omega)).1

theorem proof_of_maximum_profit_entail_wit_36_split_goal_3 : maximum_profit_entail_wit_36_split_goal_3 := by
  unfold maximum_profit_entail_wit_36_split_goal_3
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have hb := PreH23
  unfold StockInputsBounded at hb
  have hdaily := hb.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega

theorem proof_of_maximum_profit_entail_wit_36_split_goal_4 : maximum_profit_entail_wit_36_split_goal_4 := by
  unfold maximum_profit_entail_wit_36_split_goal_4
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have hb := PreH23
  unfold StockInputsBounded at hb
  have hdaily := hb.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega

theorem proof_of_maximum_profit_entail_wit_36 : maximum_profit_entail_wit_36 := by
  unfold maximum_profit_entail_wit_36
  right
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_36_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_36_split_goal_2 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_36_split_goal_3 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_36_split_goal_4 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26))
    | trivial

theorem proof_of_maximum_profit_entail_wit_37 : maximum_profit_entail_wit_37 := by
  unfold maximum_profit_entail_wit_37
  left
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l neg_inf width i source_day bid_price sell_cap ask_price buy_cap j best_index head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  sep_apply (StockProofInternal.restore_cell dp_pre (days_pre+1) width source_day best_index dp_l __default__List_Z (by omega) (by omega))
  Exists dp_l queue_l_2
  finish_entail

theorem proof_of_maximum_profit_entail_wit_38_1 : maximum_profit_entail_wit_38_1 := by
  unfold maximum_profit_entail_wit_38_1
  left
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i j source_day best_index head bid_price sell_cap ask_price buy_cap tail buy_candidate __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have hlen := PreH30.1
  have hsrc : 0 ≤ source_day ∧ source_day < Zlength dp_l_2 := by omega
  have hcur : 0 ≤ i ∧ i < Zlength dp_l_2 := by omega
  have hsdef := Znth_indep dp_l_2 source_day __default__List_Z [] hsrc
  have hidef := Znth_indep dp_l_2 i __default__List_Z [] hcur
  have hcompare := PreH1
  rw [hidef] at hcompare
  have hval : buy_candidate = StockBuyScore dp_l_2 source_day ask_price best_index - j*ask_price := by
    unfold StockBuyScore
    rw [← hsdef]
    exact PreH28
  have hcell := StockBuyCellValue_improve__buy_cell_progress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j queue_l_2 ask_price buy_cap head tail best_index buy_candidate PreH27 (by omega) PreH29 (by omega) PreH18 PreH22 PreH21 hval hcompare
  have hstep := StockBuyProgress_replace_improved_step__buy_semantics ap_l bp_l buy_l sell_l dp_l_2 days_pre max_stock_pre wait_days_pre i source_day j buy_candidate PreH26 (by omega) PreH30 PreH27 (by omega) hcompare hcell
  obtain ⟨hp,hs⟩ := hstep
  rw [← hidef] at hp hs
  have hq := StockBuyQueue_replace_other_row__buy_cell_progress dp_l_2 queue_l_2 source_day ask_price (j-buy_cap) (j-1) head tail i (replace_Znth j buy_candidate (Znth i dp_l_2 __default__List_Z)) hsrc hcur (by omega) PreH29
  have hdaily := PreH26.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  have heq := PreH27.2.2.1
  have hrange := PreH27.2.2.2.1
  have hqnext : StockBuyQueue (replace_Znth i (replace_Znth j buy_candidate (Znth i dp_l_2 __default__List_Z)) dp_l_2) queue_l_2 source_day ask_price (j+1-buy_cap-1) (j+1-2) head tail := by
    simpa only [show j+1-buy_cap-1=j-buy_cap by omega, show j+1-2=j-1 by omega] using hq
  sep_apply (StockProofInternal.merge_cell dp_pre (days_pre+1) width i j buy_candidate dp_l_2 __default__List_Z (by omega) (by omega))
  Exists queue_l_2 (replace_Znth i (replace_Znth j buy_candidate (Znth i dp_l_2 __default__List_Z)) dp_l_2)
  finish_entail

theorem proof_of_maximum_profit_entail_wit_38_2 : maximum_profit_entail_wit_38_2 := by
  unfold maximum_profit_entail_wit_38_2
  left
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i j source_day best_index head bid_price sell_cap ask_price buy_cap tail buy_candidate __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have hlen := PreH30.1
  have hsrc : 0 ≤ source_day ∧ source_day < Zlength dp_l_2 := by omega
  have hcur : 0 ≤ i ∧ i < Zlength dp_l_2 := by omega
  have hsdef := Znth_indep dp_l_2 source_day __default__List_Z [] hsrc
  have hidef := Znth_indep dp_l_2 i __default__List_Z [] hcur
  have hcompare := PreH1
  rw [hidef] at hcompare
  have hval : buy_candidate = StockBuyScore dp_l_2 source_day ask_price best_index - j*ask_price := by
    unfold StockBuyScore
    rw [← hsdef]
    exact PreH28
  have hcell := StockBuyCellValue_keep__buy_cell_progress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j queue_l_2 ask_price buy_cap head tail best_index buy_candidate PreH27 (by omega) PreH29 (by omega) PreH18 PreH22 PreH21 hval hcompare
  have hp := StockBuyProgress_step_same__buy_cell_progress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j PreH27 (by omega) hcell
  have hq := PreH29
  have hdaily := PreH26.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  have heq := PreH27.2.2.1
  have hrange := PreH27.2.2.2.1
  have hqnext : StockBuyQueue dp_l_2 queue_l_2 source_day ask_price (j+1-buy_cap-1) (j+1-2) head tail := by
    simpa only [show j+1-buy_cap-1=j-buy_cap by omega, show j+1-2=j-1 by omega] using hq
  sep_apply (StockProofInternal.restore_cell dp_pre (days_pre+1) width i j dp_l_2 __default__List_Z (by omega) (by omega))
  Exists queue_l_2 dp_l_2
  finish_entail

theorem proof_of_maximum_profit_entail_wit_38_3_split_goal_1 : maximum_profit_entail_wit_38_3_split_goal_1 := by
  unfold maximum_profit_entail_wit_38_3_split_goal_1
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  simpa only [show j + 1 - buy_cap - 1 = j - buy_cap by omega, show j + 1 - 2 = j - 1 by omega] using PreH25

theorem proof_of_maximum_profit_entail_wit_38_3_split_goal_2 : maximum_profit_entail_wit_38_3_split_goal_2 := by
  unfold maximum_profit_entail_wit_38_3_split_goal_2
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have hrow := PreH26.2 source_day (by omega)
  apply StockBuyProgress_step_same__buy_cell_progress
  · exact PreH24
  · omega
  · apply StockBuyCellValue_empty_queue__buy_cell_progress
    all_goals first | assumption | omega

theorem proof_of_maximum_profit_entail_wit_38_3_split_goal_3 : maximum_profit_entail_wit_38_3_split_goal_3 := by
  unfold maximum_profit_entail_wit_38_3_split_goal_3
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have hb := PreH23
  unfold StockInputsBounded at hb
  have hdaily := hb.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega

theorem proof_of_maximum_profit_entail_wit_38_3_split_goal_4 : maximum_profit_entail_wit_38_3_split_goal_4 := by
  unfold maximum_profit_entail_wit_38_3_split_goal_4
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have hb := PreH23
  unfold StockInputsBounded at hb
  have hdaily := hb.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega

theorem proof_of_maximum_profit_entail_wit_38_3_split_goal_5 : maximum_profit_entail_wit_38_3_split_goal_5 := by
  unfold maximum_profit_entail_wit_38_3_split_goal_5
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have hb := PreH23
  unfold StockInputsBounded at hb
  have hdaily := hb.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega

theorem proof_of_maximum_profit_entail_wit_38_3_split_goal_6 : maximum_profit_entail_wit_38_3_split_goal_6 := by
  unfold maximum_profit_entail_wit_38_3_split_goal_6
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have hb := PreH23
  unfold StockInputsBounded at hb
  have hdaily := hb.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega

theorem proof_of_maximum_profit_entail_wit_38_3_split_goal_7 : maximum_profit_entail_wit_38_3_split_goal_7 := by
  unfold maximum_profit_entail_wit_38_3_split_goal_7
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  rcases PreH24 with ⟨HD,Hi,Hsrc,Hsr,Hj,Hrest⟩
  omega

theorem proof_of_maximum_profit_entail_wit_38_3_split_goal_8 : maximum_profit_entail_wit_38_3_split_goal_8 := by
  unfold maximum_profit_entail_wit_38_3_split_goal_8
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  rcases PreH24 with ⟨HD,Hi,Hsrc,Hsr,Hj,Hrest⟩
  omega

theorem proof_of_maximum_profit_entail_wit_38_3_split_goal_9 : maximum_profit_entail_wit_38_3_split_goal_9 := by
  unfold maximum_profit_entail_wit_38_3_split_goal_9
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  rcases PreH24 with ⟨HD,Hi,Hsrc,Hsr,Hj,Hrest⟩
  omega

theorem proof_of_maximum_profit_entail_wit_38_3 : maximum_profit_entail_wit_38_3 := by
  unfold maximum_profit_entail_wit_38_3
  right
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_38_3_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_38_3_split_goal_2 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_38_3_split_goal_3 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_38_3_split_goal_4 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_38_3_split_goal_5 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_38_3_split_goal_6 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_38_3_split_goal_7 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_38_3_split_goal_8 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_38_3_split_goal_9 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26))
    | trivial

theorem proof_of_maximum_profit_entail_wit_39_split_goal_1 : maximum_profit_entail_wit_39_split_goal_1 := by
  unfold maximum_profit_entail_wit_39_split_goal_1
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j buy_cap ask_price sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  exact StockBuyProgress_complete_day__buy_semantics ap_l bp_l buy_l sell_l dp_l_2 days_pre max_stock_pre wait_days_pre i source_day j PreH25 PreH4 PreH7 (by omega) PreH26

theorem proof_of_maximum_profit_entail_wit_39_split_goal_2 : maximum_profit_entail_wit_39_split_goal_2 := by
  unfold maximum_profit_entail_wit_39_split_goal_2
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j buy_cap ask_price sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  have hb := PreH25
  unfold StockInputsBounded at hb
  have hdaily := hb.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega

theorem proof_of_maximum_profit_entail_wit_39_split_goal_3 : maximum_profit_entail_wit_39_split_goal_3 := by
  unfold maximum_profit_entail_wit_39_split_goal_3
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j buy_cap ask_price sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  have hb := PreH25
  unfold StockInputsBounded at hb
  have hdaily := hb.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega

theorem proof_of_maximum_profit_entail_wit_39_split_goal_4 : maximum_profit_entail_wit_39_split_goal_4 := by
  unfold maximum_profit_entail_wit_39_split_goal_4
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j buy_cap ask_price sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  have hb := PreH25
  unfold StockInputsBounded at hb
  have hdaily := hb.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega

theorem proof_of_maximum_profit_entail_wit_39_split_goal_5 : maximum_profit_entail_wit_39_split_goal_5 := by
  unfold maximum_profit_entail_wit_39_split_goal_5
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j buy_cap ask_price sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  have hb := PreH25
  unfold StockInputsBounded at hb
  have hdaily := hb.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega

theorem proof_of_maximum_profit_entail_wit_39 : maximum_profit_entail_wit_39 := by
  unfold maximum_profit_entail_wit_39
  right
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j buy_cap ask_price sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_39_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j buy_cap ask_price sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_39_split_goal_2 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j buy_cap ask_price sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_39_split_goal_3 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j buy_cap ask_price sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_39_split_goal_4 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j buy_cap ask_price sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_39_split_goal_5 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j buy_cap ask_price sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28))
    | trivial

theorem proof_of_maximum_profit_entail_wit_40_1_split_goal_1 : maximum_profit_entail_wit_40_1_split_goal_1 := by
  unfold maximum_profit_entail_wit_40_1_split_goal_1
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 neg_inf width i source_day bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have hb := PreH19
  unfold StockInputsBounded at hb
  rcases hb with ⟨ha,hb,hc,hd,he,hf,hg⟩
  omega

theorem proof_of_maximum_profit_entail_wit_40_1_split_goal_2 : maximum_profit_entail_wit_40_1_split_goal_2 := by
  unfold maximum_profit_entail_wit_40_1_split_goal_2
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 neg_inf width i source_day bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have hb := PreH19
  unfold StockInputsBounded at hb
  rcases hb with ⟨ha,hb,hc,hd,he,hf,hg⟩
  omega

theorem proof_of_maximum_profit_entail_wit_40_1_split_goal_3 : maximum_profit_entail_wit_40_1_split_goal_3 := by
  unfold maximum_profit_entail_wit_40_1_split_goal_3
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 neg_inf width i source_day bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have hb := PreH19
  unfold StockInputsBounded at hb
  rcases hb with ⟨ha,hb,hc,hd,he,hf,hg⟩
  omega

theorem proof_of_maximum_profit_entail_wit_40_1 : maximum_profit_entail_wit_40_1 := by
  unfold maximum_profit_entail_wit_40_1
  right
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 neg_inf width i source_day bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_40_1_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 neg_inf width i source_day bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_40_1_split_goal_2 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 neg_inf width i source_day bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_40_1_split_goal_3 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 neg_inf width i source_day bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21))
    | trivial

theorem proof_of_maximum_profit_entail_wit_40_2_split_goal_1 : maximum_profit_entail_wit_40_2_split_goal_1 := by
  unfold maximum_profit_entail_wit_40_2_split_goal_1
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 neg_inf width buy_cap i ask_price PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have hb := PreH9
  unfold StockInputsBounded at hb
  rcases hb with ⟨ha,hb,hc,hd,he,hf,hg⟩
  omega

theorem proof_of_maximum_profit_entail_wit_40_2_split_goal_2 : maximum_profit_entail_wit_40_2_split_goal_2 := by
  unfold maximum_profit_entail_wit_40_2_split_goal_2
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 neg_inf width buy_cap i ask_price PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have hb := PreH9
  unfold StockInputsBounded at hb
  rcases hb with ⟨ha,hb,hc,hd,he,hf,hg⟩
  omega

theorem proof_of_maximum_profit_entail_wit_40_2_split_goal_3 : maximum_profit_entail_wit_40_2_split_goal_3 := by
  unfold maximum_profit_entail_wit_40_2_split_goal_3
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 neg_inf width buy_cap i ask_price PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have hb := PreH9
  unfold StockInputsBounded at hb
  rcases hb with ⟨ha,hb,hc,hd,he,hf,hg⟩
  omega

theorem proof_of_maximum_profit_entail_wit_40_2 : maximum_profit_entail_wit_40_2 := by
  unfold maximum_profit_entail_wit_40_2
  right
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 neg_inf width buy_cap i ask_price PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_40_2_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 neg_inf width buy_cap i ask_price PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_40_2_split_goal_2 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 neg_inf width buy_cap i ask_price PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_40_2_split_goal_3 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 neg_inf width buy_cap i ask_price PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11))
    | trivial

theorem proof_of_maximum_profit_entail_wit_41_split_goal_1 : maximum_profit_entail_wit_41_split_goal_1 := by
  unfold maximum_profit_entail_wit_41_split_goal_1
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have hi := PreH12
  unfold StockInputsBounded at hi
  apply stock_answer_init__outer_answer
  all_goals first | assumption | omega

theorem proof_of_maximum_profit_entail_wit_41 : maximum_profit_entail_wit_41 := by
  unfold maximum_profit_entail_wit_41
  right
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_41_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14))
    | trivial

theorem proof_of_maximum_profit_entail_wit_42_1 : maximum_profit_entail_wit_42_1 := by
  unfold maximum_profit_entail_wit_42_1
  left
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 answer j width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hlen := PreH17.1
  have hday : 0 ≤ days_pre ∧ days_pre < Zlength dp_l_2 := by omega
  have he := Znth_indep dp_l_2 days_pre __default__List_Z [] hday
  have hv : (Znth j (Znth days_pre dp_l_2 __default__List_Z) 0) = Znth j (Znth days_pre dp_l_2 []) 0 := by rw [he]
  have hp := stock_answer_improve__outer_answer ap_l bp_l buy_l sell_l dp_l_2 days_pre max_stock_pre wait_days_pre j answer (Znth j (Znth days_pre dp_l_2 __default__List_Z) 0) (by omega) PreH13 PreH2 PreH16 hv PreH1
  have hb := PreH16.1.2.1 days_pre j (by rw [PreH15.1]; omega) (by omega)
  rw [← he] at hb
  unfold STOCK_MAX_PROFIT at hb
  sep_apply (StockProofInternal.restore_cell dp_pre (days_pre+1) width days_pre j dp_l_2 __default__List_Z (by omega) (by omega))
  Exists queue_l_2 dp_l_2
  finish_entail

theorem proof_of_maximum_profit_entail_wit_42_2 : maximum_profit_entail_wit_42_2 := by
  unfold maximum_profit_entail_wit_42_2
  left
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 answer j width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hlen := PreH17.1
  have hday : 0 ≤ days_pre ∧ days_pre < Zlength dp_l_2 := by omega
  have he := Znth_indep dp_l_2 days_pre __default__List_Z [] hday
  have hv : (Znth j (Znth days_pre dp_l_2 __default__List_Z) 0) = Znth j (Znth days_pre dp_l_2 []) 0 := by rw [he]
  have hp := stock_answer_keep__outer_answer ap_l bp_l buy_l sell_l dp_l_2 days_pre max_stock_pre wait_days_pre j answer (Znth j (Znth days_pre dp_l_2 __default__List_Z) 0) (by omega) PreH2 PreH16 hv PreH1
  sep_apply (StockProofInternal.restore_cell dp_pre (days_pre+1) width days_pre j dp_l_2 __default__List_Z (by omega) (by omega))
  Exists queue_l_2 dp_l_2
  finish_entail

theorem proof_of_maximum_profit_entail_wit_43_split_goal_1 : maximum_profit_entail_wit_43_split_goal_1 := by
  unfold maximum_profit_entail_wit_43_split_goal_1
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 answer j width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  exact stock_answer_finish__outer_answer ap_l bp_l buy_l sell_l dp_l_2 days_pre max_stock_pre wait_days_pre j answer (by omega) PreH1 PreH11 PreH15

theorem proof_of_maximum_profit_entail_wit_43 : maximum_profit_entail_wit_43 := by
  unfold maximum_profit_entail_wit_43
  right
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 answer j width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_43_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 answer j width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | trivial

theorem proof_of_maximum_profit_return_wit_1 : maximum_profit_return_wit_1 := by
  unfold maximum_profit_return_wit_1
  left
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width answer PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  subst width
  sep_apply (intArray.full_to_undef_full queue_index_pre (max_stock_pre+1) queue_l)
  sep_apply (intArray2.full_to_undef_full dp_pre (days_pre+1) (max_stock_pre+1) dp_l)
  finish_entail

end SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_manual_part5
