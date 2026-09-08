import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_goal
import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_auto
import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_helpers
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_manual_part1
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

theorem proof_of_maximum_profit_safety_wit_54_split_goal_1 : maximum_profit_safety_wit_54_split_goal_1 := by
  unfold maximum_profit_safety_wit_54_split_goal_1
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l bid_price tail head sell_cap j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  rcases PreH29 with hqueue | hqueue
  all_goals
    have he := hqueue.2.1 head (by omega)
    have hi := he.2.2.2
    dump_pre_spatial
    simp only [INT_MAX, INT_MIN]
    omega

theorem proof_of_maximum_profit_safety_wit_54_split_goal_2 : maximum_profit_safety_wit_54_split_goal_2 := by
  unfold maximum_profit_safety_wit_54_split_goal_2
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l bid_price tail head sell_cap j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  rcases PreH29 with hqueue | hqueue
  all_goals
    have he := hqueue.2.1 head (by omega)
    have hi := he.2.2.2
    dump_pre_spatial
    simp only [INT_MAX, INT_MIN]
    omega

theorem proof_of_maximum_profit_safety_wit_54 : maximum_profit_safety_wit_54 := by
  unfold maximum_profit_safety_wit_54
  right
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l bid_price tail head sell_cap j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_maximum_profit_safety_wit_54_split_goal_1 dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l bid_price tail head sell_cap j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30))
    | (solve | Goal_apply (proof_of_maximum_profit_safety_wit_54_split_goal_2 dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l bid_price tail head sell_cap j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30))
    | trivial

theorem proof_of_maximum_profit_safety_wit_63_split_goal_1 : maximum_profit_safety_wit_63_split_goal_1 := by
  unfold maximum_profit_safety_wit_63_split_goal_1
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap j head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have Hdone := PreH29.1
  have Hcell := StockDaysDone_cell_bounded__safety_sell ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i source_day (j + 1) __default__List_Z PreH28 Hdone PreH31 (by omega) (by omega)
  unfold STOCK_NEG_INF STOCK_MAX_PROFIT at Hcell
  have hprod := product_bounds (j + 1) bid_price (by omega) (by omega)
  have hjprod := product_bounds j bid_price (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX, INT_MIN]
  omega

theorem proof_of_maximum_profit_safety_wit_63_split_goal_2 : maximum_profit_safety_wit_63_split_goal_2 := by
  unfold maximum_profit_safety_wit_63_split_goal_2
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap j head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have Hdone := PreH29.1
  have Hcell := StockDaysDone_cell_bounded__safety_sell ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i source_day (j + 1) __default__List_Z PreH28 Hdone PreH31 (by omega) (by omega)
  unfold STOCK_NEG_INF STOCK_MAX_PROFIT at Hcell
  have hprod := product_bounds (j + 1) bid_price (by omega) (by omega)
  have hjprod := product_bounds j bid_price (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX, INT_MIN]
  omega

theorem proof_of_maximum_profit_safety_wit_63 : maximum_profit_safety_wit_63 := by
  unfold maximum_profit_safety_wit_63
  right
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap j head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_maximum_profit_safety_wit_63_split_goal_1 dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap j head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31))
    | (solve | Goal_apply (proof_of_maximum_profit_safety_wit_63_split_goal_2 dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap j head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31))
    | trivial

theorem proof_of_maximum_profit_safety_wit_70_split_goal_1 : maximum_profit_safety_wit_70_split_goal_1 := by
  unfold maximum_profit_safety_wit_70_split_goal_1
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap j head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have Hdone := PreH29.1
  have Hcell := StockDaysDone_cell_bounded__safety_sell ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i source_day (j + 1) __default__List_Z PreH28 Hdone PreH31 (by omega) (by omega)
  unfold STOCK_NEG_INF STOCK_MAX_PROFIT at Hcell
  have hprod := product_bounds (j + 1) bid_price (by omega) (by omega)
  have hjprod := product_bounds j bid_price (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX, INT_MIN]
  omega

theorem proof_of_maximum_profit_safety_wit_70_split_goal_2 : maximum_profit_safety_wit_70_split_goal_2 := by
  unfold maximum_profit_safety_wit_70_split_goal_2
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap j head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have Hdone := PreH29.1
  have Hcell := StockDaysDone_cell_bounded__safety_sell ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i source_day (j + 1) __default__List_Z PreH28 Hdone PreH31 (by omega) (by omega)
  unfold STOCK_NEG_INF STOCK_MAX_PROFIT at Hcell
  have hprod := product_bounds (j + 1) bid_price (by omega) (by omega)
  have hjprod := product_bounds j bid_price (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX, INT_MIN]
  omega

theorem proof_of_maximum_profit_safety_wit_70 : maximum_profit_safety_wit_70 := by
  unfold maximum_profit_safety_wit_70
  right
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap j head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_maximum_profit_safety_wit_70_split_goal_1 dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap j head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31))
    | (solve | Goal_apply (proof_of_maximum_profit_safety_wit_70_split_goal_2 dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap j head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31))
    | trivial

theorem proof_of_maximum_profit_safety_wit_77_split_goal_1 : maximum_profit_safety_wit_77_split_goal_1 := by
  unfold maximum_profit_safety_wit_77_split_goal_1
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l incoming_score last_index tail head sell_cap bid_price source_day j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have Hdone := PreH28.1
  have Hcell := StockDaysDone_cell_bounded__safety_sell ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i source_day last_index __default__List_Z PreH27 Hdone PreH31 (by omega) (by omega)
  unfold STOCK_NEG_INF STOCK_MAX_PROFIT at Hcell
  have hprod := product_bounds last_index bid_price (by omega) (by omega)
  have hjprod := product_bounds j bid_price (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX, INT_MIN]
  omega

theorem proof_of_maximum_profit_safety_wit_77_split_goal_2 : maximum_profit_safety_wit_77_split_goal_2 := by
  unfold maximum_profit_safety_wit_77_split_goal_2
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l incoming_score last_index tail head sell_cap bid_price source_day j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have Hdone := PreH28.1
  have Hcell := StockDaysDone_cell_bounded__safety_sell ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i source_day last_index __default__List_Z PreH27 Hdone PreH31 (by omega) (by omega)
  unfold STOCK_NEG_INF STOCK_MAX_PROFIT at Hcell
  have hprod := product_bounds last_index bid_price (by omega) (by omega)
  have hjprod := product_bounds j bid_price (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX, INT_MIN]
  omega

theorem proof_of_maximum_profit_safety_wit_77 : maximum_profit_safety_wit_77 := by
  unfold maximum_profit_safety_wit_77
  right
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l incoming_score last_index tail head sell_cap bid_price source_day j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_maximum_profit_safety_wit_77_split_goal_1 dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l incoming_score last_index tail head sell_cap bid_price source_day j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31))
    | (solve | Goal_apply (proof_of_maximum_profit_safety_wit_77_split_goal_2 dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l incoming_score last_index tail head sell_cap bid_price source_day j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31))
    | trivial

theorem proof_of_maximum_profit_safety_wit_86_split_goal_1 : maximum_profit_safety_wit_86_split_goal_1 := by
  unfold maximum_profit_safety_wit_86_split_goal_1
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap j best_index head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  have Hdone := PreH27.1
  have Hcell := StockDaysDone_cell_bounded__safety_sell ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i source_day best_index __default__List_Z PreH26 Hdone PreH29 (by omega) (by omega)
  unfold STOCK_NEG_INF STOCK_MAX_PROFIT at Hcell
  have hprod := product_bounds best_index bid_price (by omega) (by omega)
  have hjprod := product_bounds j bid_price (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX, INT_MIN]
  omega

theorem proof_of_maximum_profit_safety_wit_86_split_goal_2 : maximum_profit_safety_wit_86_split_goal_2 := by
  unfold maximum_profit_safety_wit_86_split_goal_2
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap j best_index head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  have Hdone := PreH27.1
  have Hcell := StockDaysDone_cell_bounded__safety_sell ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i source_day best_index __default__List_Z PreH26 Hdone PreH29 (by omega) (by omega)
  unfold STOCK_NEG_INF STOCK_MAX_PROFIT at Hcell
  have hprod := product_bounds best_index bid_price (by omega) (by omega)
  have hjprod := product_bounds j bid_price (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX, INT_MIN]
  omega

theorem proof_of_maximum_profit_safety_wit_86 : maximum_profit_safety_wit_86 := by
  unfold maximum_profit_safety_wit_86
  right
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap j best_index head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_maximum_profit_safety_wit_86_split_goal_1 dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap j best_index head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29))
    | (solve | Goal_apply (proof_of_maximum_profit_safety_wit_86_split_goal_2 dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap j best_index head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29))
    | trivial

theorem proof_of_maximum_profit_safety_wit_88_split_goal_1 : maximum_profit_safety_wit_88_split_goal_1 := by
  unfold maximum_profit_safety_wit_88_split_goal_1
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap j best_index head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  have Hdone := PreH27.1
  have Hcell := StockDaysDone_cell_bounded__safety_sell ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i source_day best_index __default__List_Z PreH26 Hdone PreH29 (by omega) (by omega)
  unfold STOCK_NEG_INF STOCK_MAX_PROFIT at Hcell
  have hprod := product_bounds best_index bid_price (by omega) (by omega)
  have hjprod := product_bounds j bid_price (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX, INT_MIN]
  omega

theorem proof_of_maximum_profit_safety_wit_88_split_goal_2 : maximum_profit_safety_wit_88_split_goal_2 := by
  unfold maximum_profit_safety_wit_88_split_goal_2
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap j best_index head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  have Hdone := PreH27.1
  have Hcell := StockDaysDone_cell_bounded__safety_sell ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i source_day best_index __default__List_Z PreH26 Hdone PreH29 (by omega) (by omega)
  unfold STOCK_NEG_INF STOCK_MAX_PROFIT at Hcell
  have hprod := product_bounds best_index bid_price (by omega) (by omega)
  have hjprod := product_bounds j bid_price (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX, INT_MIN]
  omega

theorem proof_of_maximum_profit_safety_wit_88 : maximum_profit_safety_wit_88 := by
  unfold maximum_profit_safety_wit_88
  right
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap j best_index head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_maximum_profit_safety_wit_88_split_goal_1 dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap j best_index head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29))
    | (solve | Goal_apply (proof_of_maximum_profit_safety_wit_88_split_goal_2 dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap j best_index head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29))
    | trivial

theorem proof_of_maximum_profit_safety_wit_103_split_goal_1 : maximum_profit_safety_wit_103_split_goal_1 := by
  unfold maximum_profit_safety_wit_103_split_goal_1
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l tail head buy_cap ask_price sell_cap bid_price j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  rcases PreH31 with hqueue | hqueue
  all_goals
    have he := hqueue.2.1 head (by omega)
    have hi := he.2.2.2
    dump_pre_spatial
    simp only [INT_MAX, INT_MIN]
    omega

theorem proof_of_maximum_profit_safety_wit_103_split_goal_2 : maximum_profit_safety_wit_103_split_goal_2 := by
  unfold maximum_profit_safety_wit_103_split_goal_2
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l tail head buy_cap ask_price sell_cap bid_price j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  rcases PreH31 with hqueue | hqueue
  all_goals
    have he := hqueue.2.1 head (by omega)
    have hi := he.2.2.2
    dump_pre_spatial
    simp only [INT_MAX, INT_MIN]
    omega

theorem proof_of_maximum_profit_safety_wit_103 : maximum_profit_safety_wit_103 := by
  unfold maximum_profit_safety_wit_103
  right
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l tail head buy_cap ask_price sell_cap bid_price j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_maximum_profit_safety_wit_103_split_goal_1 dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l tail head buy_cap ask_price sell_cap bid_price j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32))
    | (solve | Goal_apply (proof_of_maximum_profit_safety_wit_103_split_goal_2 dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l tail head buy_cap ask_price sell_cap bid_price j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32))
    | trivial

theorem proof_of_maximum_profit_safety_wit_112_split_goal_1 : maximum_profit_safety_wit_112_split_goal_1 := by
  unfold maximum_profit_safety_wit_112_split_goal_1
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap ask_price buy_cap j head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have Hdone := PreH29.1
  have Hcell := StockDaysDone_cell_bounded__safety_buy ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i source_day (j - 1) __default__List_Z PreH28 Hdone PreH31 (by omega) (by omega)
  unfold STOCK_NEG_INF STOCK_MAX_PROFIT at Hcell
  have hprod := product_bounds (j - 1) ask_price (by omega) (by omega)
  have hjprod := product_bounds j ask_price (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX, INT_MIN]
  omega

theorem proof_of_maximum_profit_safety_wit_112_split_goal_2 : maximum_profit_safety_wit_112_split_goal_2 := by
  unfold maximum_profit_safety_wit_112_split_goal_2
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap ask_price buy_cap j head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have Hdone := PreH29.1
  have Hcell := StockDaysDone_cell_bounded__safety_buy ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i source_day (j - 1) __default__List_Z PreH28 Hdone PreH31 (by omega) (by omega)
  unfold STOCK_NEG_INF STOCK_MAX_PROFIT at Hcell
  have hprod := product_bounds (j - 1) ask_price (by omega) (by omega)
  have hjprod := product_bounds j ask_price (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX, INT_MIN]
  omega

theorem proof_of_maximum_profit_safety_wit_112 : maximum_profit_safety_wit_112 := by
  unfold maximum_profit_safety_wit_112
  right
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap ask_price buy_cap j head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_maximum_profit_safety_wit_112_split_goal_1 dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap ask_price buy_cap j head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31))
    | (solve | Goal_apply (proof_of_maximum_profit_safety_wit_112_split_goal_2 dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap ask_price buy_cap j head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31))
    | trivial

theorem proof_of_maximum_profit_safety_wit_119_split_goal_1 : maximum_profit_safety_wit_119_split_goal_1 := by
  unfold maximum_profit_safety_wit_119_split_goal_1
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap ask_price buy_cap j head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have Hdone := PreH29.1
  have Hcell := StockDaysDone_cell_bounded__safety_buy ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i source_day (j - 1) __default__List_Z PreH28 Hdone PreH31 (by omega) (by omega)
  unfold STOCK_NEG_INF STOCK_MAX_PROFIT at Hcell
  have hprod := product_bounds (j - 1) ask_price (by omega) (by omega)
  have hjprod := product_bounds j ask_price (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX, INT_MIN]
  omega

theorem proof_of_maximum_profit_safety_wit_119_split_goal_2 : maximum_profit_safety_wit_119_split_goal_2 := by
  unfold maximum_profit_safety_wit_119_split_goal_2
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap ask_price buy_cap j head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have Hdone := PreH29.1
  have Hcell := StockDaysDone_cell_bounded__safety_buy ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i source_day (j - 1) __default__List_Z PreH28 Hdone PreH31 (by omega) (by omega)
  unfold STOCK_NEG_INF STOCK_MAX_PROFIT at Hcell
  have hprod := product_bounds (j - 1) ask_price (by omega) (by omega)
  have hjprod := product_bounds j ask_price (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX, INT_MIN]
  omega

theorem proof_of_maximum_profit_safety_wit_119 : maximum_profit_safety_wit_119 := by
  unfold maximum_profit_safety_wit_119
  right
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap ask_price buy_cap j head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_maximum_profit_safety_wit_119_split_goal_1 dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap ask_price buy_cap j head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31))
    | (solve | Goal_apply (proof_of_maximum_profit_safety_wit_119_split_goal_2 dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap ask_price buy_cap j head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31))
    | trivial

theorem proof_of_maximum_profit_safety_wit_126_split_goal_1 : maximum_profit_safety_wit_126_split_goal_1 := by
  unfold maximum_profit_safety_wit_126_split_goal_1
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l incoming_score last_index tail head buy_cap ask_price sell_cap bid_price source_day j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  have Hdone := PreH30.1
  have Hcell := StockDaysDone_cell_bounded__safety_buy ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i source_day last_index __default__List_Z PreH29 Hdone PreH32 (by omega) (by omega)
  unfold STOCK_NEG_INF STOCK_MAX_PROFIT at Hcell
  have hprod := product_bounds last_index ask_price (by omega) (by omega)
  have hjprod := product_bounds j ask_price (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX, INT_MIN]
  omega

theorem proof_of_maximum_profit_safety_wit_126_split_goal_2 : maximum_profit_safety_wit_126_split_goal_2 := by
  unfold maximum_profit_safety_wit_126_split_goal_2
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l incoming_score last_index tail head buy_cap ask_price sell_cap bid_price source_day j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  have Hdone := PreH30.1
  have Hcell := StockDaysDone_cell_bounded__safety_buy ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i source_day last_index __default__List_Z PreH29 Hdone PreH32 (by omega) (by omega)
  unfold STOCK_NEG_INF STOCK_MAX_PROFIT at Hcell
  have hprod := product_bounds last_index ask_price (by omega) (by omega)
  have hjprod := product_bounds j ask_price (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX, INT_MIN]
  omega

theorem proof_of_maximum_profit_safety_wit_126 : maximum_profit_safety_wit_126 := by
  unfold maximum_profit_safety_wit_126
  right
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l incoming_score last_index tail head buy_cap ask_price sell_cap bid_price source_day j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_maximum_profit_safety_wit_126_split_goal_1 dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l incoming_score last_index tail head buy_cap ask_price sell_cap bid_price source_day j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32))
    | (solve | Goal_apply (proof_of_maximum_profit_safety_wit_126_split_goal_2 dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l incoming_score last_index tail head buy_cap ask_price sell_cap bid_price source_day j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32))
    | trivial

theorem proof_of_maximum_profit_safety_wit_135_split_goal_1 : maximum_profit_safety_wit_135_split_goal_1 := by
  unfold maximum_profit_safety_wit_135_split_goal_1
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap ask_price buy_cap j best_index head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have Hdone := PreH28.1
  have Hcell := StockDaysDone_cell_bounded__safety_buy ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i source_day best_index __default__List_Z PreH27 Hdone PreH30 (by omega) (by omega)
  unfold STOCK_NEG_INF STOCK_MAX_PROFIT at Hcell
  have hprod := product_bounds best_index ask_price (by omega) (by omega)
  have hjprod := product_bounds j ask_price (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX, INT_MIN]
  omega

theorem proof_of_maximum_profit_safety_wit_135_split_goal_2 : maximum_profit_safety_wit_135_split_goal_2 := by
  unfold maximum_profit_safety_wit_135_split_goal_2
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap ask_price buy_cap j best_index head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have Hdone := PreH28.1
  have Hcell := StockDaysDone_cell_bounded__safety_buy ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i source_day best_index __default__List_Z PreH27 Hdone PreH30 (by omega) (by omega)
  unfold STOCK_NEG_INF STOCK_MAX_PROFIT at Hcell
  have hprod := product_bounds best_index ask_price (by omega) (by omega)
  have hjprod := product_bounds j ask_price (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX, INT_MIN]
  omega

theorem proof_of_maximum_profit_safety_wit_135 : maximum_profit_safety_wit_135 := by
  unfold maximum_profit_safety_wit_135
  right
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap ask_price buy_cap j best_index head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_maximum_profit_safety_wit_135_split_goal_1 dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap ask_price buy_cap j best_index head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30))
    | (solve | Goal_apply (proof_of_maximum_profit_safety_wit_135_split_goal_2 dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap ask_price buy_cap j best_index head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30))
    | trivial

theorem proof_of_maximum_profit_safety_wit_137_split_goal_1 : maximum_profit_safety_wit_137_split_goal_1 := by
  unfold maximum_profit_safety_wit_137_split_goal_1
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap ask_price buy_cap j best_index head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have Hdone := PreH28.1
  have Hcell := StockDaysDone_cell_bounded__safety_buy ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i source_day best_index __default__List_Z PreH27 Hdone PreH30 (by omega) (by omega)
  unfold STOCK_NEG_INF STOCK_MAX_PROFIT at Hcell
  have hprod := product_bounds best_index ask_price (by omega) (by omega)
  have hjprod := product_bounds j ask_price (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX, INT_MIN]
  omega

theorem proof_of_maximum_profit_safety_wit_137_split_goal_2 : maximum_profit_safety_wit_137_split_goal_2 := by
  unfold maximum_profit_safety_wit_137_split_goal_2
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap ask_price buy_cap j best_index head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have Hdone := PreH28.1
  have Hcell := StockDaysDone_cell_bounded__safety_buy ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i source_day best_index __default__List_Z PreH27 Hdone PreH30 (by omega) (by omega)
  unfold STOCK_NEG_INF STOCK_MAX_PROFIT at Hcell
  have hprod := product_bounds best_index ask_price (by omega) (by omega)
  have hjprod := product_bounds j ask_price (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX, INT_MIN]
  omega

theorem proof_of_maximum_profit_safety_wit_137 : maximum_profit_safety_wit_137 := by
  unfold maximum_profit_safety_wit_137
  right
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap ask_price buy_cap j best_index head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_maximum_profit_safety_wit_137_split_goal_1 dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap ask_price buy_cap j best_index head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30))
    | (solve | Goal_apply (proof_of_maximum_profit_safety_wit_137_split_goal_2 dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap ask_price buy_cap j best_index head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30))
    | trivial

theorem proof_of_maximum_profit_safety_wit_145_split_goal_1 : maximum_profit_safety_wit_145_split_goal_1 := by
  unfold maximum_profit_safety_wit_145_split_goal_1
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have hb := PreH19.2.2.2.2.1
  dump_pre_spatial
  simp only [INT_MAX, INT_MIN]
  omega

theorem proof_of_maximum_profit_safety_wit_145_split_goal_2 : maximum_profit_safety_wit_145_split_goal_2 := by
  unfold maximum_profit_safety_wit_145_split_goal_2
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have hb := PreH19.2.2.2.2.1
  dump_pre_spatial
  simp only [INT_MAX, INT_MIN]
  omega

theorem proof_of_maximum_profit_safety_wit_145 : maximum_profit_safety_wit_145 := by
  unfold maximum_profit_safety_wit_145
  right
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_maximum_profit_safety_wit_145_split_goal_1 dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21))
    | (solve | Goal_apply (proof_of_maximum_profit_safety_wit_145_split_goal_2 dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21))
    | trivial

theorem proof_of_maximum_profit_safety_wit_146_split_goal_1 : maximum_profit_safety_wit_146_split_goal_1 := by
  unfold maximum_profit_safety_wit_146_split_goal_1
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width buy_cap i ask_price PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have hb := PreH9.2.2.2.2.1
  dump_pre_spatial
  simp only [INT_MAX, INT_MIN]
  omega

theorem proof_of_maximum_profit_safety_wit_146_split_goal_2 : maximum_profit_safety_wit_146_split_goal_2 := by
  unfold maximum_profit_safety_wit_146_split_goal_2
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width buy_cap i ask_price PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have hb := PreH9.2.2.2.2.1
  dump_pre_spatial
  simp only [INT_MAX, INT_MIN]
  omega

theorem proof_of_maximum_profit_safety_wit_146 : maximum_profit_safety_wit_146 := by
  unfold maximum_profit_safety_wit_146
  right
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width buy_cap i ask_price PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_maximum_profit_safety_wit_146_split_goal_1 dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width buy_cap i ask_price PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11))
    | (solve | Goal_apply (proof_of_maximum_profit_safety_wit_146_split_goal_2 dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width buy_cap i ask_price PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11))
    | trivial

theorem proof_of_maximum_profit_entail_wit_3_split_goal_1 : maximum_profit_entail_wit_3_split_goal_1 := by
  unfold maximum_profit_entail_wit_3_split_goal_1
  intro wait_days_pre max_stock_pre days_pre dp_init sell_l buy_l bp_l ap_l width q_init neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact ⟨by omega, PreH13, by intro r stock hr hs; omega⟩

theorem proof_of_maximum_profit_entail_wit_3 : maximum_profit_entail_wit_3 := by
  unfold maximum_profit_entail_wit_3
  right
  intro wait_days_pre max_stock_pre days_pre dp_init sell_l buy_l bp_l ap_l width q_init neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_3_split_goal_1 wait_days_pre max_stock_pre days_pre dp_init sell_l buy_l bp_l ap_l width q_init neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13))
    | trivial

theorem proof_of_maximum_profit_entail_wit_4_split_goal_1 : maximum_profit_entail_wit_4_split_goal_1 := by
  unfold maximum_profit_entail_wit_4_split_goal_1
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have hshape := PreH13.2.1
  have hlen := hshape.1
  have hrow := hshape.2 i (by omega)
  refine ⟨by omega, ?_, ?_⟩
  · rw [← same_index_different_default i dp_l_2 __default__List_Z (by omega)]
    exact hrow
  · intro stock hs
    omega

theorem proof_of_maximum_profit_entail_wit_4 : maximum_profit_entail_wit_4 := by
  unfold maximum_profit_entail_wit_4
  right
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_4_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14))
    | trivial

theorem proof_of_maximum_profit_entail_wit_5_1 : maximum_profit_entail_wit_5_1 := by
  unfold maximum_profit_entail_wit_5_1
  left
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hvalue : 0 = StockInitialCell i j := by
    simp [StockInitialCell, show i = 0 by omega, show j = 0 by omega]
  have hstep := stock_fill_update_step__init_copy dp_l_2 days_pre max_stock_pre i j 0 __default__List_Z PreH17 PreH18 (by omega) (by omega) hvalue
  obtain ⟨hrows,hcells⟩ := hstep
  have hshape := hrows.2.1
  sep_apply (StockProofInternal.merge_cell dp_pre (days_pre+1) width i j (0:Int) dp_l_2 __default__List_Z (by omega) (by omega))
  Exists queue_l_2 (replace_Znth i (replace_Znth j 0 (Znth i dp_l_2 __default__List_Z)) dp_l_2)
  finish_entail

theorem proof_of_maximum_profit_entail_wit_5_2 : maximum_profit_entail_wit_5_2 := by
  unfold maximum_profit_entail_wit_5_2
  left
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hvalue : neg_inf = StockInitialCell i j := by
    simp [StockInitialCell, show i ≠ 0 by omega, STOCK_NEG_INF]; omega
  have hstep := stock_fill_update_step__init_copy dp_l_2 days_pre max_stock_pre i j neg_inf __default__List_Z PreH16 PreH17 (by omega) (by omega) hvalue
  obtain ⟨hrows,hcells⟩ := hstep
  have hshape := hrows.2.1
  sep_apply (StockProofInternal.merge_cell dp_pre (days_pre+1) width i j neg_inf dp_l_2 __default__List_Z (by omega) (by omega))
  Exists queue_l_2 (replace_Znth i (replace_Znth j neg_inf (Znth i dp_l_2 __default__List_Z)) dp_l_2)
  finish_entail

theorem proof_of_maximum_profit_entail_wit_5_3 : maximum_profit_entail_wit_5_3 := by
  unfold maximum_profit_entail_wit_5_3
  left
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hvalue : neg_inf = StockInitialCell i j := by
    simp [StockInitialCell, show i = 0 by omega, show j ≠ 0 by omega, STOCK_NEG_INF]; omega
  have hstep := stock_fill_update_step__init_copy dp_l_2 days_pre max_stock_pre i j neg_inf __default__List_Z PreH17 PreH18 (by omega) (by omega) hvalue
  obtain ⟨hrows,hcells⟩ := hstep
  have hshape := hrows.2.1
  sep_apply (StockProofInternal.merge_cell dp_pre (days_pre+1) width i j neg_inf dp_l_2 __default__List_Z (by omega) (by omega))
  Exists queue_l_2 (replace_Znth i (replace_Znth j neg_inf (Znth i dp_l_2 __default__List_Z)) dp_l_2)
  finish_entail

theorem proof_of_maximum_profit_entail_wit_6_split_goal_1 : maximum_profit_entail_wit_6_split_goal_1 := by
  unfold maximum_profit_entail_wit_6_split_goal_1
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hshape := PreH15.2.1
  have hlen := hshape.1
  refine ⟨by omega, hshape, ?_⟩
  intro r stock hr hs
  by_cases hri : r < i
  · exact PreH15.2.2 r stock (by omega) hs
  · have he : r = i := by omega
    subst r
    rw [same_index_different_default i dp_l_2 __default__List_Z (by omega)]
    exact ⟨PreH16.2.1, PreH16.2.2 stock (by omega)⟩

theorem proof_of_maximum_profit_entail_wit_6 : maximum_profit_entail_wit_6 := by
  unfold maximum_profit_entail_wit_6
  right
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_6_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | trivial

theorem proof_of_maximum_profit_entail_wit_7_split_goal_1 : maximum_profit_entail_wit_7_split_goal_1 := by
  unfold maximum_profit_entail_wit_7_split_goal_1
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have he : i = days_pre + 1 := by omega
  subst i
  exact (stock_completed_initial_table_days_done__init_copy ap_l bp_l buy_l sell_l dp_l_2 days_pre max_stock_pre wait_days_pre (by omega) PreH12 PreH13).1

theorem proof_of_maximum_profit_entail_wit_7 : maximum_profit_entail_wit_7 := by
  unfold maximum_profit_entail_wit_7
  right
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_7_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14))
    | trivial

theorem proof_of_maximum_profit_entail_wit_9_split_goal_1 : maximum_profit_entail_wit_9_split_goal_1 := by
  unfold maximum_profit_entail_wit_9_split_goal_1
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  refine ⟨PreH13, by omega, by omega, ?_⟩
  intro stock hs
  omega

theorem proof_of_maximum_profit_entail_wit_9 : maximum_profit_entail_wit_9 := by
  unfold maximum_profit_entail_wit_9
  right
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_9_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14))
    | trivial

theorem proof_of_maximum_profit_entail_wit_10 : maximum_profit_entail_wit_10 := by
  unfold maximum_profit_entail_wit_10
  left
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  sep_apply (StockProofInternal.restore_cell dp_pre (days_pre+1) width (i-1) j dp_l __default__List_Z (by omega) (by omega))
  Exists queue_l_2 dp_l
  finish_entail

theorem proof_of_maximum_profit_entail_wit_11 : maximum_profit_entail_wit_11 := by
  unfold maximum_profit_entail_wit_11
  left
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i j previous_value __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hshapeA := PreH16.1.1
  have hlenA := hshapeA.1
  have hlen := PreH17.1
  have hask : Zlength ap_l = days_pre := by omega
  have hprev : 0 ≤ i-1 ∧ i-1 < Zlength dp_l_2 := by omega
  have hcur : 0 ≤ i ∧ i < Zlength dp_l_2 := by omega
  have hv : previous_value = Znth j (Znth (i-1) dp_l_2 []) 0 := by
    rw [← Znth_indep dp_l_2 (i-1) __default__List_Z [] hprev]
    exact PreH14
  have hstep := stock_copy_update_step__init_copy ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i j previous_value hshapeA PreH16 hv (by omega) (by omega) (by omega)
  obtain ⟨hcopy,hshape⟩ := hstep
  rw [← Znth_indep dp_l_2 i __default__List_Z [] hcur] at hcopy hshape
  rw [hask] at hshape
  sep_apply (StockProofInternal.merge_cell dp_pre (days_pre+1) width i j previous_value dp_l_2 __default__List_Z (by omega) (by omega))
  Exists queue_l_2 (replace_Znth i (replace_Znth j previous_value (Znth i dp_l_2 __default__List_Z)) dp_l_2)
  finish_entail

theorem proof_of_maximum_profit_entail_wit_12_split_goal_1 : maximum_profit_entail_wit_12_split_goal_1 := by
  unfold maximum_profit_entail_wit_12_split_goal_1
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hdaily := PreH15.2.2.2.2.2.2 i (by omega)
  have hbuy := hdaily.2.2.1
  rcases PreH16 with ⟨HD, Hi, Hcol, Hcopy⟩
  refine ⟨HD, Hi, by omega, Hcopy 0 (by omega), ?_⟩
  intro stock hs
  simp only [if_neg (show ¬ stock < 1 by omega)]
  exact Hcopy stock (by omega)

theorem proof_of_maximum_profit_entail_wit_12_split_goal_2 : maximum_profit_entail_wit_12_split_goal_2 := by
  unfold maximum_profit_entail_wit_12_split_goal_2
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hdaily := PreH15.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega

theorem proof_of_maximum_profit_entail_wit_12_split_goal_3 : maximum_profit_entail_wit_12_split_goal_3 := by
  unfold maximum_profit_entail_wit_12_split_goal_3
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hdaily := PreH15.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega

theorem proof_of_maximum_profit_entail_wit_12_split_goal_4 : maximum_profit_entail_wit_12_split_goal_4 := by
  unfold maximum_profit_entail_wit_12_split_goal_4
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hdaily := PreH15.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega

theorem proof_of_maximum_profit_entail_wit_12_split_goal_5 : maximum_profit_entail_wit_12_split_goal_5 := by
  unfold maximum_profit_entail_wit_12_split_goal_5
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hdaily := PreH15.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega

theorem proof_of_maximum_profit_entail_wit_12_split_goal_6 : maximum_profit_entail_wit_12_split_goal_6 := by
  unfold maximum_profit_entail_wit_12_split_goal_6
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hdaily := PreH15.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega

theorem proof_of_maximum_profit_entail_wit_12 : maximum_profit_entail_wit_12 := by
  unfold maximum_profit_entail_wit_12
  right
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_12_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_12_split_goal_2 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_12_split_goal_3 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_12_split_goal_4 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_12_split_goal_5 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_12_split_goal_6 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | trivial

end SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_manual_part1
