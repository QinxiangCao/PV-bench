import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_goal
import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_auto
import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_helpers
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_manual_part3
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

theorem proof_of_maximum_profit_entail_wit_26_1 : maximum_profit_entail_wit_26_1 := by
  unfold maximum_profit_entail_wit_26_1
  left
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i j source_day best_index head tail bid_price sell_cap sell_candidate __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  have hlen := PreH29.1
  have hsrc : 0 ≤ source_day ∧ source_day < Zlength dp_l_2 := by omega
  have hcur : 0 ≤ i ∧ i < Zlength dp_l_2 := by omega
  have hsdef := Znth_indep dp_l_2 source_day __default__List_Z [] hsrc
  have hidef := Znth_indep dp_l_2 i __default__List_Z [] hcur
  have hcompare := PreH1
  rw [hidef] at hcompare
  have hval : sell_candidate = StockSellScore dp_l_2 source_day bid_price best_index - j*bid_price := by
    unfold StockSellScore
    rw [← hsdef]
    exact PreH27
  have hcell := StockProofInternal.sell_cell_queue ap_l bp_l buy_l sell_l dp_l_2 days_pre max_stock_pre wait_days_pre i source_day j queue_l_2 bid_price sell_cap head tail best_index sell_candidate PreH25 PreH26 (by omega) PreH28 (by omega) PreH19 PreH23 PreH24 hval
  rw [Int.max_eq_right (by omega)] at hcell
  have hstep := StockProofInternal.sell_replace_step ap_l bp_l buy_l sell_l dp_l_2 days_pre max_stock_pre wait_days_pre i source_day j sell_candidate PreH25 (by omega) PreH26 (by omega) hcell
  obtain ⟨hp,hs⟩ := hstep
  rw [← hidef] at hp hs
  have hq := StockProofInternal.sell_queue_replace dp_l_2 queue_l_2 source_day bid_price (j+1) (j+sell_cap) head tail i (replace_Znth j sell_candidate (Znth i dp_l_2 __default__List_Z)) hsrc hcur (by omega) PreH28
  have hqnext : StockSellQueue (replace_Znth i (replace_Znth j sell_candidate (Znth i dp_l_2 __default__List_Z)) dp_l_2) queue_l_2 source_day bid_price (j-1+2) (j-1+sell_cap+1) head tail := by
    simpa only [show j-1+2=j+1 by omega, show j-1+sell_cap+1=j+sell_cap by omega] using hq
  have hdaily := PreH25.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  have heq := PreH26.2.2.1
  have hrange := PreH26.2.2.2.1
  sep_apply (StockProofInternal.merge_cell dp_pre (days_pre+1) width i j sell_candidate dp_l_2 __default__List_Z (by omega) (by omega))
  Exists queue_l_2 (replace_Znth i (replace_Znth j sell_candidate (Znth i dp_l_2 __default__List_Z)) dp_l_2)
  finish_entail

theorem proof_of_maximum_profit_entail_wit_26_2 : maximum_profit_entail_wit_26_2 := by
  unfold maximum_profit_entail_wit_26_2
  left
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i j source_day best_index head tail bid_price sell_cap sell_candidate __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  have hlen := PreH29.1
  have hsrc : 0 ≤ source_day ∧ source_day < Zlength dp_l_2 := by omega
  have hcur : 0 ≤ i ∧ i < Zlength dp_l_2 := by omega
  have hsdef := Znth_indep dp_l_2 source_day __default__List_Z [] hsrc
  have hidef := Znth_indep dp_l_2 i __default__List_Z [] hcur
  have hcompare := PreH1
  rw [hidef] at hcompare
  have hval : sell_candidate = StockSellScore dp_l_2 source_day bid_price best_index - j*bid_price := by
    unfold StockSellScore
    rw [← hsdef]
    exact PreH27
  have hcell := StockProofInternal.sell_cell_queue ap_l bp_l buy_l sell_l dp_l_2 days_pre max_stock_pre wait_days_pre i source_day j queue_l_2 bid_price sell_cap head tail best_index sell_candidate PreH25 PreH26 (by omega) PreH28 (by omega) PreH19 PreH23 PreH24 hval
  rw [Int.max_eq_left (by omega)] at hcell
  have hp : StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day (j-1) := by
    rcases PreH26 with ⟨HD,Hi,Hsrc,Hsr,Hj,Hcopy,Hcells,Hlast⟩
    refine ⟨HD,Hi,Hsrc,Hsr,by omega,?_,?_,Hlast⟩
    · intro stock hs; exact Hcopy stock (by omega)
    · intro stock hs
      by_cases he : stock = j
      · subst stock; exact hcell
      · exact Hcells stock (by omega)
  have hq := PreH28
  have hqnext : StockSellQueue dp_l_2 queue_l_2 source_day bid_price (j-1+2) (j-1+sell_cap+1) head tail := by
    simpa only [show j-1+2=j+1 by omega, show j-1+sell_cap+1=j+sell_cap by omega] using hq
  have hdaily := PreH25.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  have heq := PreH26.2.2.1
  have hrange := PreH26.2.2.2.1
  sep_apply (StockProofInternal.restore_cell dp_pre (days_pre+1) width i j dp_l_2 __default__List_Z (by omega) (by omega))
  Exists queue_l_2 dp_l_2
  finish_entail

theorem proof_of_maximum_profit_entail_wit_26_3_split_goal_1 : maximum_profit_entail_wit_26_3_split_goal_1 := by
  unfold maximum_profit_entail_wit_26_3_split_goal_1
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  simpa only [show j - 1 + 2 = j + 1 by omega, show j - 1 + sell_cap + 1 = j + sell_cap by omega] using PreH24

theorem proof_of_maximum_profit_entail_wit_26_3_split_goal_2 : maximum_profit_entail_wit_26_3_split_goal_2 := by
  unfold maximum_profit_entail_wit_26_3_split_goal_2
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  rcases PreH23 with ⟨HD,Hi,Hsrc,Hsr,Hj,Hcopy,Hcells,Hlast⟩
  refine ⟨HD,Hi,Hsrc,Hsr,by omega,?_,?_,Hlast⟩
  · intro stock hs; exact Hcopy stock (by omega)
  · intro stock hs
    by_cases he : stock = j
    · subst stock
      refine ⟨⟨0,Or.inl ⟨rfl,Hcopy j (by omega)⟩⟩,?_⟩
      intro amount candidate hc
      rcases hc with ⟨ha,hc⟩ | ⟨ha,hs,hn,hc⟩
      · have hv := Hcopy j (by omega); omega
      · have hrow := PreH25.2 source_day (by omega)
        have hq := PreH24.2.2.2 (j+amount) ⟨by omega,by omega,hn,by omega⟩
        obtain ⟨pos,hp,_⟩ := hq
        omega
    · exact Hcells stock (by omega)

theorem proof_of_maximum_profit_entail_wit_26_3_split_goal_3 : maximum_profit_entail_wit_26_3_split_goal_3 := by
  unfold maximum_profit_entail_wit_26_3_split_goal_3
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hb := PreH22
  unfold StockInputsBounded at hb
  have hdaily := hb.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  rcases PreH23 with ⟨HD,Hi,Hsrc,Hsr,Hj,Hcopy,Hrest⟩
  omega

theorem proof_of_maximum_profit_entail_wit_26_3_split_goal_4 : maximum_profit_entail_wit_26_3_split_goal_4 := by
  unfold maximum_profit_entail_wit_26_3_split_goal_4
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hb := PreH22
  unfold StockInputsBounded at hb
  have hdaily := hb.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  rcases PreH23 with ⟨HD,Hi,Hsrc,Hsr,Hj,Hcopy,Hrest⟩
  omega

theorem proof_of_maximum_profit_entail_wit_26_3_split_goal_5 : maximum_profit_entail_wit_26_3_split_goal_5 := by
  unfold maximum_profit_entail_wit_26_3_split_goal_5
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hb := PreH22
  unfold StockInputsBounded at hb
  have hdaily := hb.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  rcases PreH23 with ⟨HD,Hi,Hsrc,Hsr,Hj,Hcopy,Hrest⟩
  omega

theorem proof_of_maximum_profit_entail_wit_26_3_split_goal_6 : maximum_profit_entail_wit_26_3_split_goal_6 := by
  unfold maximum_profit_entail_wit_26_3_split_goal_6
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hb := PreH22
  unfold StockInputsBounded at hb
  have hdaily := hb.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  rcases PreH23 with ⟨HD,Hi,Hsrc,Hsr,Hj,Hcopy,Hrest⟩
  omega

theorem proof_of_maximum_profit_entail_wit_26_3_split_goal_7 : maximum_profit_entail_wit_26_3_split_goal_7 := by
  unfold maximum_profit_entail_wit_26_3_split_goal_7
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  rcases PreH23 with ⟨HD,Hi,Hsrc,Hsr,Hj,Hrest⟩
  omega

theorem proof_of_maximum_profit_entail_wit_26_3_split_goal_8 : maximum_profit_entail_wit_26_3_split_goal_8 := by
  unfold maximum_profit_entail_wit_26_3_split_goal_8
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  rcases PreH23 with ⟨HD,Hi,Hsrc,Hsr,Hj,Hrest⟩
  omega

theorem proof_of_maximum_profit_entail_wit_26_3 : maximum_profit_entail_wit_26_3 := by
  unfold maximum_profit_entail_wit_26_3
  right
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_26_3_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_26_3_split_goal_2 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_26_3_split_goal_3 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_26_3_split_goal_4 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_26_3_split_goal_5 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_26_3_split_goal_6 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_26_3_split_goal_7 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_26_3_split_goal_8 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25))
    | trivial

end SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_manual_part3
