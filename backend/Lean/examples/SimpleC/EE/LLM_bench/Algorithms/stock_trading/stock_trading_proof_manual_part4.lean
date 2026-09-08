import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_goal
import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_auto
import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_helpers
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_manual_part4
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

theorem proof_of_maximum_profit_entail_wit_27_split_goal_1 : maximum_profit_entail_wit_27_split_goal_1 := by
  unfold maximum_profit_entail_wit_27_split_goal_1
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro pos hp; omega
  · intro l r hr; omega
  · intro candidate hc
    rcases hc with ⟨hc0,hcl,hcf,hcr⟩
    omega

theorem proof_of_maximum_profit_entail_wit_27_split_goal_2 : maximum_profit_entail_wit_27_split_goal_2 := by
  unfold maximum_profit_entail_wit_27_split_goal_2
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  rcases PreH28 with ⟨HD,Hi,Hsrc,Hsr,Hj,Hcopy,Hsell,Hmaxeq⟩
  refine ⟨HD,Hi,rfl,by omega,by omega,?_,?_⟩
  · intro stock hs
    have he : stock = 0 := by omega
    subst stock
    have hsell := Hsell 0 (by omega)
    rw [Hsrc] at hsell
    refine ⟨⟨⟨0,Or.inl ⟨rfl,hsell⟩⟩,?_⟩,⟨_,hsell⟩⟩
    intro amount candidate hc
    rcases hc with ⟨ha,hc⟩ | ⟨ha,hamt,hn,hc⟩
    · obtain ⟨sa,hsa⟩ := hc.1
      exact hsell.2 sa candidate hsa
    · omega
  · intro stock hs
    by_cases he : stock = max_stock_pre
    · subst stock
      refine ⟨⟨0,Or.inl ⟨rfl,Hmaxeq⟩⟩,?_⟩
      intro amount candidate hc
      rcases hc with ⟨ha,hc⟩ | ⟨ha,hamt,hn,hc⟩ <;> omega
    · rw [← Hsrc]
      exact Hsell stock (by omega)

theorem proof_of_maximum_profit_entail_wit_27_split_goal_3 : maximum_profit_entail_wit_27_split_goal_3 := by
  unfold maximum_profit_entail_wit_27_split_goal_3
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have hb := PreH27
  unfold StockInputsBounded at hb
  have hdaily := hb.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega

theorem proof_of_maximum_profit_entail_wit_27_split_goal_4 : maximum_profit_entail_wit_27_split_goal_4 := by
  unfold maximum_profit_entail_wit_27_split_goal_4
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have hb := PreH27
  unfold StockInputsBounded at hb
  have hdaily := hb.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega

theorem proof_of_maximum_profit_entail_wit_27_split_goal_5 : maximum_profit_entail_wit_27_split_goal_5 := by
  unfold maximum_profit_entail_wit_27_split_goal_5
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have hb := PreH27
  unfold StockInputsBounded at hb
  have hdaily := hb.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega

theorem proof_of_maximum_profit_entail_wit_27_split_goal_6 : maximum_profit_entail_wit_27_split_goal_6 := by
  unfold maximum_profit_entail_wit_27_split_goal_6
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have hb := PreH27
  unfold StockInputsBounded at hb
  have hdaily := hb.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega

theorem proof_of_maximum_profit_entail_wit_27 : maximum_profit_entail_wit_27 := by
  unfold maximum_profit_entail_wit_27
  right
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_27_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_27_split_goal_2 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_27_split_goal_3 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_27_split_goal_4 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_27_split_goal_5 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_27_split_goal_6 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30))
    | trivial

theorem proof_of_maximum_profit_entail_wit_28_split_goal_1 : maximum_profit_entail_wit_28_split_goal_1 := by
  unfold maximum_profit_entail_wit_28_split_goal_1
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j buy_cap ask_price sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  left
  rw [← PreH9]
  exact PreH27

theorem proof_of_maximum_profit_entail_wit_28_split_goal_2 : maximum_profit_entail_wit_28_split_goal_2 := by
  unfold maximum_profit_entail_wit_28_split_goal_2
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j buy_cap ask_price sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  have hb := PreH25
  unfold StockInputsBounded at hb
  rcases hb with ⟨ha,hb,hc,hd,he,hf,hg⟩
  omega

theorem proof_of_maximum_profit_entail_wit_28_split_goal_3 : maximum_profit_entail_wit_28_split_goal_3 := by
  unfold maximum_profit_entail_wit_28_split_goal_3
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j buy_cap ask_price sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  have hb := PreH25
  unfold StockInputsBounded at hb
  rcases hb with ⟨ha,hb,hc,hd,he,hf,hg⟩
  omega

theorem proof_of_maximum_profit_entail_wit_28 : maximum_profit_entail_wit_28 := by
  unfold maximum_profit_entail_wit_28
  right
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j buy_cap ask_price sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_28_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j buy_cap ask_price sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_28_split_goal_2 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j buy_cap ask_price sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28))
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_28_split_goal_3 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j buy_cap ask_price sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28))
    | trivial

theorem proof_of_maximum_profit_entail_wit_29_split_goal_1 : maximum_profit_entail_wit_29_split_goal_1 := by
  unfold maximum_profit_entail_wit_29_split_goal_1
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head buy_cap ask_price sell_cap bid_price j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  rw [← PreH14]
  rcases PreH32 with hq | hq
  · right
    rcases hq with ⟨hb,he,ho,hc⟩
    have hhead := he head (by omega)
    have hheadrange := hhead.2.2.2
    refine ⟨by omega,?_,?_,?_⟩
    · intro pos hp
      rcases he pos (by omega) with ⟨hp0,hpl,hpv,hpr⟩
      have hh := (ho head pos (by omega)).1
      exact ⟨hp0,hpl,hpv,by omega⟩
    · intro l r hr; exact ho l r (by omega)
    · intro candidate hh
      rcases hh with ⟨h0,hl,hv,hr⟩
      obtain ⟨pos,hp,hindex,hscore⟩ := hc candidate ⟨h0,hl,hv,by omega⟩
      have hne : pos ≠ head := by intro heq; subst pos; omega
      exact ⟨pos,by omega,hindex,hscore⟩
  · have hh := (hq.2.1 head (by omega)).2.2.2
    omega

theorem proof_of_maximum_profit_entail_wit_29 : maximum_profit_entail_wit_29 := by
  unfold maximum_profit_entail_wit_29
  right
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head buy_cap ask_price sell_cap bid_price j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_29_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head buy_cap ask_price sell_cap bid_price j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33))
    | trivial

theorem proof_of_maximum_profit_entail_wit_30_1_split_goal_1 : maximum_profit_entail_wit_30_1_split_goal_1 := by
  unfold maximum_profit_entail_wit_30_1_split_goal_1
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head buy_cap ask_price sell_cap bid_price j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  rw [← PreH13]
  rcases PreH31 with hq | hq
  · rcases hq with ⟨hb,he,ho,hc⟩
    refine ⟨hb,?_,?_,?_⟩
    · intro pos hp; omega
    · intro l r hr; omega
    · intro candidate hh
      rcases hh with ⟨h0,hl,hv,hr⟩
      exact hc candidate ⟨h0,hl,hv,by omega⟩
  · exact hq

theorem proof_of_maximum_profit_entail_wit_30_1 : maximum_profit_entail_wit_30_1 := by
  unfold maximum_profit_entail_wit_30_1
  right
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head buy_cap ask_price sell_cap bid_price j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_30_1_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head buy_cap ask_price sell_cap bid_price j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32))
    | trivial

theorem proof_of_maximum_profit_entail_wit_30_2_split_goal_1 : maximum_profit_entail_wit_30_2_split_goal_1 := by
  unfold maximum_profit_entail_wit_30_2_split_goal_1
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head buy_cap ask_price sell_cap bid_price j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  rw [← PreH14]
  rcases PreH32 with hq | hq
  · rcases hq with ⟨hb,he,ho,hc⟩
    refine ⟨hb,?_,ho,?_⟩
    · intro pos hp
      rcases he pos hp with ⟨h0,hl,hv,hr⟩
      have hlo : j-buy_cap ≤ Znth pos queue_l_2 0 := by
        by_cases heq : pos = head
        · subst pos; omega
        · have hh := (ho head pos (by omega)).1
          omega
      exact ⟨h0,hl,hv,by omega⟩
    · intro candidate hh
      rcases hh with ⟨h0,hl,hv,hr⟩
      exact hc candidate ⟨h0,hl,hv,by omega⟩
  · exact hq

theorem proof_of_maximum_profit_entail_wit_30_2 : maximum_profit_entail_wit_30_2 := by
  unfold maximum_profit_entail_wit_30_2
  right
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head buy_cap ask_price sell_cap bid_price j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intros; Goal_apply (proof_of_maximum_profit_entail_wit_30_2_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head buy_cap ask_price sell_cap bid_price j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33))
    | trivial

theorem proof_of_maximum_profit_entail_wit_31_1 : maximum_profit_entail_wit_31_1 := by
  unfold maximum_profit_entail_wit_31_1
  left
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l neg_inf width i source_day bid_price sell_cap ask_price buy_cap j head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have hlen := PreH31.1
  have hrow := PreH31.2 source_day (by omega)
  have he := Znth_indep dp_l source_day __default__List_Z [] (by omega)
  have hn : Znth (j-1) (Znth source_day dp_l []) 0 ≠ STOCK_NEG_INF := by
    rw [he] at PreH2
    unfold STOCK_NEG_INF
    omega
  have hq : StockBuyQueue dp_l queue_l source_day ask_price (j-buy_cap) ((j-1)-1) head tail := by
    simpa only [show j-1-1=j-2 by omega] using PreH30
  have hp := StockBuyQueue_begin_popping__buy_pop_append dp_l queue_l source_day ask_price (j-buy_cap) (j-1) head tail (by omega) (by omega) hn hq
  have hlast := PreH30.2.1 (tail-1) (by omega)
  rcases hlast with ⟨hl0,hll,hlv,hlr⟩
  sep_apply (StockProofInternal.restore_cell dp_pre (days_pre+1) width source_day (j-1) dp_l __default__List_Z (by omega) (by omega))
  Exists queue_l dp_l
  finish_entail

theorem proof_of_maximum_profit_entail_wit_31_2 : maximum_profit_entail_wit_31_2 := by
  unfold maximum_profit_entail_wit_31_2
  left
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l neg_inf width i source_day bid_price sell_cap ask_price buy_cap j head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have hlen := PreH31.1
  have hrow := PreH31.2 source_day (by omega)
  have he := Znth_indep dp_l source_day __default__List_Z [] (by omega)
  have hn : Znth (j-1) (Znth source_day dp_l []) 0 ≠ STOCK_NEG_INF := by
    rw [he] at PreH2
    unfold STOCK_NEG_INF
    omega
  have hq : StockBuyQueue dp_l queue_l_2 source_day ask_price (j-buy_cap) ((j-1)-1) head tail := by
    simpa only [show j-1-1=j-2 by omega] using PreH30
  have hp := StockBuyQueue_begin_popping__buy_pop_append dp_l queue_l_2 source_day ask_price (j-buy_cap) (j-1) head tail (by omega) (by omega) hn hq
  sep_apply (StockProofInternal.restore_cell dp_pre (days_pre+1) width source_day (j-1) dp_l __default__List_Z (by omega) (by omega))
  Exists queue_l_2 dp_l
  finish_entail

theorem proof_of_maximum_profit_entail_wit_32_1 : maximum_profit_entail_wit_32_1 := by
  unfold maximum_profit_entail_wit_32_1
  left
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 incoming_score last_index tail head buy_cap ask_price sell_cap bid_price source_day j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  have hlen := PreH34.1
  have hrow := PreH34.2 source_day (by omega)
  have he := Znth_indep dp_l_2 source_day __default__List_Z [] (by omega)
  have hscore : StockBuyScore dp_l_2 source_day ask_price (Znth (tail-1) queue_l_2 0) ≤ StockBuyScore dp_l_2 source_day ask_price (j-1) := by
    unfold StockBuyScore
    rw [← PreH30 (by omega), ← he]
    omega
  have hp := StockBuyQueuePopping_drop_tail__buy_pop_append dp_l_2 queue_l_2 source_day ask_price (j-buy_cap) (j-1) head tail PreH33 (by omega) hscore
  have hlast := PreH33.2.2.1 (tail-1-1) (by omega)
  rcases hlast with ⟨hl0,hll,hlv,hlr⟩
  sep_apply (StockProofInternal.restore_cell dp_pre (days_pre+1) width source_day last_index dp_l_2 __default__List_Z (by omega) (by omega))
  Exists queue_l_2 dp_l_2
  finish_entail

theorem proof_of_maximum_profit_entail_wit_32_2 : maximum_profit_entail_wit_32_2 := by
  unfold maximum_profit_entail_wit_32_2
  left
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 incoming_score last_index tail head buy_cap ask_price sell_cap bid_price source_day j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  have hlen := PreH34.1
  have hrow := PreH34.2 source_day (by omega)
  have he := Znth_indep dp_l_2 source_day __default__List_Z [] (by omega)
  have hscore : StockBuyScore dp_l_2 source_day ask_price (Znth (tail-1) queue_l_2 0) ≤ StockBuyScore dp_l_2 source_day ask_price (j-1) := by
    unfold StockBuyScore
    rw [← PreH30 (by omega), ← he]
    omega
  have hp := StockBuyQueuePopping_drop_tail__buy_pop_append dp_l_2 queue_l_2 source_day ask_price (j-buy_cap) (j-1) head tail PreH33 (by omega) hscore
  sep_apply (StockProofInternal.restore_cell dp_pre (days_pre+1) width source_day last_index dp_l_2 __default__List_Z (by omega) (by omega))
  Exists queue_l_2 dp_l_2
  finish_entail

theorem proof_of_maximum_profit_entail_wit_33_1 : maximum_profit_entail_wit_33_1 := by
  unfold maximum_profit_entail_wit_33_1
  left
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 incoming_score last_index tail head buy_cap ask_price sell_cap bid_price source_day j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  prop_apply (intArray.full_Zlength queue_index_pre width queue_l_2)
  Intros_p hqlen
  have hp : StockBuyQueuePending dp_l_2 queue_l_2 source_day ask_price (j-buy_cap) (j-1) head tail := by
    refine ⟨PreH31, by omega, ?_⟩
    intro hh
    omega
  Exists dp_l_2 queue_l_2
  finish_entail

theorem proof_of_maximum_profit_entail_wit_33_2 : maximum_profit_entail_wit_33_2 := by
  unfold maximum_profit_entail_wit_33_2
  left
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 incoming_score last_index tail head buy_cap ask_price sell_cap bid_price source_day j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  prop_apply (intArray.full_Zlength queue_index_pre width queue_l_2)
  Intros_p hqlen
  have hp : StockBuyQueuePending dp_l_2 queue_l_2 source_day ask_price (j-buy_cap) (j-1) head tail := by
    refine ⟨PreH32, by omega, ?_⟩
    intro hh
    have hlen := PreH33.1
    have he := Znth_indep dp_l_2 source_day __default__List_Z [] (by omega)
    unfold StockBuyScore
    rw [← PreH29 hh, ← he]
    omega
  sep_apply (StockProofInternal.restore_cell dp_pre (days_pre+1) width source_day last_index dp_l_2 __default__List_Z (by omega) (by omega))
  Exists dp_l_2 queue_l_2
  finish_entail

theorem proof_of_maximum_profit_entail_wit_34 : maximum_profit_entail_wit_34 := by
  unfold maximum_profit_entail_wit_34
  left
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width j bid_price i sell_cap ask_price buy_cap head tail source_day PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have hlen := PreH19.1
  have hi := PreH20.2.1
  have hsrc := PreH20.2.2.2.1
  have hdaily := PreH19.2.2.2.2.2.2 i (by omega)
  have hbuy := hdaily.2.2.1
  have hq := StockBuyQueuePending_append__buy_pop_append dp_l_2 queue_l_2 source_day ask_price (j-buy_cap) (j-1) head tail PreH21 (by omega)
  Exists (replace_Znth tail (j-1) queue_l_2) dp_l_2
  finish_entail

theorem proof_of_maximum_profit_entail_wit_35_2 : maximum_profit_entail_wit_35_2 := by
  unfold maximum_profit_entail_wit_35_2
  left
  intro dp_pre queue_index_pre sell_limit_pre buy_limit_pre bp_pre ap_pre wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day bid_price sell_cap ask_price buy_cap j head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have hlen := PreH30.1
  have hrow := PreH30.2 source_day (by omega)
  have he := Znth_indep dp_l_2 source_day __default__List_Z [] (by omega)
  have hn : Znth (j-1) (Znth source_day dp_l_2 []) 0 = STOCK_NEG_INF := by
    rw [he] at PreH1
    unfold STOCK_NEG_INF
    omega
  have hp := StockBuyQueue_extend_invalid__buy_cell_progress dp_l_2 queue_l_2 source_day ask_price (j-buy_cap) (j-1) head tail (by simpa only [show j-1-1=j-2 by omega] using PreH29) (by omega) hn
  sep_apply (StockProofInternal.restore_cell dp_pre (days_pre+1) width source_day (j-1) dp_l_2 __default__List_Z (by omega) (by omega))
  Exists queue_l_2 dp_l_2
  finish_entail

end SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_manual_part4
