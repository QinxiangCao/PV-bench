import SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_goal

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open coin_change_goal coin_change_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

theorem proof_of_coinChange_entail_wit_1 : coinChange_entail_wit_1 := by
  unfold coinChange_entail_wit_1
  left
  intro dp_pre amount_pre coinsSize_pre coins_pre coins_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  split_pure_spatial
  · sep_apply (intArray.seg_single dp_pre 0 (1 : Int))
    cancel
    exact naive_C_Rules.toContext.derivable1_refl _
  · split_pures
    all_goals dump_pre_spatial
    all_goals assumption

theorem proof_of_coinChange_entail_wit_2 : coinChange_entail_wit_2 := by
  unfold coinChange_entail_wit_2
  left
  intro dp_pre amount_pre coinsSize_pre coins_pre coins_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  have hp : DpPrefixZeroed [1] 1 := by
    refine ⟨by omega, by simp [Zlength], rfl, ?_⟩
    intro k hk; omega
  Exists ([1] : List Int)
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | omega | rfl | trivial

theorem proof_of_coinChange_entail_wit_3 : coinChange_entail_wit_3 := by
  unfold coinChange_entail_wit_3
  left
  intro dp_pre amount_pre coinsSize_pre coins_pre coins_l dp_l_2 j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  prop_apply (intArray.seg_Zlength dp_pre 0 (j + 1) (dp_l_2 ++ [0]))
  Intros_p hlen
  have hp := DpPrefixZeroed_snoc_zero dp_l_2 j (by omega) PreH9 (by simpa using hlen)
  Exists (dp_l_2 ++ [0])
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | omega | rfl | trivial

theorem proof_of_coinChange_entail_wit_4 : coinChange_entail_wit_4 := by
  unfold coinChange_entail_wit_4
  left
  intro dp_pre amount_pre coinsSize_pre coins_pre coins_l dp_l_2 j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hj : j = amount_pre + 1 := by omega
  subst j
  have hp := DpPrefixZeroed_to_DpReachableTable_nil dp_l_2 (amount_pre + 1) PreH9
  Exists dp_l_2
  split_pure_spatial
  · cancel
    exact (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp
      (intArray.undef_seg_empty dp_pre (amount_pre + 1))).1)
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | omega | rfl | trivial

theorem proof_of_coinChange_entail_wit_5 : coinChange_entail_wit_5 := by
  unfold coinChange_entail_wit_5
  left
  intro dp_pre amount_pre coinsSize_pre coins_pre coins_l dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have ht : DpReachableTable (sublist 0 0 coins_l) dp_l_2 (amount_pre + 1) := by
    simpa [sublist] using PreH7
  Exists dp_l_2
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | omega | rfl | trivial

theorem proof_of_coinChange_entail_wit_6 : coinChange_entail_wit_6 := by
  unfold coinChange_entail_wit_6
  left
  intro dp_pre amount_pre coinsSize_pre coins_pre coins_l dp_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hcoin := PreH10 i ⟨PreH7, PreH1⟩
  Exists dp_l_2
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | omega | rfl | trivial

theorem proof_of_coinChange_entail_wit_7 : coinChange_entail_wit_7 := by
  unfold coinChange_entail_wit_7
  left
  intro dp_pre amount_pre coinsSize_pre coins_pre coins_l dp_l_2 i coin PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hp : DpCoinInnerProgress (sublist 0 i coins_l) coin dp_l_2 coin amount_pre := by
    rcases PreH12 with ⟨hh, hlen, ht⟩
    refine ⟨by omega, by omega, by omega, hlen, ?_, ?_⟩
    · intro k hk
      exact (ht k (by omega)).trans (ReachableAmount_app_single_below _ coin k (by omega) hk).symm
    · intro k hk
      exact ht k (by omega)
  Exists dp_l_2
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | omega | rfl | trivial

theorem proof_of_coinChange_entail_wit_8_1 : coinChange_entail_wit_8_1 := by
  unfold coinChange_entail_wit_8_1
  left
  intro dp_pre amount_pre coinsSize_pre coins_pre coins_l dp_l_2 j coin i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have hp := DpCoinInnerProgress_replace_current _ coin dp_l_2 j amount_pre PreH1 PreH2 PreH15
  Exists (replace_Znth j 1 dp_l_2)
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | omega | rfl | trivial

theorem proof_of_coinChange_entail_wit_8_2 : coinChange_entail_wit_8_2 := by
  unfold coinChange_entail_wit_8_2
  left
  intro dp_pre amount_pre coinsSize_pre coins_pre coins_l dp_l_2 j coin i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have hp : DpCoinInnerProgress (sublist 0 i coins_l) coin dp_l_2 (j + 1) amount_pre := by
    rcases PreH15 with ⟨hc, hcj, hja, hlen, hb, ha⟩
    refine ⟨hc, by omega, by omega, hlen, ?_, ?_⟩
    · intro k hk
      by_cases he : k = j
      · subst k
        constructor
        · intro hz
          exact ReachableAmount_app_l _ [coin] j ((ha j (by omega)).mp hz)
        · intro hr
          rcases ReachableAmount_app_single_inv _ coin j hc hr with hr | ⟨_, hm⟩
          · exact (ha j (by omega)).mpr hr
          · exact False.elim (((hb (j - coin) (by omega)).mpr hm) PreH1)
      · exact hb k (by omega)
    · intro k hk
      exact ha k (by omega)
  Exists dp_l_2
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | omega | rfl | trivial

theorem proof_of_coinChange_entail_wit_9_1 : coinChange_entail_wit_9_1 := by
  unfold coinChange_entail_wit_9_1
  left
  intro dp_pre amount_pre coinsSize_pre coins_pre coins_l dp_l_2 j coin i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hj : j = amount_pre + 1 := by omega
  have hcoin : coin ≤ INT_MAX := by rw [PreH9]; exact (PreH15 i ⟨PreH7, PreH8⟩).2
  have ht : DpReachableTable (sublist 0 (i + 1) coins_l) dp_l_2 (amount_pre + 1) := by
    rw [sublist_0_succ_app 0 coins_l i (by omega), ← PreH9]
    rcases PreH14 with ⟨hc, hcj, hja, hlen, hb, ha⟩
    exact ⟨by omega, hlen, fun k hk => hb k (by omega)⟩
  Exists dp_l_2
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | omega | rfl | trivial

theorem proof_of_coinChange_entail_wit_9_2 : coinChange_entail_wit_9_2 := by
  unfold coinChange_entail_wit_9_2
  left
  intro dp_pre amount_pre coinsSize_pre coins_pre coins_l dp_l_2 i coin PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have ht : DpReachableTable (sublist 0 (i + 1) coins_l) dp_l_2 (amount_pre + 1) := by
    rw [sublist_0_succ_app 0 coins_l i (by omega), ← PreH9]
    rcases PreH12 with ⟨hh, hlen, ht⟩
    refine ⟨hh, hlen, ?_⟩
    intro k hk
    exact (ht k hk).trans (ReachableAmount_app_single_below _ coin k (by omega) (by omega)).symm
  Exists dp_l_2
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | omega | rfl | trivial

theorem proof_of_coinChange_entail_wit_10 : coinChange_entail_wit_10 := by
  unfold coinChange_entail_wit_10
  left
  intro dp_pre amount_pre coinsSize_pre coins_pre coins_l dp_l_2 i coin PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  Exists dp_l_2
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | omega | rfl | trivial

theorem proof_of_coinChange_entail_wit_11 : coinChange_entail_wit_11 := by
  unfold coinChange_entail_wit_11
  left
  intro dp_pre amount_pre coinsSize_pre coins_pre coins_l dp_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hi : i = coinsSize_pre := by omega
  have hs : sublist 0 i coins_l = coins_l := by
    apply sublist_self
    omega
  have ht : DpReachableTable coins_l dp_l_2 (amount_pre + 1) := by simpa only [hs] using PreH9
  have hn : NoReachableAbove coins_l amount_pre amount_pre := by
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    intro k hk hr; omega
  Exists dp_l_2
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | omega | rfl | trivial

theorem proof_of_coinChange_entail_wit_12 : coinChange_entail_wit_12 := by
  unfold coinChange_entail_wit_12
  left
  intro dp_pre amount_pre coinsSize_pre coins_pre coins_l dp_l_2 res PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hn : NoReachableAbove coins_l amount_pre (res - 1) := by
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    intro k hk hr
    by_cases he : k = res
    · subst k
      exact ((PreH10.2.2 res (by omega)).mpr hr) PreH1
    · exact PreH11.2 k (by omega) hr
  Exists dp_l_2
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | omega | rfl | trivial

theorem proof_of_coinChange_entail_wit_13_1 : coinChange_entail_wit_13_1 := by
  unfold coinChange_entail_wit_13_1
  left
  intro dp_pre amount_pre coinsSize_pre coins_pre coins_l dp_l_2 res PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have hr : res = 0 := by omega
  have hm : MaxReachableAmount coins_l amount_pre res :=
    MaxReachableAmount_intro_no_above _ _ _ (by rw [hr]; exact ReachableAmount_zero) (by omega) (by omega) PreH10
  Exists dp_l_2
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | omega | rfl | trivial

theorem proof_of_coinChange_entail_wit_13_2 : coinChange_entail_wit_13_2 := by
  unfold coinChange_entail_wit_13_2
  left
  intro dp_pre amount_pre coinsSize_pre coins_pre coins_l dp_l_2 res PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hm : MaxReachableAmount coins_l amount_pre res :=
    MaxReachableAmount_intro_no_above _ _ _ ((PreH10.2.2 res (by omega)).mp PreH1) (by omega) (by omega) PreH11
  Exists dp_l_2
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | omega | rfl | trivial

theorem proof_of_coinChange_entail_wit_10_split_goal_1 : coinChange_entail_wit_10_split_goal_1 := by
  unfold coinChange_entail_wit_10_split_goal_1
  intro amount n l dp i coin h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  exact h12

end SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_proof_manual
