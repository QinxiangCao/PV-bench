import Codeforces.examples_shard01.P081_432E_square_tiling.lean.groundtruth.P081_432E_square_tiling_goal
import Codeforces.examples_shard01.P081_432E_square_tiling.lean.groundtruth.P081_432E_square_tiling_proof_auto
import Codeforces.examples_shard01.P081_432E_square_tiling.lean.groundtruth.proof_lib

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace Codeforces.examples_shard01.P081_432E_square_tiling.lean.groundtruth.P081_432E_square_tiling_proof_manual

open Codeforces.examples_shard01.P081_432E_square_tiling.lean
open Codeforces.examples_shard01.P081_432E_square_tiling.lean.groundtruth.proof_lib
open Codeforces.examples_shard01.P081_432E_square_tiling.lean.groundtruth.P081_432E_square_tiling_goal
open scoped SimpleC

open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open Codeforces.examples_shard01.P081_432E_square_tiling.lean.groundtruth.P081_432E_square_tiling_goal SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
local infixl:70 " /ᶻ " => Z.div
local infixl:70 " mod " => Z.modulo

 theorem p081_signed_byte (flat : List Int) (index : Int) (hc : CanonicalGrid flat) (hi : 0≤index ∧ index<Zlength flat) :
    signed_last_nbits (Znth index flat 0) 8=Znth index flat 0 := by
  apply signed_last_nbits_eq _ 8 (by decide)
  change -128≤Znth index flat 0 ∧ Znth index flat 0<128
  rcases hc index hi with hz | hr <;> omega

theorem proof_of_conflicts_entail_wit_1_split_goal_1 : conflicts_entail_wit_1_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  intro h
  constructor <;> nlinarith

theorem proof_of_conflicts_entail_wit_1_split_goal_2 : conflicts_entail_wit_1_split_goal_2 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  intro h
  constructor <;> nlinarith

theorem proof_of_conflicts_entail_wit_1_split_goal_3 : conflicts_entail_wit_1_split_goal_3 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  intro h
  constructor <;> nlinarith

theorem proof_of_conflicts_entail_wit_1_split_goal_4 : conflicts_entail_wit_1_split_goal_4 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  intro h
  constructor <;> nlinarith

theorem proof_of_conflicts_entail_wit_1 : conflicts_entail_wit_1 := by
  unfold conflicts_entail_wit_1
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_entail_wit_1_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
    | exact proof_of_conflicts_entail_wit_1_split_goal_2 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
    | exact proof_of_conflicts_entail_wit_1_split_goal_3 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
    | exact proof_of_conflicts_entail_wit_1_split_goal_4 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14

theorem proof_of_conflicts_return_wit_1_split_goal_1 : conflicts_return_wit_1_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_1 : conflicts_return_wit_1 := by
  unfold conflicts_return_wit_1
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_1_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26

theorem proof_of_conflicts_return_wit_2_split_goal_1 : conflicts_return_wit_2_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have hbyte := p081_signed_byte flat (i_pre*m_pre+j_pre-1) PreH26 (by constructor <;> nlinarith)
  rw [hbyte] at PreH1
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_2 : conflicts_return_wit_2 := by
  unfold conflicts_return_wit_2
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_2_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26

theorem proof_of_conflicts_return_wit_3_split_goal_1 : conflicts_return_wit_3_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_3 : conflicts_return_wit_3 := by
  unfold conflicts_return_wit_3
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_3_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_conflicts_return_wit_4_split_goal_1 : conflicts_return_wit_4_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hbyte := p081_signed_byte flat (i_pre*m_pre+j_pre-1) PreH25 (by constructor <;> nlinarith)
  rw [hbyte] at PreH1
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_4 : conflicts_return_wit_4 := by
  unfold conflicts_return_wit_4
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_4_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_conflicts_return_wit_5_split_goal_1 : conflicts_return_wit_5_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_5 : conflicts_return_wit_5 := by
  unfold conflicts_return_wit_5
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_5_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_conflicts_return_wit_6_split_goal_1 : conflicts_return_wit_6_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have hbyte := p081_signed_byte flat (i_pre*m_pre+j_pre-1) PreH24 (by constructor <;> nlinarith)
  rw [hbyte] at PreH1
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_6 : conflicts_return_wit_6 := by
  unfold conflicts_return_wit_6
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_6_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_conflicts_return_wit_7_split_goal_1 : conflicts_return_wit_7_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_7 : conflicts_return_wit_7 := by
  unfold conflicts_return_wit_7
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_7_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_conflicts_return_wit_8_split_goal_1 : conflicts_return_wit_8_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hbyte := p081_signed_byte flat (i_pre*m_pre+j_pre-1) PreH25 (by constructor <;> nlinarith)
  rw [hbyte] at PreH1
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_8 : conflicts_return_wit_8 := by
  unfold conflicts_return_wit_8
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_8_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_conflicts_return_wit_9_split_goal_1 : conflicts_return_wit_9_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_9 : conflicts_return_wit_9 := by
  unfold conflicts_return_wit_9
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_9_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26

theorem proof_of_conflicts_return_wit_10_split_goal_1 : conflicts_return_wit_10_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have hbyte := p081_signed_byte flat (i_pre*m_pre+j_pre-1) PreH26 (by constructor <;> nlinarith)
  rw [hbyte] at PreH1
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_10 : conflicts_return_wit_10 := by
  unfold conflicts_return_wit_10
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_10_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26

theorem proof_of_conflicts_return_wit_11_split_goal_1 : conflicts_return_wit_11_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_11 : conflicts_return_wit_11 := by
  unfold conflicts_return_wit_11
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_11_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_conflicts_return_wit_12_split_goal_1 : conflicts_return_wit_12_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hbyte := p081_signed_byte flat (i_pre*m_pre+j_pre-1) PreH25 (by constructor <;> nlinarith)
  rw [hbyte] at PreH1
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_12 : conflicts_return_wit_12 := by
  unfold conflicts_return_wit_12
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_12_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_conflicts_return_wit_13_split_goal_1 : conflicts_return_wit_13_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_13 : conflicts_return_wit_13 := by
  unfold conflicts_return_wit_13
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_13_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26

theorem proof_of_conflicts_return_wit_14_split_goal_1 : conflicts_return_wit_14_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have hbyte := p081_signed_byte flat (i_pre*m_pre+j_pre-1) PreH26 (by constructor <;> nlinarith)
  rw [hbyte] at PreH1
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_14 : conflicts_return_wit_14 := by
  unfold conflicts_return_wit_14
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_14_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26

theorem proof_of_conflicts_return_wit_15_split_goal_1 : conflicts_return_wit_15_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_15 : conflicts_return_wit_15 := by
  unfold conflicts_return_wit_15
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_15_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27

theorem proof_of_conflicts_return_wit_16_split_goal_1 : conflicts_return_wit_16_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hbyte := p081_signed_byte flat (i_pre*m_pre+j_pre-1) PreH27 (by constructor <;> nlinarith)
  rw [hbyte] at PreH1
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_16 : conflicts_return_wit_16 := by
  unfold conflicts_return_wit_16
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_16_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27

theorem proof_of_conflicts_return_wit_17_split_goal_1 : conflicts_return_wit_17_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_17 : conflicts_return_wit_17 := by
  unfold conflicts_return_wit_17
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_17_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_conflicts_return_wit_18_split_goal_1 : conflicts_return_wit_18_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_18 : conflicts_return_wit_18 := by
  unfold conflicts_return_wit_18
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_18_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_conflicts_return_wit_19_split_goal_1 : conflicts_return_wit_19_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_19 : conflicts_return_wit_19 := by
  unfold conflicts_return_wit_19
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_19_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23

theorem proof_of_conflicts_return_wit_20_split_goal_1 : conflicts_return_wit_20_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_20 : conflicts_return_wit_20 := by
  unfold conflicts_return_wit_20
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_20_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_conflicts_return_wit_21_split_goal_1 : conflicts_return_wit_21_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_21 : conflicts_return_wit_21 := by
  unfold conflicts_return_wit_21
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_21_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_conflicts_return_wit_22_split_goal_1 : conflicts_return_wit_22_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_22 : conflicts_return_wit_22 := by
  unfold conflicts_return_wit_22
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_22_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_conflicts_return_wit_23_split_goal_1 : conflicts_return_wit_23_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_23 : conflicts_return_wit_23 := by
  unfold conflicts_return_wit_23
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_23_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_conflicts_return_wit_24_split_goal_1 : conflicts_return_wit_24_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_24 : conflicts_return_wit_24 := by
  unfold conflicts_return_wit_24
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_24_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26

theorem proof_of_conflicts_return_wit_25_split_goal_1 : conflicts_return_wit_25_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega,rfl⟩)))

theorem proof_of_conflicts_return_wit_25 : conflicts_return_wit_25 := by
  unfold conflicts_return_wit_25
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_25_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_conflicts_return_wit_26_split_goal_1 : conflicts_return_wit_26_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega,rfl⟩)))

theorem proof_of_conflicts_return_wit_26 : conflicts_return_wit_26 := by
  unfold conflicts_return_wit_26
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_26_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_conflicts_return_wit_27_split_goal_1 : conflicts_return_wit_27_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega,rfl⟩)))

theorem proof_of_conflicts_return_wit_27 : conflicts_return_wit_27 := by
  unfold conflicts_return_wit_27
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_27_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23

theorem proof_of_conflicts_return_wit_28_split_goal_1 : conflicts_return_wit_28_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega,rfl⟩)))

theorem proof_of_conflicts_return_wit_28 : conflicts_return_wit_28 := by
  unfold conflicts_return_wit_28
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_28_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_conflicts_return_wit_29_split_goal_1 : conflicts_return_wit_29_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega,rfl⟩)))

theorem proof_of_conflicts_return_wit_29 : conflicts_return_wit_29 := by
  unfold conflicts_return_wit_29
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_29_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_conflicts_return_wit_30_split_goal_1 : conflicts_return_wit_30_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega,rfl⟩)))

theorem proof_of_conflicts_return_wit_30 : conflicts_return_wit_30 := by
  unfold conflicts_return_wit_30
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_30_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_conflicts_return_wit_31_split_goal_1 : conflicts_return_wit_31_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega,rfl⟩)))

theorem proof_of_conflicts_return_wit_31 : conflicts_return_wit_31 := by
  unfold conflicts_return_wit_31
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_31_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_conflicts_return_wit_32_split_goal_1 : conflicts_return_wit_32_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega,rfl⟩)))

theorem proof_of_conflicts_return_wit_32 : conflicts_return_wit_32 := by
  unfold conflicts_return_wit_32
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_32_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26

theorem proof_of_conflicts_return_wit_33_split_goal_1 : conflicts_return_wit_33_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_33 : conflicts_return_wit_33 := by
  unfold conflicts_return_wit_33
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_33_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26

theorem proof_of_conflicts_return_wit_34_split_goal_1 : conflicts_return_wit_34_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have hbyte := p081_signed_byte flat (i_pre*m_pre+j_pre-1) PreH26 (by constructor <;> nlinarith)
  rw [hbyte] at PreH1
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_34 : conflicts_return_wit_34 := by
  unfold conflicts_return_wit_34
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_34_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26

theorem proof_of_conflicts_return_wit_35_split_goal_1 : conflicts_return_wit_35_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_35 : conflicts_return_wit_35 := by
  unfold conflicts_return_wit_35
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_35_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_conflicts_return_wit_36_split_goal_1 : conflicts_return_wit_36_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hbyte := p081_signed_byte flat (i_pre*m_pre+j_pre-1) PreH25 (by constructor <;> nlinarith)
  rw [hbyte] at PreH1
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_36 : conflicts_return_wit_36 := by
  unfold conflicts_return_wit_36
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_36_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_conflicts_return_wit_37_split_goal_1 : conflicts_return_wit_37_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_37 : conflicts_return_wit_37 := by
  unfold conflicts_return_wit_37
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_37_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_conflicts_return_wit_38_split_goal_1 : conflicts_return_wit_38_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have hbyte := p081_signed_byte flat (i_pre*m_pre+j_pre-1) PreH24 (by constructor <;> nlinarith)
  rw [hbyte] at PreH1
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_38 : conflicts_return_wit_38 := by
  unfold conflicts_return_wit_38
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_38_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_conflicts_return_wit_39_split_goal_1 : conflicts_return_wit_39_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_39 : conflicts_return_wit_39 := by
  unfold conflicts_return_wit_39
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_39_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_conflicts_return_wit_40_split_goal_1 : conflicts_return_wit_40_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hbyte := p081_signed_byte flat (i_pre*m_pre+j_pre-1) PreH25 (by constructor <;> nlinarith)
  rw [hbyte] at PreH1
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_40 : conflicts_return_wit_40 := by
  unfold conflicts_return_wit_40
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_40_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_conflicts_return_wit_41_split_goal_1 : conflicts_return_wit_41_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_41 : conflicts_return_wit_41 := by
  unfold conflicts_return_wit_41
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_41_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26

theorem proof_of_conflicts_return_wit_42_split_goal_1 : conflicts_return_wit_42_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have hbyte := p081_signed_byte flat (i_pre*m_pre+j_pre-1) PreH26 (by constructor <;> nlinarith)
  rw [hbyte] at PreH1
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_42 : conflicts_return_wit_42 := by
  unfold conflicts_return_wit_42
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_42_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26

theorem proof_of_conflicts_return_wit_43_split_goal_1 : conflicts_return_wit_43_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_43 : conflicts_return_wit_43 := by
  unfold conflicts_return_wit_43
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_43_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_conflicts_return_wit_44_split_goal_1 : conflicts_return_wit_44_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hbyte := p081_signed_byte flat (i_pre*m_pre+j_pre-1) PreH25 (by constructor <;> nlinarith)
  rw [hbyte] at PreH1
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_44 : conflicts_return_wit_44 := by
  unfold conflicts_return_wit_44
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_44_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_conflicts_return_wit_45_split_goal_1 : conflicts_return_wit_45_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_45 : conflicts_return_wit_45 := by
  unfold conflicts_return_wit_45
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_45_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26

theorem proof_of_conflicts_return_wit_46_split_goal_1 : conflicts_return_wit_46_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have hbyte := p081_signed_byte flat (i_pre*m_pre+j_pre-1) PreH26 (by constructor <;> nlinarith)
  rw [hbyte] at PreH1
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_46 : conflicts_return_wit_46 := by
  unfold conflicts_return_wit_46
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_46_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26

theorem proof_of_conflicts_return_wit_47_split_goal_1 : conflicts_return_wit_47_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_47 : conflicts_return_wit_47 := by
  unfold conflicts_return_wit_47
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_47_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27

theorem proof_of_conflicts_return_wit_48_split_goal_1 : conflicts_return_wit_48_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hbyte := p081_signed_byte flat (i_pre*m_pre+j_pre-1) PreH27 (by constructor <;> nlinarith)
  rw [hbyte] at PreH1
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_48 : conflicts_return_wit_48 := by
  unfold conflicts_return_wit_48
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_48_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27

theorem proof_of_conflicts_return_wit_49_split_goal_1 : conflicts_return_wit_49_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_49 : conflicts_return_wit_49 := by
  unfold conflicts_return_wit_49
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_49_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23

theorem proof_of_conflicts_return_wit_50_split_goal_1 : conflicts_return_wit_50_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_50 : conflicts_return_wit_50 := by
  unfold conflicts_return_wit_50
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_50_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22

theorem proof_of_conflicts_return_wit_51_split_goal_1 : conflicts_return_wit_51_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_51 : conflicts_return_wit_51 := by
  unfold conflicts_return_wit_51
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_51_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23

theorem proof_of_conflicts_return_wit_52_split_goal_1 : conflicts_return_wit_52_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_52 : conflicts_return_wit_52 := by
  unfold conflicts_return_wit_52
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_52_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_conflicts_return_wit_53_split_goal_1 : conflicts_return_wit_53_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_53 : conflicts_return_wit_53 := by
  unfold conflicts_return_wit_53
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_53_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21

theorem proof_of_conflicts_return_wit_54_split_goal_1 : conflicts_return_wit_54_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_54 : conflicts_return_wit_54 := by
  unfold conflicts_return_wit_54
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_54_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22

theorem proof_of_conflicts_return_wit_55_split_goal_1 : conflicts_return_wit_55_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_55 : conflicts_return_wit_55 := by
  unfold conflicts_return_wit_55
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_55_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20

open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open Codeforces.examples_shard01.P081_432E_square_tiling.lean.groundtruth.P081_432E_square_tiling_goal SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩


theorem proof_of_cell_colour_entail_wit_1_split_goal_1 : cell_colour_entail_wit_1_split_goal_1 := by
  intro left_override_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  intro color hc
  omega

theorem proof_of_cell_colour_entail_wit_1 : cell_colour_entail_wit_1 := by
  unfold cell_colour_entail_wit_1
  right
  intro left_override_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_cell_colour_entail_wit_1_split_goal_1 left_override_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_cell_colour_entail_wit_2_split_goal_1 : cell_colour_entail_wit_2_split_goal_1 := by
  intro left_override_pre j_pre i_pre m_pre n_pre flat c retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  intro color hc
  by_cases hlt : color<c
  · exact PreH20 color (by omega)
  · have he : color=c := by omega
    simpa only [he] using PreH3

theorem proof_of_cell_colour_entail_wit_2 : cell_colour_entail_wit_2 := by
  unfold cell_colour_entail_wit_2
  right
  intro left_override_pre j_pre i_pre m_pre n_pre flat c retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_cell_colour_entail_wit_2_split_goal_1 left_override_pre j_pre i_pre m_pre n_pre flat c retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20

theorem proof_of_cell_colour_return_wit_1_split_goal_1 : cell_colour_return_wit_1_split_goal_1 := by
  intro left_override_pre j_pre i_pre m_pre n_pre flat c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  obtain ⟨color,hc,hfree⟩ := neighbor_conflict_five_colour_choice__colour_selection flat n_pre m_pre i_pre j_pre left_override_pre
  exact False.elim (hfree (PreH16 color (by omega)))

theorem proof_of_cell_colour_return_wit_1 : cell_colour_return_wit_1 := by
  unfold cell_colour_return_wit_1
  right
  intro left_override_pre j_pre i_pre m_pre n_pre flat c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_cell_colour_return_wit_1_split_goal_1 left_override_pre j_pre i_pre m_pre n_pre flat c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16

theorem proof_of_cell_colour_return_wit_2_split_goal_1 : cell_colour_return_wit_2_split_goal_1 := by
  intro left_override_pre j_pre i_pre m_pre n_pre flat c retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  refine ⟨⟨by omega,PreH3⟩,?_⟩
  intro color hc hlegal
  exact hlegal.2 (PreH20 color hc)

theorem proof_of_cell_colour_return_wit_2 : cell_colour_return_wit_2 := by
  unfold cell_colour_return_wit_2
  right
  intro left_override_pre j_pre i_pre m_pre n_pre flat c retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_cell_colour_return_wit_2_split_goal_1 left_override_pre j_pre i_pre m_pre n_pre flat c retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20

theorem proof_of_can_place_entail_wit_1_split_goal_1 : can_place_entail_wit_1_split_goal_1 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  intro off hoff
  nlinarith

theorem proof_of_can_place_entail_wit_1 : can_place_entail_wit_1 := by
  unfold can_place_entail_wit_1
  right
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_can_place_entail_wit_1_split_goal_1 c_pre s_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16

theorem proof_of_can_place_entail_wit_2_split_goal_1 : can_place_entail_wit_2_split_goal_1 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  intro off hoff
  exact PreH20 off (by constructor <;> nlinarith)

theorem proof_of_can_place_entail_wit_2_split_goal_2 : can_place_entail_wit_2_split_goal_2 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  intro h
  constructor <;> nlinarith

theorem proof_of_can_place_entail_wit_2 : can_place_entail_wit_2 := by
  unfold can_place_entail_wit_2
  right
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_can_place_entail_wit_2_split_goal_1 c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
    | exact proof_of_can_place_entail_wit_2_split_goal_2 c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20

theorem proof_of_can_place_entail_wit_3_split_goal_1 : can_place_entail_wit_3_split_goal_1 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat q r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  intro off hoff
  exact PreH23 off (by constructor <;> nlinarith)

theorem proof_of_can_place_entail_wit_3 : can_place_entail_wit_3 := by
  unfold can_place_entail_wit_3
  right
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat q r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_can_place_entail_wit_3_split_goal_1 c_pre s_pre j_pre i_pre m_pre n_pre flat q r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23

theorem proof_of_can_place_entail_wit_4_split_goal_1 : can_place_entail_wit_4_split_goal_1 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat q r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  intro off hoff
  by_cases hlt : off<(r-i_pre)*s_pre+(q-j_pre)
  · exact PreH23 off (by omega)
  · have he : off=(r-i_pre)*s_pre+(q-j_pre) := by omega
    obtain ⟨hd,hm⟩ := p081_div_mod_pair (r-i_pre) (q-j_pre) s_pre (by omega)
    change Znth ((i_pre+off /ᶻ s_pre)*m_pre+(j_pre+off mod s_pre)) flat 0=0
    rw [he,hd,hm]
    convert PreH24 using 1 <;> congr 1 <;> ring

theorem proof_of_can_place_entail_wit_4_split_goal_2 : can_place_entail_wit_4_split_goal_2 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat q r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  intro h
  constructor <;> nlinarith

theorem proof_of_can_place_entail_wit_4 : can_place_entail_wit_4 := by
  unfold can_place_entail_wit_4
  right
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat q r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_can_place_entail_wit_4_split_goal_1 c_pre s_pre j_pre i_pre m_pre n_pre flat q r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
    | exact proof_of_can_place_entail_wit_4_split_goal_2 c_pre s_pre j_pre i_pre m_pre n_pre flat q r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_can_place_entail_wit_5_split_goal_1 : can_place_entail_wit_5_split_goal_1 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  intro off hoff
  nlinarith

theorem proof_of_can_place_entail_wit_5_split_goal_2 : can_place_entail_wit_5_split_goal_2 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  intro off hoff
  exact PreH20 off (by constructor <;> nlinarith)

theorem proof_of_can_place_entail_wit_5_split_goal_3 : can_place_entail_wit_5_split_goal_3 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  intro h
  constructor <;> nlinarith

theorem proof_of_can_place_entail_wit_5_split_goal_4 : can_place_entail_wit_5_split_goal_4 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  intro h
  constructor <;> nlinarith

theorem proof_of_can_place_entail_wit_5 : can_place_entail_wit_5 := by
  unfold can_place_entail_wit_5
  right
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_can_place_entail_wit_5_split_goal_1 c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
    | exact proof_of_can_place_entail_wit_5_split_goal_2 c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
    | exact proof_of_can_place_entail_wit_5_split_goal_3 c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
    | exact proof_of_can_place_entail_wit_5_split_goal_4 c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20

theorem proof_of_can_place_entail_wit_6_1_split_goal_1 : can_place_entail_wit_6_1_split_goal_1 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  intro off hoff
  by_cases hlt : off<q-j_pre
  · exact PreH26 off (by omega)
  · have he : off=q-j_pre := by omega
    subst off
    unfold HorizontalBoundaryClearPrefix at *
    simp only [show j_pre+(q-j_pre)=q by omega]
    constructor <;> intro hb <;> omega

theorem proof_of_can_place_entail_wit_6_1_split_goal_2 : can_place_entail_wit_6_1_split_goal_2 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  intro h
  constructor <;> nlinarith

theorem proof_of_can_place_entail_wit_6_1 : can_place_entail_wit_6_1 := by
  unfold can_place_entail_wit_6_1
  right
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_can_place_entail_wit_6_1_split_goal_1 c_pre s_pre j_pre i_pre m_pre n_pre flat q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
    | exact proof_of_can_place_entail_wit_6_1_split_goal_2 c_pre s_pre j_pre i_pre m_pre n_pre flat q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26

theorem proof_of_can_place_entail_wit_6_2_split_goal_1 : can_place_entail_wit_6_2_split_goal_1 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  intro off hoff
  by_cases hlt : off<q-j_pre
  · exact PreH25 off (by omega)
  · have he : off=q-j_pre := by omega
    subst off
    unfold HorizontalBoundaryClearPrefix at *
    simp only [show j_pre+(q-j_pre)=q by omega]
    constructor <;> intro hb <;> omega

theorem proof_of_can_place_entail_wit_6_2 : can_place_entail_wit_6_2 := by
  unfold can_place_entail_wit_6_2
  right
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_can_place_entail_wit_6_2_split_goal_1 c_pre s_pre j_pre i_pre m_pre n_pre flat q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_can_place_entail_wit_6_3_split_goal_1 : can_place_entail_wit_6_3_split_goal_1 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  intro off hoff
  by_cases hlt : off<q-j_pre
  · exact PreH26 off (by omega)
  · have he : off=q-j_pre := by omega
    subst off
    unfold HorizontalBoundaryClearPrefix at *
    simp only [show j_pre+(q-j_pre)=q by omega]
    constructor <;> intro hb <;> omega

theorem proof_of_can_place_entail_wit_6_3_split_goal_2 : can_place_entail_wit_6_3_split_goal_2 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  intro h
  constructor <;> nlinarith

theorem proof_of_can_place_entail_wit_6_3 : can_place_entail_wit_6_3 := by
  unfold can_place_entail_wit_6_3
  right
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_can_place_entail_wit_6_3_split_goal_1 c_pre s_pre j_pre i_pre m_pre n_pre flat q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
    | exact proof_of_can_place_entail_wit_6_3_split_goal_2 c_pre s_pre j_pre i_pre m_pre n_pre flat q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26

theorem proof_of_can_place_entail_wit_6_4_split_goal_1 : can_place_entail_wit_6_4_split_goal_1 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  intro off hoff
  by_cases hlt : off<q-j_pre
  · exact PreH27 off (by omega)
  · have he : off=q-j_pre := by omega
    subst off
    unfold HorizontalBoundaryClearPrefix at *
    simp only [show j_pre+(q-j_pre)=q by omega]
    constructor <;> intro hb <;> omega

theorem proof_of_can_place_entail_wit_6_4_split_goal_2 : can_place_entail_wit_6_4_split_goal_2 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  intro h
  constructor <;> nlinarith

theorem proof_of_can_place_entail_wit_6_4_split_goal_3 : can_place_entail_wit_6_4_split_goal_3 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  intro h
  constructor <;> nlinarith

theorem proof_of_can_place_entail_wit_6_4 : can_place_entail_wit_6_4 := by
  unfold can_place_entail_wit_6_4
  right
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_can_place_entail_wit_6_4_split_goal_1 c_pre s_pre j_pre i_pre m_pre n_pre flat q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
    | exact proof_of_can_place_entail_wit_6_4_split_goal_2 c_pre s_pre j_pre i_pre m_pre n_pre flat q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
    | exact proof_of_can_place_entail_wit_6_4_split_goal_3 c_pre s_pre j_pre i_pre m_pre n_pre flat q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27

theorem proof_of_can_place_entail_wit_7_split_goal_1 : can_place_entail_wit_7_split_goal_1 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  intro off hoff
  nlinarith

theorem proof_of_can_place_entail_wit_7_split_goal_2 : can_place_entail_wit_7_split_goal_2 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  intro off hoff
  exact PreH23 off (by constructor <;> nlinarith)

theorem proof_of_can_place_entail_wit_7_split_goal_3 : can_place_entail_wit_7_split_goal_3 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  intro h
  constructor <;> nlinarith

theorem proof_of_can_place_entail_wit_7_split_goal_4 : can_place_entail_wit_7_split_goal_4 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  intro h
  constructor <;> nlinarith

theorem proof_of_can_place_entail_wit_7 : can_place_entail_wit_7 := by
  unfold can_place_entail_wit_7
  right
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_can_place_entail_wit_7_split_goal_1 c_pre s_pre j_pre i_pre m_pre n_pre flat q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
    | exact proof_of_can_place_entail_wit_7_split_goal_2 c_pre s_pre j_pre i_pre m_pre n_pre flat q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
    | exact proof_of_can_place_entail_wit_7_split_goal_3 c_pre s_pre j_pre i_pre m_pre n_pre flat q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
    | exact proof_of_can_place_entail_wit_7_split_goal_4 c_pre s_pre j_pre i_pre m_pre n_pre flat q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23

theorem proof_of_can_place_entail_wit_8_1_split_goal_1 : can_place_entail_wit_8_1_split_goal_1 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  intro off hoff
  by_cases hlt : off<r-i_pre
  · exact PreH27 off (by omega)
  · have he : off=r-i_pre := by omega
    subst off
    unfold VerticalBoundaryClearPrefix at *
    simp only [show i_pre+(r-i_pre)=r by omega]
    constructor <;> intro hb <;> omega

theorem proof_of_can_place_entail_wit_8_1_split_goal_2 : can_place_entail_wit_8_1_split_goal_2 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  intro h
  constructor <;> nlinarith

theorem proof_of_can_place_entail_wit_8_1 : can_place_entail_wit_8_1 := by
  unfold can_place_entail_wit_8_1
  right
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_can_place_entail_wit_8_1_split_goal_1 c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
    | exact proof_of_can_place_entail_wit_8_1_split_goal_2 c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27

theorem proof_of_can_place_entail_wit_8_2_split_goal_1 : can_place_entail_wit_8_2_split_goal_1 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  intro off hoff
  by_cases hlt : off<r-i_pre
  · exact PreH26 off (by omega)
  · have he : off=r-i_pre := by omega
    subst off
    unfold VerticalBoundaryClearPrefix at *
    simp only [show i_pre+(r-i_pre)=r by omega]
    constructor <;> intro hb <;> omega

theorem proof_of_can_place_entail_wit_8_2 : can_place_entail_wit_8_2 := by
  unfold can_place_entail_wit_8_2
  right
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_can_place_entail_wit_8_2_split_goal_1 c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26

theorem proof_of_can_place_entail_wit_8_3_split_goal_1 : can_place_entail_wit_8_3_split_goal_1 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  intro off hoff
  by_cases hlt : off<r-i_pre
  · exact PreH27 off (by omega)
  · have he : off=r-i_pre := by omega
    subst off
    unfold VerticalBoundaryClearPrefix at *
    simp only [show i_pre+(r-i_pre)=r by omega]
    constructor <;> intro hb <;> omega

theorem proof_of_can_place_entail_wit_8_3_split_goal_2 : can_place_entail_wit_8_3_split_goal_2 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  intro h
  constructor <;> nlinarith

theorem proof_of_can_place_entail_wit_8_3 : can_place_entail_wit_8_3 := by
  unfold can_place_entail_wit_8_3
  right
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_can_place_entail_wit_8_3_split_goal_1 c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
    | exact proof_of_can_place_entail_wit_8_3_split_goal_2 c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27

theorem proof_of_can_place_entail_wit_8_4_split_goal_1 : can_place_entail_wit_8_4_split_goal_1 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  intro off hoff
  by_cases hlt : off<r-i_pre
  · exact PreH28 off (by omega)
  · have he : off=r-i_pre := by omega
    subst off
    unfold VerticalBoundaryClearPrefix at *
    simp only [show i_pre+(r-i_pre)=r by omega]
    constructor <;> intro hb <;> omega

theorem proof_of_can_place_entail_wit_8_4_split_goal_2 : can_place_entail_wit_8_4_split_goal_2 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  intro h
  constructor <;> nlinarith

theorem proof_of_can_place_entail_wit_8_4_split_goal_3 : can_place_entail_wit_8_4_split_goal_3 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  intro h
  constructor <;> nlinarith

theorem proof_of_can_place_entail_wit_8_4 : can_place_entail_wit_8_4 := by
  unfold can_place_entail_wit_8_4
  right
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_can_place_entail_wit_8_4_split_goal_1 c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
    | exact proof_of_can_place_entail_wit_8_4_split_goal_2 c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
    | exact proof_of_can_place_entail_wit_8_4_split_goal_3 c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28

theorem proof_of_can_place_return_wit_1_split_goal_1 : can_place_return_wit_1_split_goal_1 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  refine ⟨PreH10,PreH14,PreH15,?_,?_,?_⟩
  · intro row col hr hc
    have hoff : 0≤(row-i_pre)*s_pre+(col-j_pre) ∧ (row-i_pre)*s_pre+(col-j_pre)<s_pre*s_pre := by constructor <;> nlinarith
    have h := PreH22 ((row-i_pre)*s_pre+(col-j_pre)) hoff
    obtain ⟨hd,hm⟩ := p081_div_mod_pair (row-i_pre) (col-j_pre) s_pre (by omega)
    change Znth ((i_pre+((row-i_pre)*s_pre+(col-j_pre)) /ᶻ s_pre)*m_pre+(j_pre+((row-i_pre)*s_pre+(col-j_pre)) mod s_pre)) flat 0=0 at h
    rw [hd,hm] at h
    convert h using 1 <;> congr 1 <;> ring
  · intro col hc
    have h := PreH23 (col-j_pre) (by omega)
    simpa only [show j_pre+(col-j_pre)=col by omega] using h
  · intro row hr
    have h := PreH24 (row-i_pre) (by omega)
    simpa only [show i_pre+(row-i_pre)=row by omega] using h

theorem proof_of_can_place_return_wit_1 : can_place_return_wit_1 := by
  unfold can_place_return_wit_1
  right
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_can_place_return_wit_1_split_goal_1 c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_can_place_return_wit_2_split_goal_1 : can_place_return_wit_2_split_goal_1 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  intro h
  exact ((h.2.2.2.2.2 r (by omega)).2 (by omega)) PreH1

theorem proof_of_can_place_return_wit_2 : can_place_return_wit_2 := by
  unfold can_place_return_wit_2
  right
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_can_place_return_wit_2_split_goal_1 c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27

theorem proof_of_can_place_return_wit_3_split_goal_1 : can_place_return_wit_3_split_goal_1 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  intro h
  exact ((h.2.2.2.2.2 r (by omega)).2 (by omega)) PreH1

theorem proof_of_can_place_return_wit_3 : can_place_return_wit_3 := by
  unfold can_place_return_wit_3
  right
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_can_place_return_wit_3_split_goal_1 c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28

theorem proof_of_can_place_return_wit_4_split_goal_1 : can_place_return_wit_4_split_goal_1 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  intro h
  exact ((h.2.2.2.2.2 r (by omega)).1 (by omega)) PreH1

theorem proof_of_can_place_return_wit_4 : can_place_return_wit_4 := by
  unfold can_place_return_wit_4
  right
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_can_place_return_wit_4_split_goal_1 c_pre s_pre j_pre i_pre m_pre n_pre flat r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26

theorem proof_of_can_place_return_wit_5_split_goal_1 : can_place_return_wit_5_split_goal_1 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  intro h
  exact ((h.2.2.2.2.1 q (by omega)).2 (by omega)) PreH1

theorem proof_of_can_place_return_wit_5 : can_place_return_wit_5 := by
  unfold can_place_return_wit_5
  right
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_can_place_return_wit_5_split_goal_1 c_pre s_pre j_pre i_pre m_pre n_pre flat q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26

theorem proof_of_can_place_return_wit_6_split_goal_1 : can_place_return_wit_6_split_goal_1 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  intro h
  exact ((h.2.2.2.2.1 q (by omega)).2 (by omega)) PreH1

theorem proof_of_can_place_return_wit_6 : can_place_return_wit_6 := by
  unfold can_place_return_wit_6
  right
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_can_place_return_wit_6_split_goal_1 c_pre s_pre j_pre i_pre m_pre n_pre flat q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27

theorem proof_of_can_place_return_wit_7_split_goal_1 : can_place_return_wit_7_split_goal_1 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  intro h
  exact ((h.2.2.2.2.1 q (by omega)).1 (by omega)) PreH1

theorem proof_of_can_place_return_wit_7 : can_place_return_wit_7 := by
  unfold can_place_return_wit_7
  right
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_can_place_return_wit_7_split_goal_1 c_pre s_pre j_pre i_pre m_pre n_pre flat q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_can_place_return_wit_8_split_goal_1 : can_place_return_wit_8_split_goal_1 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat q r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  intro h
  exact PreH24 (h.2.2.2.1 r q (by omega) (by omega))

theorem proof_of_can_place_return_wit_8 : can_place_return_wit_8 := by
  unfold can_place_return_wit_8
  right
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat q r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_can_place_return_wit_8_split_goal_1 c_pre s_pre j_pre i_pre m_pre n_pre flat q r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_can_place_return_wit_9_split_goal_1 : can_place_return_wit_9_split_goal_1 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  intro h
  have hb := h.2.1
  omega

theorem proof_of_can_place_return_wit_9 : can_place_return_wit_9 := by
  unfold can_place_return_wit_9
  right
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_can_place_return_wit_9_split_goal_1 c_pre s_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15

theorem proof_of_can_place_return_wit_10_split_goal_1 : can_place_return_wit_10_split_goal_1 := by
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  intro h
  have hb := h.2.2.1
  omega

theorem proof_of_can_place_return_wit_10 : can_place_return_wit_10 := by
  unfold can_place_return_wit_10
  right
  intro c_pre s_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_can_place_return_wit_10_split_goal_1 c_pre s_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16

open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open Codeforces.examples_shard01.P081_432E_square_tiling.lean.groundtruth.P081_432E_square_tiling_goal SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩


private noncomputable abbrev charArray := naive_C_Rules.CharArray

private theorem greedyPlacementTrace_to_qcp {n m next : Int} {flat : List Int} :
    Codeforces.examples_shard01.P081_432E_square_tiling.lean.GreedyPlacementTrace n m next flat →
      SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib.GreedyPlacementTrace n m next flat := by
  intro h
  induction h with
  | GreedyTrace_zero flat hlen hzero =>
      apply SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib.GreedyPlacementTrace.GreedyTrace_zero
      · exact hlen
      · simpa only [Codeforces.examples_shard01.P081_432E_square_tiling.lean.ZeroPrefix,
          SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib.ZeroPrefix] using hzero
  | GreedyTrace_skip next flat htrace hbounds hcell ih =>
      exact SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib.GreedyPlacementTrace.GreedyTrace_skip
        next flat ih hbounds hcell
  | GreedyTrace_place next before after i j color side htrace hnext hi hj hzero hsettled hpaint ih =>
      apply SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib.GreedyPlacementTrace.GreedyTrace_place
        next before after i j color side ih hnext hi hj hzero
      · simpa only [Codeforces.examples_shard01.P081_432E_square_tiling.lean.SettledSquareState,
          SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib.SettledSquareState,
          Codeforces.examples_shard01.P081_432E_square_tiling.lean.ChosenSquareState,
          SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib.ChosenSquareState,
          Codeforces.examples_shard01.P081_432E_square_tiling.lean.LeastLegalColor,
          SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib.LeastLegalColor,
          Codeforces.examples_shard01.P081_432E_square_tiling.lean.LegalColor,
          SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib.LegalColor,
          Codeforces.examples_shard01.P081_432E_square_tiling.lean.NeighborConflict,
          SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib.NeighborConflict,
          Codeforces.examples_shard01.P081_432E_square_tiling.lean.GreedySideState,
          SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib.GreedySideState,
          Codeforces.examples_shard01.P081_432E_square_tiling.lean.NoPlaceableColorBelow,
          SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib.NoPlaceableColorBelow,
          Codeforces.examples_shard01.P081_432E_square_tiling.lean.CanPlace,
          SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib.CanPlace] using hsettled
      · simpa only [Codeforces.examples_shard01.P081_432E_square_tiling.lean.PaintRectanglePrefix,
          SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib.PaintRectanglePrefix] using hpaint

private theorem shape_rec (storeA : Int → Int → Int → SacContext.rules.expr)
    (k : Nat) (x lo hi : Int) :
    store_undef_array_rec SacContext.rules (fun x lo => EX a : Int, storeA x lo a) x lo hi k |--
      EX l : List Int, store_array_rec SacContext.rules storeA x lo hi l := by
  induction k generalizing lo with
  | zero =>
    simp only [store_undef_array_rec]
    Intros_p he
    Exists ([] : List Int)
    simp only [store_array_rec]
    split_pure_spatial
    · cancel
    · split_pures <;> dump_pre_spatial
      all_goals solve | assumption | rfl | trivial
  | succ k ih =>
    simp only [store_undef_array_rec]
    Intros a
    sep_apply (ih (lo+1))
    Intros l
    Exists (a::l)
    simp only [store_array_rec]
    cancel

private theorem shape_full (x n : Int) :
    charArray.full_shape x n |-- EX l : List Int, charArray.full x n l := by
  apply shape_rec

theorem proof_of_solver_safety_wit_18_split_goal_1 : solver_safety_wit_18_split_goal_1 := by
  intro g_pre m_pre n_pre available grid c t j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  dump_pre_spatial
  exact False.elim (PreH17 available (by omega) PreH20)

theorem proof_of_solver_safety_wit_18 : solver_safety_wit_18 := by
  unfold solver_safety_wit_18
  right
  intro g_pre m_pre n_pre available grid c t j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  exact proof_of_solver_safety_wit_18_split_goal_1 g_pre m_pre n_pre available grid c t j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  unfold solver_entail_wit_1
  right
  intro g_pre m_pre n_pre PreH1 PreH2 PreH3 PreH4
  sep_apply (shape_full g_pre (n_pre*m_pre))
  Intros flat
  prop_apply (charArray.full_Zlength g_pre (n_pre*m_pre) flat)
  Intros_p hlen
  Exists flat
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | (intro k hk; omega)

theorem proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1 := by
  intro m_pre n_pre flat_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  simpa only [add_zero] using PreH9

theorem proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2 := by
  intro m_pre n_pre flat_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  intro h
  constructor <;> nlinarith

theorem proof_of_solver_entail_wit_2 : solver_entail_wit_2 := by
  unfold solver_entail_wit_2
  right
  intro m_pre n_pre flat_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_2_split_goal_1 m_pre n_pre flat_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
    | exact proof_of_solver_entail_wit_2_split_goal_2 m_pre n_pre flat_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9

theorem proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1 := by
  intro m_pre n_pre flat_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have he : (i+1)*m_pre=i*m_pre+j := by nlinarith
  rw [he]
  exact PreH12

theorem proof_of_solver_entail_wit_3 : solver_entail_wit_3 := by
  unfold solver_entail_wit_3
  right
  intro m_pre n_pre flat_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_3_split_goal_1 m_pre n_pre flat_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1 := by
  intro m_pre n_pre flat_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  intro k hk
  by_cases he : k=i*m_pre+j
  · subst k
    exact Znth_replace_Znth_Same 0 flat_2 (i*m_pre+j) 0 (by constructor <;> nlinarith)
  · rw [Znth_replace_Znth_Diff 0 flat_2 (i*m_pre+j) k 0 (by constructor <;> nlinarith) (by omega) (Ne.symm he)]
    exact PreH12 k (by omega)

theorem proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2 := by
  intro m_pre n_pre flat_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  rw [Zlength_replace_Znth]
  exact PreH11

theorem proof_of_solver_entail_wit_4_split_goal_3 : solver_entail_wit_4_split_goal_3 := by
  intro m_pre n_pre flat_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  intro h
  constructor <;> nlinarith

theorem proof_of_solver_entail_wit_4 : solver_entail_wit_4 := by
  unfold solver_entail_wit_4
  right
  intro m_pre n_pre flat_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_4_split_goal_1 m_pre n_pre flat_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
    | exact proof_of_solver_entail_wit_4_split_goal_2 m_pre n_pre flat_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
    | exact proof_of_solver_entail_wit_4_split_goal_3 m_pre n_pre flat_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1 := by
  intro m_pre n_pre flat i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  rw [zero_mul]
  apply GreedyTrace_zero flat PreH8
  have he : n_pre*m_pre=i*m_pre := by nlinarith
  rw [he]
  exact PreH9

theorem proof_of_solver_entail_wit_5_split_goal_2 : solver_entail_wit_5_split_goal_2 := by
  intro m_pre n_pre flat i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  intro k hk
  left
  apply PreH9 k
  have he : i*m_pre=n_pre*m_pre := by nlinarith
  rw [he,← PreH8]
  exact hk

theorem proof_of_solver_entail_wit_5 : solver_entail_wit_5 := by
  unfold solver_entail_wit_5
  right
  intro m_pre n_pre flat i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_5_split_goal_1 m_pre n_pre flat i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
    | exact proof_of_solver_entail_wit_5_split_goal_2 m_pre n_pre flat i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9

theorem proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1 := by
  intro m_pre n_pre grid_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  simpa only [add_zero] using PreH10

theorem proof_of_solver_entail_wit_6_split_goal_2 : solver_entail_wit_6_split_goal_2 := by
  intro m_pre n_pre grid_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  intro h
  constructor <;> nlinarith

theorem proof_of_solver_entail_wit_6 : solver_entail_wit_6 := by
  unfold solver_entail_wit_6
  right
  intro m_pre n_pre grid_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_6_split_goal_1 m_pre n_pre grid_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
    | exact proof_of_solver_entail_wit_6_split_goal_2 m_pre n_pre grid_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10

theorem proof_of_solver_entail_wit_7_split_goal_1 : solver_entail_wit_7_split_goal_1 := by
  intro m_pre n_pre grid_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  apply GreedyTrace_skip (i*m_pre+j) grid_2 PreH13 (PreH10 PreH1)
  rcases PreH12 (i*m_pre+j) (by have h:=PreH10 PreH1; omega) with hz | hc
  · contradiction
  · exact hc

theorem proof_of_solver_entail_wit_7 : solver_entail_wit_7 := by
  unfold solver_entail_wit_7
  right
  intro m_pre n_pre grid_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_7_split_goal_1 m_pre n_pre grid_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14

theorem proof_of_solver_entail_wit_8 : solver_entail_wit_8 := by
  unfold solver_entail_wit_8
  right
  intro m_pre n_pre grid_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  obtain ⟨available,hr,hplace⟩ := five_colour_neighbour_available__solver_colour_search grid_2 n_pre m_pre i j PreH2 PreH4 (by omega) (by omega) PreH14
  Exists available
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hplace | assumption | omega | (intro color hc; omega)

theorem proof_of_solver_entail_wit_11_split_goal_1 : solver_entail_wit_11_split_goal_1 := by
  intro m_pre n_pre available grid_2 c t j i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have he := can_place_one_iff_legal_color__solver_colour_search grid_2 n_pre m_pre i j t PreH5 PreH7 (by omega) (by omega) PreH18 (by omega)
  refine ⟨he.mp PreH2,?_⟩
  intro d hd hlegal
  exact PreH20 d hd ((can_place_one_iff_legal_color__solver_colour_search grid_2 n_pre m_pre i j d PreH5 PreH7 (by omega) (by omega) PreH18 (by omega)).mpr hlegal)

theorem proof_of_solver_entail_wit_11 : solver_entail_wit_11 := by
  unfold solver_entail_wit_11
  right
  intro m_pre n_pre available grid_2 c t j i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_11_split_goal_1 m_pre n_pre available grid_2 c t j i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_solver_entail_wit_12_1 : solver_entail_wit_12_1 := by
  unfold solver_entail_wit_12_1
  right
  intro m_pre n_pre available grid_2 c t_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  exact False.elim (PreH17 available (by omega) PreH20)

theorem proof_of_solver_entail_wit_13 : solver_entail_wit_13 := by
  unfold solver_entail_wit_13
  right
  intro m_pre n_pre available_2 grid_2 c t j i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have hnone : NoPlaceableColorBelow grid_2 n_pre m_pre i j (t+1) := by
    intro d hd
    by_cases hlt : d<t
    · exact PreH20 d (by omega)
    · have he : d=t := by omega
      simpa only [he] using PreH2
  Exists available_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hnone | assumption | omega

theorem proof_of_solver_entail_wit_14_colour_found_split_goal_1 : solver_entail_wit_14_colour_found_split_goal_1 := by
  intro m_pre n_pre grid_2 i j t c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  exact ⟨PreH17,PreH16,by intro prev hp; omega⟩

theorem proof_of_solver_entail_wit_14_colour_found_split_goal_2 : solver_entail_wit_14_colour_found_split_goal_2 := by
  intro m_pre n_pre grid_2 i j t c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  exact ⟨PreH16,by intro prev hp; omega⟩

theorem proof_of_solver_entail_wit_14_colour_found_split_goal_3 : solver_entail_wit_14_colour_found_split_goal_3 := by
  intro m_pre n_pre grid_2 i j t c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  exact PreH17.1.1.2

theorem proof_of_solver_entail_wit_14_colour_found_split_goal_4 : solver_entail_wit_14_colour_found_split_goal_4 := by
  intro m_pre n_pre grid_2 i j t c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  exact PreH17.1.1.1

theorem proof_of_solver_entail_wit_14_colour_found : solver_entail_wit_14_colour_found := by
  unfold solver_entail_wit_14_colour_found
  right
  intro m_pre n_pre grid_2 i j t c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_14_colour_found_split_goal_1 m_pre n_pre grid_2 i j t c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
    | exact proof_of_solver_entail_wit_14_colour_found_split_goal_2 m_pre n_pre grid_2 i j t c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
    | exact proof_of_solver_entail_wit_14_colour_found_split_goal_3 m_pre n_pre grid_2 i j t c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
    | exact proof_of_solver_entail_wit_14_colour_found_split_goal_4 m_pre n_pre grid_2 i j t c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17

theorem proof_of_solver_entail_wit_17_colour_found_split_goal_1 : solver_entail_wit_17_colour_found_split_goal_1 := by
  intro m_pre n_pre grid_2 size c j i retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  exact ⟨PreH26,greedy_side_extend__solver_greedy_side grid_2 n_pre m_pre i j c size retval_2 PreH27 PreH6 PreH2 PreH1⟩

theorem proof_of_solver_entail_wit_17_colour_found_split_goal_2 : solver_entail_wit_17_colour_found_split_goal_2 := by
  intro m_pre n_pre grid_2 size c j i retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  exact greedy_side_extend__solver_greedy_side grid_2 n_pre m_pre i j c size retval_2 PreH27 PreH6 PreH2 PreH1

theorem proof_of_solver_entail_wit_17_colour_found_split_goal_3 : solver_entail_wit_17_colour_found_split_goal_3 := by
  intro m_pre n_pre grid_2 size c j i retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  have h := PreH6.2.1
  omega

theorem proof_of_solver_entail_wit_17_colour_found : solver_entail_wit_17_colour_found := by
  unfold solver_entail_wit_17_colour_found
  right
  intro m_pre n_pre grid_2 size c j i retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_17_colour_found_split_goal_1 m_pre n_pre grid_2 size c j i retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
    | exact proof_of_solver_entail_wit_17_colour_found_split_goal_2 m_pre n_pre grid_2 size c j i retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
    | exact proof_of_solver_entail_wit_17_colour_found_split_goal_3 m_pre n_pre grid_2 size c j i retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28

theorem proof_of_solver_entail_wit_18_1_colour_found_split_goal_1 : solver_entail_wit_18_1_colour_found_split_goal_1 := by
  intro m_pre n_pre grid_2 size c j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  exact ⟨PreH21,Or.inl (by omega)⟩

theorem proof_of_solver_entail_wit_18_1_colour_found : solver_entail_wit_18_1_colour_found := by
  unfold solver_entail_wit_18_1_colour_found
  right
  intro m_pre n_pre grid_2 size c j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_18_1_colour_found_split_goal_1 m_pre n_pre grid_2 size c j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21

theorem proof_of_solver_entail_wit_18_2_colour_found_split_goal_1 : solver_entail_wit_18_2_colour_found_split_goal_1 := by
  intro m_pre n_pre grid_2 size c j i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  exact ⟨PreH25,Or.inr (Or.inl PreH3)⟩

theorem proof_of_solver_entail_wit_18_2_colour_found : solver_entail_wit_18_2_colour_found := by
  unfold solver_entail_wit_18_2_colour_found
  right
  intro m_pre n_pre grid_2 size c j i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_18_2_colour_found_split_goal_1 m_pre n_pre grid_2 size c j i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_solver_entail_wit_18_3_colour_found_split_goal_1 : solver_entail_wit_18_3_colour_found_split_goal_1 := by
  intro m_pre n_pre grid_2 size c j i retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  exact ⟨PreH28,Or.inr (Or.inr ⟨retval_2,PreH2,PreH1⟩)⟩

theorem proof_of_solver_entail_wit_18_3_colour_found : solver_entail_wit_18_3_colour_found := by
  unfold solver_entail_wit_18_3_colour_found
  right
  intro m_pre n_pre grid_2 size c j i retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_18_3_colour_found_split_goal_1 m_pre n_pre grid_2 size c j i retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28

theorem proof_of_solver_entail_wit_19_colour_found : solver_entail_wit_19_colour_found := by
  unfold solver_entail_wit_19_colour_found
  right
  intro m_pre n_pre grid i j c size PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hpaint : PaintRectanglePrefix grid grid m_pre i j size c ((i-i)*size) := by
    refine ⟨rfl,?_⟩
    intro k hk
    exact Or.inr ⟨by intro off hoff; nlinarith,rfl⟩
  Exists grid
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hpaint | assumption | omega

theorem proof_of_solver_entail_wit_20_colour_found : solver_entail_wit_20_colour_found := by
  unfold solver_entail_wit_20_colour_found
  right
  intro m_pre n_pre current_2 before_2 r size c j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have hpaint : PaintRectanglePrefix before_2 current_2 m_pre i j size c ((r-i)*size+(j-j)) := by simpa only [sub_self,add_zero] using PreH24
  have hbound : j<j+size → 0≤r*m_pre+j ∧ r*m_pre+j<n_pre*m_pre := by intro h; constructor <;> nlinarith
  Exists before_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hpaint | exact hbound | assumption | omega

theorem proof_of_solver_entail_wit_21_colour_found : solver_entail_wit_21_colour_found := by
  unfold solver_entail_wit_21_colour_found
  right
  intro m_pre n_pre current_2 before_2 q r size c j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hpaint : PaintRectanglePrefix before_2 current_2 m_pre i j size c (((r+1)-i)*size) := by
    have he : ((r+1)-i)*size=(r-i)*size+(q-j) := by nlinarith
    rw [he]
    exact PreH27
  Exists before_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hpaint | assumption | omega

theorem proof_of_solver_entail_wit_22_colour_found : solver_entail_wit_22_colour_found := by
  unfold solver_entail_wit_22_colour_found
  right
  intro m_pre n_pre current_2 before_2 q r size c j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hidx : 0≤r*m_pre+q ∧ r*m_pre+q<Zlength current_2 := by have h:=PreH19 PreH1; omega
  have hpaint := paint_prefix_replace__solver_paint before_2 current_2 m_pre i j size c r q PreH12 (by omega) (by omega) hidx PreH27
  have hcanon := canonical_grid_replace__solver_paint current_2 (r*m_pre+q) c hidx (by omega) PreH23
  have hlen : Zlength (replace_Znth (r*m_pre+q) c current_2)=n_pre*m_pre := by rw [Zlength_replace_Znth,PreH21]
  have hbound : q+1<j+size → 0≤r*m_pre+(q+1) ∧ r*m_pre+(q+1)<n_pre*m_pre := by intro h; constructor <;> nlinarith
  Exists before_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hpaint | exact hcanon | exact hlen | exact hbound | assumption | omega

theorem proof_of_solver_entail_wit_23_split_goal_1 : solver_entail_wit_23_split_goal_1 := by
  intro m_pre n_pre grid_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have he : (i+1)*m_pre=i*m_pre+j := by nlinarith
  rw [he]
  exact PreH13

theorem proof_of_solver_entail_wit_23 : solver_entail_wit_23 := by
  unfold solver_entail_wit_23
  right
  intro m_pre n_pre grid_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_23_split_goal_1 m_pre n_pre grid_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13

theorem proof_of_solver_entail_wit_24_colour_found_split_goal_1 : solver_entail_wit_24_colour_found_split_goal_1 := by
  intro m_pre n_pre current before r size c j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  rw [← add_assoc]
  apply GreedyTrace_place (i*m_pre+j) before current i j c size PreH22 rfl (by omega) (by omega) PreH21 PreH23
  have he : size*size=(r-i)*size := by nlinarith
  rw [he]
  exact PreH24

theorem proof_of_solver_entail_wit_24_colour_found_split_goal_2 : solver_entail_wit_24_colour_found_split_goal_2 := by
  intro m_pre n_pre current before r size c j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  intro h
  constructor <;> nlinarith

theorem proof_of_solver_entail_wit_24_colour_found : solver_entail_wit_24_colour_found := by
  unfold solver_entail_wit_24_colour_found
  right
  intro m_pre n_pre current before r size c j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_24_colour_found_split_goal_1 m_pre n_pre current before r size c j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
    | exact proof_of_solver_entail_wit_24_colour_found_split_goal_2 m_pre n_pre current before r size c j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_solver_entail_wit_25_split_goal_1 : solver_entail_wit_25_split_goal_1 := by
  intro m_pre n_pre grid_2 i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  simpa only [add_assoc] using PreH11

theorem proof_of_solver_entail_wit_25_split_goal_2 : solver_entail_wit_25_split_goal_2 := by
  intro m_pre n_pre grid_2 i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  intro h
  constructor <;> nlinarith

theorem proof_of_solver_entail_wit_25 : solver_entail_wit_25 := by
  unfold solver_entail_wit_25
  right
  intro m_pre n_pre grid_2 i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_25_split_goal_1 m_pre n_pre grid_2 i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
    | exact proof_of_solver_entail_wit_25_split_goal_2 m_pre n_pre grid_2 i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  unfold solver_return_wit_1
  right
  intro m_pre n_pre grid i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have htrace : GreedyPlacementTrace n_pre m_pre (n_pre*m_pre) grid := by
    have he : i=n_pre := by omega
    simpa only [he] using PreH10
  have htrace_qcp := greedyPlacementTrace_to_qcp htrace
  have hpartial := greedy_trace_implies_partial_tiling__solver_final n_pre m_pre (n_pre*m_pre) grid PreH2 PreH4 htrace_qcp
  obtain ⟨out,hflat,hspec⟩ := complete_partial_tiling_implies_spec__solver_final n_pre m_pre grid PreH2 PreH4 PreH8 hpartial
  Exists out
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    · simpa only [Codeforces.examples_shard01.P081_432E_square_tiling.lean.concat,
        Codeforces.examples_shard01.P081_432E_square_tiling.lean.Flatten,
        SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib.Flatten] using hflat.symm
    · simpa only [Codeforces.examples_shard01.P081_432E_square_tiling.lean.Spec,
        SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib.Spec,
        Codeforces.examples_shard01.P081_432E_square_tiling.lean.SquareTiling,
        SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib.SquareTiling,
        Codeforces.examples_shard01.P081_432E_square_tiling.lean.SameColorPath,
        SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib.SameColorPath,
        Codeforces.examples_shard01.P081_432E_square_tiling.lean.AdjCell,
        SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib.AdjCell,
        Codeforces.examples_shard01.P081_432E_square_tiling.lean.Flatten,
        SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib.Flatten] using hspec

end Codeforces.examples_shard01.P081_432E_square_tiling.lean.groundtruth.P081_432E_square_tiling_proof_manual
