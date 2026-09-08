import Codeforces.examples_shard01.P029_817A_treasure_hunt.lean.groundtruth.P029_817A_treasure_hunt_goal
import Codeforces.examples_shard01.P029_817A_treasure_hunt.lean.groundtruth.P029_817A_treasure_hunt_proof_auto
import Codeforces.examples_shard01.P029_817A_treasure_hunt.lean.groundtruth.proof_lib

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace Codeforces.examples_shard01.P029_817A_treasure_hunt.lean.groundtruth.P029_817A_treasure_hunt_proof_manual

open Codeforces.examples_shard01.P029_817A_treasure_hunt.lean
open Codeforces.examples_shard01.P029_817A_treasure_hunt.lean.groundtruth.proof_lib
open Codeforces.examples_shard01.P029_817A_treasure_hunt.lean.groundtruth.P029_817A_treasure_hunt_goal
open scoped SimpleC

open SimpleC.SL.CommonAssertion SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.SeparationLogic
open Codeforces.examples_shard01.P029_817A_treasure_hunt.lean.groundtruth.P029_817A_treasure_hunt_goal Codeforces.examples_shard01.P029_817A_treasure_hunt.lean.groundtruth.proof_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

theorem proof_of_solver_entail_wit_1_1_split_goal_1 : solver_entail_wit_1_1_split_goal_1 := by
  intro y x y2 x2 y1 x1 h
  intros
  simp [AbsDiff, show ¬ x1 < x2 by omega]

theorem proof_of_solver_entail_wit_1_1 : solver_entail_wit_1_1 := by
  unfold solver_entail_wit_1_1
  right
  intro y x y2 x2 y1 x1
  intros
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    apply proof_of_solver_entail_wit_1_1_split_goal_1 y x y2 x2 y1 x1 <;> assumption

theorem proof_of_solver_entail_wit_1_2_split_goal_1 : solver_entail_wit_1_2_split_goal_1 := by
  intro y x y2 x2 y1 x1 h
  intros
  simp [AbsDiff, h]

theorem proof_of_solver_entail_wit_1_2 : solver_entail_wit_1_2 := by
  unfold solver_entail_wit_1_2
  right
  intro y x y2 x2 y1 x1
  intros
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    apply proof_of_solver_entail_wit_1_2_split_goal_1 y x y2 x2 y1 x1 <;> assumption

theorem proof_of_solver_entail_wit_2_1_split_goal_1 : solver_entail_wit_2_1_split_goal_1 := by
  intro y x y2 x2 y1 x1 h
  intros
  simp [AbsDiff, show ¬ y1 < y2 by omega]

theorem proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1 := by
  unfold solver_entail_wit_2_1
  right
  intro y x y2 x2 y1 x1
  intros
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    apply proof_of_solver_entail_wit_2_1_split_goal_1 y x y2 x2 y1 x1 <;> assumption

theorem proof_of_solver_entail_wit_2_2_split_goal_1 : solver_entail_wit_2_2_split_goal_1 := by
  intro y x y2 x2 y1 x1 h
  intros
  simp [AbsDiff, h]

theorem proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2 := by
  unfold solver_entail_wit_2_2
  right
  intro y x y2 x2 y1 x1
  intros
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    apply proof_of_solver_entail_wit_2_2_split_goal_1 y x y2 x2 y1 x1 <;> assumption

theorem proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1 := by
  intro y x y2 x2 y1 x1 h
  intros
  exact Or.inr ⟨fun reach => h reach.2.2, rfl⟩

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  unfold solver_return_wit_1
  right
  intro y x y2 x2 y1 x1
  intros
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    apply proof_of_solver_return_wit_1_split_goal_1 y x y2 x2 y1 x1 <;> assumption

theorem proof_of_solver_return_wit_2_split_goal_1 : solver_return_wit_2_split_goal_1 := by
  intro y x y2 x2 y1 x1 parity hy hx
  intros
  exact Or.inl ⟨⟨hx, hy, parity⟩, rfl⟩

theorem proof_of_solver_return_wit_2 : solver_return_wit_2 := by
  unfold solver_return_wit_2
  right
  intro y x y2 x2 y1 x1
  intros
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    apply proof_of_solver_return_wit_2_split_goal_1 y x y2 x2 y1 x1 <;> assumption

theorem proof_of_solver_return_wit_3_split_goal_1 : solver_return_wit_3_split_goal_1 := by
  intro y x y2 x2 y1 x1 h
  intros
  exact Or.inr ⟨fun reach => h reach.1, rfl⟩

theorem proof_of_solver_return_wit_3 : solver_return_wit_3 := by
  unfold solver_return_wit_3
  right
  intro y x y2 x2 y1 x1
  intros
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    apply proof_of_solver_return_wit_3_split_goal_1 y x y2 x2 y1 x1 <;> assumption

theorem proof_of_solver_return_wit_4_split_goal_1 : solver_return_wit_4_split_goal_1 := by
  intro y x y2 x2 y1 x1 h
  intros
  exact Or.inr ⟨fun reach => h reach.2.1, rfl⟩

theorem proof_of_solver_return_wit_4 : solver_return_wit_4 := by
  unfold solver_return_wit_4
  right
  intro y x y2 x2 y1 x1
  intros
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    apply proof_of_solver_return_wit_4_split_goal_1 y x y2 x2 y1 x1 <;> assumption

end Codeforces.examples_shard01.P029_817A_treasure_hunt.lean.groundtruth.P029_817A_treasure_hunt_proof_manual
