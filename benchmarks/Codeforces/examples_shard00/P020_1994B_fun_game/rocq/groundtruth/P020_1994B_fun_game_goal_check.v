From PVbench.Codeforces.examples_shard00.P020_1994B_fun_game.rocq.groundtruth Require Import P020_1994B_fun_game_goal P020_1994B_fun_game_proof_auto P020_1994B_fun_game_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include P020_1994B_fun_game_proof_auto.
  Include P020_1994B_fun_game_proof_manual.
End VC_Correctness.
