From PVbench.Algorithms.kings_game.rocq.groundtruth Require Import kings_game_goal kings_game_proof_auto kings_game_proof_manual.

Module VC_Correctness : VC_Correct.
  Include kings_game_proof_auto.
  Include kings_game_proof_manual.
End VC_Correctness.
