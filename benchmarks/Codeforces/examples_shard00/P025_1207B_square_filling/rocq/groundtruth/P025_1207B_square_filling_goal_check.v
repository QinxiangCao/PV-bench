From PVbench.Codeforces.examples_shard00.P025_1207B_square_filling.rocq.groundtruth Require Import P025_1207B_square_filling_goal P025_1207B_square_filling_proof_auto P025_1207B_square_filling_proof_manual.

Module VC_Correctness : VC_Correct.
  Include array2_strategy_proof.
  Include array2_char_strategy_proof.
  Include int_array_strategy_proof.
  Include char_array_strategy_proof.
  Include array2_ext_strategy_proof.
  Include P025_1207B_square_filling_proof_auto.
  Include P025_1207B_square_filling_proof_manual.
End VC_Correctness.
