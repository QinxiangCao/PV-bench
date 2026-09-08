From PVbench.Codeforces.examples_shard00.P031_1194C_from_s_to_t.rocq.groundtruth Require Import P031_1194C_from_s_to_t_goal P031_1194C_from_s_to_t_proof_auto P031_1194C_from_s_to_t_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include P031_1194C_from_s_to_t_proof_auto.
  Include P031_1194C_from_s_to_t_proof_manual.
End VC_Correctness.
