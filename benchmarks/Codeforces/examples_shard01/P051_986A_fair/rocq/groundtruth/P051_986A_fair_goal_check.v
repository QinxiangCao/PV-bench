From PVbench.Codeforces.examples_shard01.P051_986A_fair.rocq.groundtruth Require Import P051_986A_fair_goal P051_986A_fair_proof_auto P051_986A_fair_proof_manual.

Module VC_Correctness : VC_Correct.
  Include array2_strategy_proof.
  Include array2_char_strategy_proof.
  Include int_array_strategy_proof.
  Include char_array_strategy_proof.
  Include array2_ext_strategy_proof.
  Include P051_986A_fair_proof_auto.
  Include P051_986A_fair_proof_manual.
End VC_Correctness.
