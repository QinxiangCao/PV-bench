From PVbench.Codeforces.examples_shard01.P049_411B_multi_core_processor.rocq.groundtruth Require Import P049_411B_multi_core_processor_goal P049_411B_multi_core_processor_proof_auto P049_411B_multi_core_processor_proof_manual.

Module VC_Correctness : VC_Correct.
  Include array2_strategy_proof.
  Include array2_char_strategy_proof.
  Include int_array_strategy_proof.
  Include char_array_strategy_proof.
  Include array2_ext_strategy_proof.
  Include P049_411B_multi_core_processor_proof_auto.
  Include P049_411B_multi_core_processor_proof_manual.
End VC_Correctness.
