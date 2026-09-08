From PVbench.Engineering.string.memory.rocq.groundtruth Require Import memory_goal memory_proof_auto memory_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include memory_proof_auto.
  Include memory_proof_manual.
End VC_Correctness.
