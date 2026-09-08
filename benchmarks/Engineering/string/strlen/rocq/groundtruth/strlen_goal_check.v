From PVbench.Engineering.string.strlen.rocq.groundtruth Require Import strlen_goal strlen_proof_auto strlen_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include strlen_proof_auto.
  Include strlen_proof_manual.
End VC_Correctness.
