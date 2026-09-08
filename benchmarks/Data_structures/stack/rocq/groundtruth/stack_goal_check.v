From PVbench.Data_structures.stack.rocq.groundtruth Require Import stack_goal stack_proof_auto stack_proof_manual.

Module VC_Correctness : VC_Correct.
  Include stack_proof_auto.
  Include stack_proof_manual.
End VC_Correctness.
