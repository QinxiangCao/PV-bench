From PVbench.Data_structures.priority_queue.rocq.groundtruth Require Import priority_queue_goal priority_queue_proof_auto priority_queue_proof_manual.

Module VC_Correctness : VC_Correct.
  Include priority_queue_proof_auto.
  Include priority_queue_proof_manual.
End VC_Correctness.
