From PVbench.Algorithms.bucket_sort.rocq.groundtruth Require Import bucket_sort_goal bucket_sort_proof_auto bucket_sort_proof_manual.

Module VC_Correctness : VC_Correct.
  Include bucket_sort_proof_auto.
  Include bucket_sort_proof_manual.
End VC_Correctness.
