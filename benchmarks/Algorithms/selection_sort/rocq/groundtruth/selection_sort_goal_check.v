From PVbench.Algorithms.selection_sort.rocq.groundtruth Require Import selection_sort_goal selection_sort_proof_auto selection_sort_proof_manual.

Module VC_Correctness : VC_Correct.
  Include selection_sort_proof_auto.
  Include selection_sort_proof_manual.
End VC_Correctness.
