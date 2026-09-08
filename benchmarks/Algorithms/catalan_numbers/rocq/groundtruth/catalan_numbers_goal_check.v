From PVbench.Algorithms.catalan_numbers.rocq.groundtruth Require Import catalan_numbers_goal catalan_numbers_proof_auto catalan_numbers_proof_manual.

Module VC_Correctness : VC_Correct.
  Include catalan_numbers_proof_auto.
  Include catalan_numbers_proof_manual.
End VC_Correctness.
