From PVbench.Algorithms.rod_cutting.rocq.groundtruth Require Import rod_cutting_goal rod_cutting_proof_auto rod_cutting_proof_manual.

Module VC_Correctness : VC_Correct.
  Include rod_cutting_proof_auto.
  Include rod_cutting_proof_manual.
End VC_Correctness.
