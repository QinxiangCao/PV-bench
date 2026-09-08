From PVbench.Codeforces.examples_shard01.P014_1765E_exchange.rocq.groundtruth Require Import P014_1765E_exchange_goal P014_1765E_exchange_proof_auto P014_1765E_exchange_proof_manual.

Module VC_Correctness : VC_Correct.
  Include P014_1765E_exchange_proof_auto.
  Include P014_1765E_exchange_proof_manual.
End VC_Correctness.
