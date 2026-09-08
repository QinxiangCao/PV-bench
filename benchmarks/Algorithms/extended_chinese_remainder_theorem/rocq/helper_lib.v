Require Import PVbench.Algorithms.extended_chinese_remainder_theorem.rocq.spec_lib.

From Coq Require Import ZArith List.
Require Import AUXLib.ListLib.
Import ListNotations.
Local Open Scope Z_scope.

Definition CRTPrefixMeaning
    (residues moduli : list Z)
    (count answer combined_modulus : Z) : Prop :=
  combined_modulus = CRTLCMPrefix moduli count /\
  CRTAllCongruences residues moduli count answer.
Definition CRTReducedMergeEquation
    (current_answer current_modulus next_residue next_modulus
     multiplier : Z) : Prop :=
  let gcd := Z.gcd current_modulus next_modulus in
  exists adjustment,
    (current_modulus / gcd) * multiplier +
      (next_modulus / gcd) * adjustment =
    (next_residue - current_answer) / gcd.
