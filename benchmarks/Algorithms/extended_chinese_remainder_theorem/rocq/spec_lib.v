From Coq Require Import ZArith List Lia.
Require Import MaxMinLib.MaxMin AUXLib.MonotonicList.
Require Import AUXLib.ListLib.
Import ListNotations.
Local Open Scope Z_scope.
From Coq Require Import Lia.
From Coq Require Import Lia Ring.

Definition CRTLCMPrefix (moduli : list Z) (count : Z) : Z :=
  fold_left Z.lcm (sublist 0 count moduli) 1.

Definition CRTCongruent (value residue modulus : Z) : Prop :=
  exists quotient, value = residue + modulus * quotient.

Definition CRTAllCongruences
    (residues moduli : list Z) (count value : Z) : Prop :=
  Forall2 (fun residue modulus => CRTCongruent value residue modulus)
    (sublist 0 count residues) (sublist 0 count moduli).

Definition ExtendedCRTSystemCompatible
    (residues moduli : list Z) (n : Z) : Prop :=
  exists solution, CRTAllCongruences residues moduli n solution.

(* The candidate's nonnegativity is part of the requested mathematical
   answer; machine bounds and input restrictions belong to the C contract. *)
Definition ExtendedCRTSystemResult
    (residues moduli : list Z)
    (n result combined_modulus : Z) : Prop :=
  combined_modulus = CRTLCMPrefix moduli n /\
  min_value_of_subset Z.le
    (fun value => 0 <= value /\ CRTAllCongruences residues moduli n value)
    (fun value : Z => value) result.
