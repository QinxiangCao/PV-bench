From Coq Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.

Definition ModularMul
    (multiplicand multiplier modulus result : Z) : Prop :=
  (* A bounded residue of the mathematical product.  This interval defines
     the answer, independently of C integer bounds or execution safety. *)
  -modulus < result < modulus /\
  (modulus | multiplicand * multiplier - result).

Require Import Coq.micromega.Lia.
Require Import Coq.setoid_ring.Ring.
From Coq Require Import Lia.
