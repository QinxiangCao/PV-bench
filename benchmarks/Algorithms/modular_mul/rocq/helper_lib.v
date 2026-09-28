Require Export PVbench.Algorithms.modular_mul.rocq.spec_lib.
From Coq Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.

Definition ModularMulProgress
    (original_multiplicand original_multiplier modulus
     current_multiplicand remaining_multiplier accumulator sign : Z) : Prop :=
  exists quotient,
    original_multiplicand * original_multiplier =
      sign * (accumulator + current_multiplicand * remaining_multiplier) +
      modulus * quotient.

Require Import Coq.micromega.Lia.
Require Import Coq.setoid_ring.Ring.
From Coq Require Import Lia.
