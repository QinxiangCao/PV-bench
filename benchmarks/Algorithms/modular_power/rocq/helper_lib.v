Require Export PVbench.Algorithms.modular_power.rocq.spec_lib.
From Coq Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.
Require Import Coq.micromega.Lia.
Require Import Coq.setoid_ring.Ring.
Require Import SimpleC.SL.IntLib.

Definition ModularPowerProgress
    (original_base original_exponent modulus
     current_base remaining_exponent accumulator : Z) : Prop :=
  (accumulator * current_base ^ remaining_exponent) mod modulus =
  (original_base ^ original_exponent) mod modulus.
