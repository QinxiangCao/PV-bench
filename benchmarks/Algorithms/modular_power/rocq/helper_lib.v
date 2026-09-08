Require Import PVbench.Algorithms.modular_power.rocq.spec_lib.

From Coq Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.

Definition ModularPowerProgress
    (original_base original_exponent modulus
     current_base remaining_exponent accumulator : Z) : Prop :=
  (accumulator * current_base ^ remaining_exponent) mod modulus =
  (original_base ^ original_exponent) mod modulus.
