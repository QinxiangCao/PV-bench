From Coq Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.
Require Import Coq.micromega.Lia.
Require Import Coq.setoid_ring.Ring.
Require Import SimpleC.SL.IntLib.

Definition ModularPower
    (base exponent modulus result : Z) : Prop :=
  result = (base ^ exponent) mod modulus.
