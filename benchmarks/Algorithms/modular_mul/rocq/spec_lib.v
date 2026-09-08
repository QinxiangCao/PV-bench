From Coq Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.

Definition ModularMul
    (multiplicand multiplier modulus result : Z) : Prop :=
  -modulus < result < modulus /\
  exists quotient,
    multiplicand * multiplier = result + modulus * quotient.
