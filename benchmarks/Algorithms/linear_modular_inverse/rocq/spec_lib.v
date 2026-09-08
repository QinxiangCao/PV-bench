From Coq Require Import ZArith List.
From AUXLib Require Import ListLib.

Import ListNotations.
Local Open Scope Z_scope.

Definition PrimeForLinearInverse (p : Z) : Prop :=
  2 <= p /\
  forall divisor,
    2 <= divisor < p ->
    p mod divisor <> 0.
Definition CanonicalModularInverse
    (p index value : Z) : Prop :=
  1 <= index < p /\
  0 < value < p /\
  exists coefficient,
    index * value + p * coefficient = 1.
Definition ModularInversePrefix
    (p next : Z) (values : list Z) : Prop :=
  Zlength values = next - 1 /\
  forall index,
    1 <= index < next ->
    CanonicalModularInverse p index
      (Znth (index - 1) values 0).
