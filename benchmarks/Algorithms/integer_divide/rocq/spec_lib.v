From Coq Require Import ZArith List Znumtheory Sorting.Sorted.
Import ListNotations.
Local Open Scope Z_scope.
From Coq Require Import Lia.

(** [PrimeFactorization original factors] is the public mathematical meaning of
    the initialized output segment.  Membership is deliberately bidirectional:
    the segment contains no non-prime/non-divisor and omits no prime divisor of
    [original].  [Sorted Z.le] records the program's increasing trial-divisor
    order, while the product equation fixes multiplicities to the actual prime
    factorization rather than merely listing each distinct divisor once. *)
Definition PrimeFactorization (original : Z) (factors : list Z) : Prop :=
  Forall prime factors /\
  Sorted Z.le factors /\
  fold_right Z.mul 1 factors = original /\
  (forall q : Z,
      In q factors <-> prime q /\ Z.divide q original).
