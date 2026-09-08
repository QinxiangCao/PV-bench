From Coq Require Import ZArith List Znumtheory Sorting.Sorted.
Import ListNotations.
Local Open Scope Z_scope.

Definition PrimeFactorization (original : Z) (factors : list Z) : Prop :=
  Forall prime factors /\
  Sorted Z.le factors /\
  fold_right Z.mul 1 factors = original /\
  (forall q : Z,
      In q factors <-> prime q /\ Z.divide q original).

(** Internal mathematical state shared by both trial-division loop heads.
    Machine ranges, [cnt]/list-length bindings, modulo guards, and array
    ownership deliberately remain visible in the C annotation. *)
