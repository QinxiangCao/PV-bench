From Coq Require Import ZArith List.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.

Definition CRTProduct (moduli : list Z) : Z :=
  fold_right Z.mul 1 moduli.

(** A well-formed nonempty system of congruences: corresponding lists have
    the same length, each modulus is positive, each remainder is canonical,
    and distinct moduli are coprime. *)
Definition CRTInputValid
    (remainders moduli : list Z) : Prop :=
  Zlength remainders = Zlength moduli /\
  1 <= Zlength moduli /\
  (forall i,
      0 <= i < Zlength moduli ->
      1 <= Znth i moduli 0 /\
      0 <= Znth i remainders 0 < Znth i moduli 0) /\
  (forall i j,
      0 <= i /\ i < j /\ j < Zlength moduli ->
      Z.gcd (Znth i moduli 0) (Znth j moduli 0) = 1).

(** The C example intentionally uses [int].  The product bound makes every
    multiplication of two reduced residues fit.  The final clause accounts
    for the hard-frozen [exgcd] interface, which exposes an arbitrary signed
    [int] Bezout coefficient but no stronger coefficient bound. *)
Definition CRTMachineSafe
    (remainders moduli : list Z) : Prop :=
  let product := CRTProduct moduli in
  1 <= product <= 46340 /\
  (forall i coefficient,
      0 <= i < Zlength moduli ->
      (-2147483648 <= coefficient <= 2147483647) ->
      -2147483648 <=
        coefficient * (product / Znth i moduli 0) <=
        2147483647).

(** The public functional result: [answer] is the canonical representative
    modulo the product and satisfies every input congruence.  Pairwise
    coprimality in [CRTInputValid] makes this representative unique. *)
Definition CanonicalCRTSolution
    (remainders moduli : list Z) (answer : Z) : Prop :=
  0 <= answer < CRTProduct moduli /\
  forall i,
    0 <= i < Zlength moduli ->
    answer mod Znth i moduli 0 = Znth i remainders 0.

(** Internal mathematical state for the accumulation phase.  C-level bounds,
    pointer ownership, and the range of [processed] deliberately remain in
    the loop invariant rather than being hidden in this predicate. *)
