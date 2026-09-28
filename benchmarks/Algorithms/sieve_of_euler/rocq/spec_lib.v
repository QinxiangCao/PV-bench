Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Require Import Coq.ZArith.Znumtheory Coq.ZArith.Wf_Z MaxMinLib.MaxMin SetsClass.SetsClass AUXLib.MonotonicList Coq.Setoids.Setoid.

Module Legacy.
(** Mathematical primality, independent of the concrete sieve arrays. *)
Definition StrictPrime (p : Z) : Prop :=
  1 < p /\
  forall d : Z,
    0 < d ->
    Z.divide d p ->
    d = 1 \/ d = p.
End Legacy.

Module Modern.
Import Legacy.
Definition StrictPrime : Z -> Prop := Legacy.StrictPrime.

Definition PrimePrefixList (bound tot : Z) (primes : list Z) : Prop :=
  Forall StrictPrime (sublist 0 tot primes) /\
  Forall (Z.ge bound) (sublist 0 tot primes) /\
  (forall p : Z,
    2 <= p /\ p <= bound ->
    (StrictPrime p <->
     exists pos : Z,
       1 <= pos /\ pos <= tot /\
       Znth (pos - 1) primes 0 = p)) /\
  (forall p q : Z,
    1 <= p /\ p < q /\ q <= tot ->
    Znth (p - 1) primes 0 < Znth (q - 1) primes 0).
End Modern.

Export Legacy Modern.
