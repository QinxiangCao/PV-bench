Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Require Import AUXLib.MonotonicList.
Import ListNotations.
Local Open Scope Z_scope.

(** Mathematical primality, independent of any program array or sieve state. *)
Definition StrictPrime (p : Z) : Prop :=
  1 < p /\
  forall d : Z,
    0 < d ->
    Z.divide d p ->
    d = 1 \/ d = p.

(** The required final contents of the concrete segment [f[1]..f[n]].
    Logical position [k - 1] represents the program index [k]. *)
Definition PrimeIndicatorList (n : Z) (values : list Z) : Prop :=
  Zlength values = n /\
  forall k : Z,
    1 <= k <= n ->
    ((StrictPrime k /\ Znth (k - 1) values 0 = 1) \/
     (~ StrictPrime k /\ Znth (k - 1) values 0 = 0)).
