Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.

Import ListNotations.
Local Open Scope Z_scope.

Definition StrictPrime (p : Z) : Prop :=
  1 < p /\
  forall d : Z,
    0 < d ->
    Z.divide d p ->
    d = 1 \/ d = p.

(** [HasProperDivisorBelow bound k] says that [k] has a nontrivial positive
    divisor strictly below both [bound] and [k]. *)
Definition HasProperDivisorBelow (bound k : Z) : Prop :=
  exists d : Z,
    2 <= d /\
    d < bound /\
    d < k /\
    Z.divide d k.

(** Exact, two-sided 0/1 interpretation of a mathematical proposition. *)
Definition PrimeIndicatorList (n : Z) (values : list Z) : Prop :=
  Zlength values = n /\
  forall k : Z,
    1 <= k <= n ->
    ((StrictPrime k /\ Znth (k - 1) values 0 = 1) \/
     (~ StrictPrime k /\ Znth (k - 1) values 0 = 0)).

(** State of the first initialization loop: all program-owned indices before
    [next] have already been written to one. *)
