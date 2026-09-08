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

(** [LeastPrimeFactor p k] says [p] is the least prime divisor of [k]. *)
Definition LeastPrimeFactor (p k : Z) : Prop :=
  StrictPrime p /\
  Z.divide p k /\
  forall q : Z,
    StrictPrime q ->
    Z.divide q k ->
    p <= q.

(** Final meaning of a single [flag[k]] entry.  Primes keep their own value;
    composites store their least prime factor. *)
Definition FlagEntryFor (k value : Z) : Prop :=
  (StrictPrime k /\ value = k) \/
  (~ StrictPrime k /\ LeastPrimeFactor value k).

(** Logical position [k - 2] represents the concrete [flag[k]] slot. *)
Definition LeastPrimeFlagList (n : Z) (flags : list Z) : Prop :=
  Zlength flags = n - 1 /\
  forall k : Z,
    2 <= k /\ k <= n ->
    FlagEntryFor k (Znth (k - 2) flags 0).

(** The first [tot] entries of [primes] are exactly the primes not exceeding
    [bound], in increasing order.  Concrete index [pos] is logical [pos - 1]. *)
Definition PrimePrefixList (bound tot : Z) (primes : list Z) : Prop :=
  0 <= tot /\
  (forall pos : Z,
    1 <= pos /\ pos <= tot ->
    StrictPrime (Znth (pos - 1) primes 0) /\
    Znth (pos - 1) primes 0 <= bound) /\
  (forall p : Z,
    2 <= p /\ p <= bound ->
    (StrictPrime p <->
     exists pos : Z,
       1 <= pos /\ pos <= tot /\
       Znth (pos - 1) primes 0 = p)) /\
  (forall p q : Z,
    1 <= p /\ p < q /\ q <= tot ->
    Znth (p - 1) primes 0 < Znth (q - 1) primes 0).
Definition EulerSieveResult
    (n tot : Z) (flags primes : list Z) : Prop :=
  Zlength flags = n - 1 /\
  Zlength primes = n /\
  0 <= tot /\ tot <= n /\
  LeastPrimeFlagList n flags /\
  PrimePrefixList n tot primes.

(** Initialization loop: all concrete entries before [next] have been written
    to their own index value. *)
