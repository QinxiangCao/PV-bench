Require Import PVbench.Algorithms.sieve_of_euler.rocq.spec_lib.

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.

Import ListNotations.
Local Open Scope Z_scope.

Definition PrimeBounds (n tot : Z) (primes : list Z) : Prop :=
  forall pos : Z,
    1 <= pos /\ pos <= tot ->
    2 <= Znth (pos - 1) primes 0 /\
    Znth (pos - 1) primes 0 <= n.
Definition PriorNonDivisibility
    (current j : Z) (primes : list Z) : Prop :=
  forall pos : Z,
    1 <= pos /\ pos < j ->
    ~ Z.divide (Znth (pos - 1) primes 0) current.
Definition ProductIndex
    (current j : Z) (primes : list Z) : Z :=
  current * Znth (j - 1) primes 0.
Definition FlagValue (flags : list Z) (k : Z) : Z :=
  Znth (k - 2) flags 0.

(** Progress made by the current base inside the Euler inner loop.  Before the
    loop reaches index [j], every in-range product [current * primes[pos]] with
    [pos < j] has already been written and is a sound non-self flag entry. *)
Definition CurrentProductMarked
    (n current pos : Z) (flags primes : list Z) : Prop :=
  2 <= ProductIndex current pos primes /\
  ProductIndex current pos primes <= n ->
  FlagValue flags (ProductIndex current pos primes) =
    Znth (pos - 1) primes 0 /\
  FlagValue flags (ProductIndex current pos primes) <>
    ProductIndex current pos primes /\
  FlagEntryFor (ProductIndex current pos primes)
    (FlagValue flags (ProductIndex current pos primes)).
Definition CurrentBaseProgress
    (n current j : Z) (flags primes : list Z) : Prop :=
  forall pos : Z,
    1 <= pos /\ pos < j ->
    CurrentProductMarked n current pos flags primes.

(** A pair [base, primes[pos]] is exactly the kind of product that an earlier
    Euler-sieve inner loop would have written: [base] was already processed,
    the prime was already known by then, and no smaller processed prime had
    broken that inner loop first. *)
Definition EarlierLinearProduct
    (frontier k tot : Z) (primes : list Z) : Prop :=
  exists base pos : Z,
    2 <= base /\ base < frontier /\
    1 <= pos /\ pos <= tot /\
    Znth (pos - 1) primes 0 <= base /\
    PriorNonDivisibility base pos primes /\
    k = base * Znth (pos - 1) primes 0.
Definition FutureSelfCompleteness
    (frontier k tot : Z) (primes : list Z) : Prop :=
  ~ EarlierLinearProduct frontier k tot primes.
Definition FutureFlagState
    (frontier k tot : Z) (flags primes : list Z) : Prop :=
  (FlagValue flags k <> k -> FlagEntryFor k (FlagValue flags k)) /\
  (FlagValue flags k = k -> FutureSelfCompleteness frontier k tot primes).

(** At an outer-loop boundary, slots up to the current index already have their
    final least-prime-factor meaning.  Future non-self slots are sound marks.
    Future self-valued slots are not arbitrary: they have not been reachable as
    an eligible product of an earlier processed base and known prime.  This is
    the completeness fact needed to classify the successor slot when the outer
    boundary advances. *)
Definition EulerFlagState
    (n frontier tot : Z) (flags primes : list Z) : Prop :=
  Zlength flags = n - 1 /\
  forall k : Z,
    2 <= k /\ k <= n ->
    (k <= frontier -> FlagEntryFor k (FlagValue flags k)) /\
    (frontier < k -> FutureFlagState frontier k tot flags primes).
Definition EulerInitPrefix (n next : Z) (flags : list Z) : Prop :=
  Zlength flags = n - 1 /\
  forall k : Z,
    2 <= k /\ k < next ->
    Znth (k - 2) flags 0 = k.

(** Outer-loop state before processing [next].  Entries below [next] already
    have their final least-prime-factor meaning; the current slot [next] is
    meaningful too when [next <= n].  Future slots are allowed to remain at
    their initial self value, but any future non-self mark must already be a
    valid least-prime-factor mark.  [primes[1..tot]] lists exactly the primes
    below [next]. *)
Definition EulerOuterState
    (n next tot : Z) (flags primes : list Z) : Prop :=
  EulerFlagState n next tot flags primes /\
  Zlength primes = n /\
  2 <= next /\ next <= n + 1 /\
  0 <= tot /\ tot < next /\
  PrimePrefixList (next - 1) tot primes /\
  PrimeBounds n tot primes.

(** Inner-loop state after [current] has been classified and, if prime, appended
    to the prime prefix.  The current flag slot remains classified throughout
    the loop, future non-self marks remain sound, all current-base products
    before [j] have already been marked, and all primes before [j] are known not
    to divide [current].  If the product guard is already false, the state is
    strong enough to move to the next outer iteration. *)
Definition EulerInnerState
    (n current j tot : Z) (flags primes : list Z) : Prop :=
  EulerFlagState n current tot flags primes /\
  Zlength primes = n /\
  2 <= current /\ current <= n /\
  1 <= j /\ j <= tot /\
  0 < tot /\ tot <= n /\
  tot < current + 1 /\
  PrimePrefixList current tot primes /\
  PrimeBounds current tot primes /\
  CurrentBaseProgress n current j flags primes /\
  PriorNonDivisibility current j primes /\
  (ProductIndex current j primes > n ->
   EulerOuterState n (current + 1) tot flags primes).

(** State immediately after writing [flag[current * primes[j]]].  The written
    product is a sound least-prime-factor mark.  The state also records the two
    possible exits from the just-tested prime: divisibility breaks to the next
    outer state, while non-divisibility makes the [j + 1] inner state valid. *)
Definition EulerInnerMarkedState
    (n current j tot : Z) (flags primes : list Z) : Prop :=
  EulerInnerState n current j tot flags primes /\
  ProductIndex current j primes <= n /\
  FlagEntryFor (ProductIndex current j primes)
    (Znth (j - 1) primes 0) /\
  FlagValue flags (ProductIndex current j primes) =
    Znth (j - 1) primes 0 /\
  CurrentBaseProgress n current (j + 1) flags primes /\
  (Z.divide (Znth (j - 1) primes 0) current ->
   EulerOuterState n (current + 1) tot flags primes) /\
  (~ Z.divide (Znth (j - 1) primes 0) current ->
   EulerInnerState n current (j + 1) tot flags primes).

Require Import Coq.ZArith.Znumtheory.
Require Import Coq.ZArith.Wf_Z.
