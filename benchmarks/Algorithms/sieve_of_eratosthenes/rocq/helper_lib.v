Require Export PVbench.Algorithms.sieve_of_eratosthenes.rocq.spec_lib.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Require Import AUXLib.MonotonicList.
Import ListNotations.
Local Open Scope Z_scope.

(** [HasProperDivisorBelow bound k] says that [k] has a nontrivial positive
    divisor strictly below both [bound] and [k]. *)
Definition HasProperDivisorBelow (bound k : Z) : Prop :=
  exists d : Z,
    2 <= d /\
    d < bound /\
    d < k /\
    Z.divide d k.

(** Exact, two-sided 0/1 interpretation of a mathematical proposition. *)
Definition ExactZeroOne (is_zero : Prop) (value : Z) : Prop :=
  (is_zero /\ value = 0) \/ (~ is_zero /\ value = 1).

(** State of the first initialization loop: all program-owned indices before
    [next] have already been written to one. *)
Definition SieveInitPrefix (n next : Z) (values : list Z) : Prop :=
  Zlength values = n /\
  Forall (fun value => value = 1) (sublist 0 (next - 1) values).

(** At outer-loop bound [bound], an index greater than one is zero exactly
    when it already has a proper divisor below [bound].  Index one is always
    zero. *)
Definition SieveStage (n bound : Z) (values : list Z) : Prop :=
  Zlength values = n /\
  forall k : Z,
    1 <= k <= n ->
    ((k = 1 /\ Znth (k - 1) values 0 = 0) \/
     (2 <= k /\
      ExactZeroOne
        (HasProperDivisorBelow bound k)
        (Znth (k - 1) values 0))).

(** Multiples of [factor] strictly before [next] that the inner loop has
    processed.  Starting at [2 * factor] excludes the factor itself. *)
Definition ProcessedMultiple (factor next k : Z) : Prop :=
  2 * factor <= k /\
  k < next /\
  Z.divide factor k.

(** Inner-loop state: the exact zero set consists of entries eliminated by a
    smaller proper divisor, plus the multiples processed in this inner loop. *)
Definition SieveMarkState
    (n factor next : Z) (values : list Z) : Prop :=
  Z.divide factor next /\
  Zlength values = n /\
  forall k : Z,
    1 <= k <= n ->
    ((k = 1 /\ Znth (k - 1) values 0 = 0) \/
     (2 <= k /\
      ExactZeroOne
        (HasProperDivisorBelow factor k \/
         ProcessedMultiple factor next k)
        (Znth (k - 1) values 0))).
