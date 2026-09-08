Require Import PVbench.Algorithms.sieve_of_eratosthenes.rocq.spec_lib.

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.

Import ListNotations.
Local Open Scope Z_scope.

Definition ExactZeroOne (is_zero : Prop) (value : Z) : Prop :=
  (is_zero /\ value = 0) \/ (~ is_zero /\ value = 1).

(** The required final contents of the concrete segment [f[1]..f[n]].
    Logical position [k - 1] represents the program index [k]. *)
Definition SieveInitPrefix (n next : Z) (values : list Z) : Prop :=
  Zlength values = n /\
  forall k : Z,
    1 <= k < next ->
    Znth (k - 1) values 0 = 1.

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
  2 <= factor /\
  2 * factor <= next /\
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
