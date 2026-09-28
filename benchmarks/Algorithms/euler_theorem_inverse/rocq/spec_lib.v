From Coq Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.

Require Import
  PVbench.Algorithms.modular_power.rocq.spec_lib.

(** The canonical Euler totient is the cardinality of the positive residues
    [1, n] that are coprime to [n].  This finite count is independent of the
    trial-division implementation used by the C program. *)
Require Import AUXLib.ListLib SumLib.ZRange.

From Coq Require Import Lia Sorting.Permutation.

(** The public result states the inverse equation, independently of the
    totient computation and modular exponentiation used to obtain it. *)
Definition EulerTheoremInverse
    (value modulus inverse : Z) : Prop :=
  (value * inverse) mod modulus = 1.

(** Proof-only arithmetic support for the structural transport lemmas below. *)
Require Import Coq.micromega.Lia.
Require Import Coq.setoid_ring.Ring.

From Coq Require Import Lia Psatz ZArith.Znumtheory ZArith.Zpow_facts
  Sorting.Permutation.
From Coq Require Import Lia Psatz ZArith.Znumtheory ZArith.Zquot.
From Coq Require Import ZArith.Znumtheory Sorting.Permutation.
