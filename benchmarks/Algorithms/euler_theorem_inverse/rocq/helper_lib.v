Require Export PVbench.Algorithms.euler_theorem_inverse.rocq.spec_lib.
From Coq Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.

Require Import
  PVbench.Algorithms.modular_power.rocq.spec_lib.

(** The canonical Euler totient is the cardinality of the positive residues
    [1, n] that are coprime to [n].  This finite count is independent of the
    trial-division implementation used by the C program. *)
Require Import AUXLib.ListLib SumLib.ZRange.

Definition EulerTotientValue (n : Z) : Z :=
  Zlength (filter (fun k : Z => Z.eqb (Z.gcd k n) 1) (Zrange 1 (n + 1))).

From Coq Require Import Lia Sorting.Permutation.

Definition EulerPhi (n result : Z) : Prop :=
  result = EulerTotientValue n.

(** The residual state isolates the mathematical work still carried by the
    unprocessed factor [remaining].  Besides the totient identity, divisibility
    records the accumulator's reachable factorization shape: every unprocessed
    factor still present in [remaining] is also present in [result]. *)
Definition EulerPhiResidual
    (original remaining result : Z) : Prop :=
  Z.divide remaining result /\
  forall original_phi remaining_phi,
    EulerPhi original original_phi ->
    EulerPhi remaining remaining_phi ->
    original_phi * remaining = result * remaining_phi.

(** Mathematical primality, stated without extending the spec-stage import
    surface. *)
Definition EulerPrime (p : Z) : Prop :=
  1 < p /\
  forall d,
    0 < d ->
    Z.divide d p ->
    d = 1 \/ d = p.

(** No prime below the trial-division frontier remains in the residual. *)
Definition NoPrimeDivisorBelow (frontier remaining : Z) : Prop :=
  forall p,
    EulerPrime p ->
    p < frontier ->
    ~ Z.divide p remaining.

(** Stable mathematical meaning of the outer factor scan.  The residual state
    carries both reachability/divisibility and totient semantics; runtime
    ranges and multiplication safety deliberately remain in the C invariant. *)
Definition EulerPhiProgress
    (original frontier remaining result : Z) : Prop :=
  EulerPhiResidual original remaining result /\
  NoPrimeDivisorBelow frontier remaining.

(** Semantic completion interface for one prime-removal phase.  It quantifies
    every factor-free terminal reachable from [current] by removing a
    nonnegative power of [factor].  This descendant-closed formulation is
    preserved by exact division and supplies the canonical totient transition
    at loop exit. *)
Definition EulerPhiFactorCompletion
    (original factor current result : Z) : Prop :=
  forall terminal removed,
    0 <= removed ->
    current = terminal * factor ^ removed ->
    terminal mod factor <> 0 ->
    EulerPhiResidual original terminal
      ((result / factor) * (factor - 1)).

(** Proof-only arithmetic support for the structural transport lemmas below. *)
Require Import Coq.micromega.Lia.
Require Import Coq.setoid_ring.Ring.

(** While one distinct prime factor is being removed, [before] records the
    outer residual and [removed] records only the mathematical multiplicity
    already stripped from it.  The completion component makes the canonical
    prime-power totient effect explicit rather than asking the exit proof to
    reconstruct a semantic relation absent from the invariant. *)
Definition EulerPhiRemovalProgress
    (original factor current result : Z) : Prop :=
  exists before removed,
    0 <= removed /\
    before = current * factor ^ removed /\
    Z.divide factor before /\
    Z.divide factor result /\
    EulerPhiProgress original factor before result /\
    EulerPhiFactorCompletion original factor current result.

(** Stable square-and-multiply state for this case's local helper. *)
Definition EulerModularPowerProgress
    (original_base original_exponent modulus
     current_base remaining_exponent accumulator : Z) : Prop :=
  (accumulator * current_base ^ remaining_exponent) mod modulus =
  (original_base ^ original_exponent) mod modulus.

(** Forward the dependency's public relation to generated clients while
    preserving the frozen [Require Import] dependency row. *)
Notation ModularPower :=
  PVbench.Algorithms.modular_power.rocq.spec_lib.ModularPower
  (only parsing).

From Coq Require Import Lia Psatz ZArith.Znumtheory ZArith.Zpow_facts
  Sorting.Permutation.
From Coq Require Import Lia Psatz ZArith.Znumtheory ZArith.Zquot.
From Coq Require Import ZArith.Znumtheory Sorting.Permutation.
