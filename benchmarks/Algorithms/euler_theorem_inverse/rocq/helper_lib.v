Require Import PVbench.Algorithms.euler_theorem_inverse.rocq.spec_lib.

From Coq Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.

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
Definition EulerPhiRemovalProgress
    (original factor current result : Z) : Prop :=
  exists before removed,
    0 <= removed /\
    before = current * factor ^ removed /\
    Z.divide factor before /\
    Z.divide factor result /\
    EulerPhiProgress original factor before result /\
    EulerPhiFactorCompletion original factor current result.

(** The factor-completion phase consumes the invariant's semantic interface by
    choosing the current value itself with exponent zero. *)
Definition EulerModularPowerProgress
    (original_base original_exponent modulus
     current_base remaining_exponent accumulator : Z) : Prop :=
  (accumulator * current_base ^ remaining_exponent) mod modulus =
  (original_base ^ original_exponent) mod modulus.
