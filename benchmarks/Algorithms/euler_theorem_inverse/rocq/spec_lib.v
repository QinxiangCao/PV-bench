From Coq Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.

Definition ModularPower
    (base exponent modulus result : Z) : Prop :=
  result = (base ^ exponent) mod modulus.

Definition EulerTotientValue (n : Z) : Z :=
  Z.of_nat
    (length
       (filter
          (fun k : nat => Z.eqb (Z.gcd (Z.of_nat k) n) 1)
          (seq 1 (Z.to_nat n)))).
Definition EulerPhi (n result : Z) : Prop :=
  result = EulerTotientValue n.

(** The public inverse result is the canonical modular-power value obtained
    from Euler's totient, and it satisfies the modular inverse equation. *)
Definition EulerTheoremInverse
    (value modulus inverse : Z) : Prop :=
  exists phi,
    EulerPhi modulus phi /\
    ModularPower value (phi - 1) modulus inverse /\
    (value * inverse) mod modulus = 1.

(** The residual state isolates the mathematical work still carried by the
    unprocessed factor [remaining].  Besides the totient identity, divisibility
    records the accumulator's reachable factorization shape: every unprocessed
    factor still present in [remaining] is also present in [result]. *)
