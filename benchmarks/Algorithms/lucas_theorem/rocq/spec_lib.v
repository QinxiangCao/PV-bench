From Coq Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.

Definition ModularPower
    (base exponent modulus result : Z) : Prop :=
  result = (base ^ exponent) mod modulus.

(** A positive integer is prime when it has no nontrivial divisor.  This
    case-local formulation keeps the public annotation surface independent of
    proof-only number-theory imports. *)
Definition PrimeForLucas (p : Z) : Prop :=
  2 <= p /\
  forall divisor,
    2 <= divisor < p ->
    p mod divisor <> 0.

(** A Pascal-recursive mathematical binomial coefficient.  This is a
    property-level object independent of the multiplicative C helper. *)
Fixpoint LucasNatBinomial (upper lower : nat) : nat :=
  match upper, lower with
  | _, O => 1%nat
  | O, S _ => 0%nat
  | S upper', S lower' =>
      (LucasNatBinomial upper' lower' +
       LucasNatBinomial upper' (S lower'))%nat
  end.
Definition LucasBinomialCoefficient (upper lower : Z) : Z :=
  Z.of_nat
    (LucasNatBinomial (Z.to_nat upper) (Z.to_nat lower)).
Definition LucasBinomialResidue
    (n m p result : Z) : Prop :=
  result = LucasBinomialCoefficient (n + m) n mod p.

(** The helper replaces [lower] by its symmetric, smaller choice before the
    multiplicative loop. *)
Definition DigitEffectiveLower (upper lower : Z) : Z :=
  Z.min lower (upper - lower).

(** A finite mathematical product of [count] consecutive integers beginning
    at [start]. *)
Definition LucasRangeProduct (start count : Z) : Z :=
  fold_right Z.mul 1
    (map (fun offset => start + Z.of_nat offset)
      (seq 0 (Z.to_nat count))).
Definition DigitNumeratorPrefix
    (upper lower processed : Z) : Z :=
  LucasRangeProduct (upper - lower + 1) processed.
Definition DigitDenominatorPrefix (processed : Z) : Z :=
  LucasRangeProduct 1 processed.

(** The precise signed-int safety promise for the digit helper.  It talks
    about mathematical prefix residues rather than simulating C state. *)
Definition DigitBinomialMachineSafe
    (upper original_lower p : Z) : Prop :=
  let lower := DigitEffectiveLower upper original_lower in
  (forall next,
      1 <= next <= lower ->
      0 <=
        (DigitNumeratorPrefix upper lower (next - 1) mod p) *
        (upper - lower + next) <= 2147483647 /\
      0 <=
        (DigitDenominatorPrefix (next - 1) mod p) * next <=
        2147483647) /\
  (forall inverse,
      ModularPower
        (DigitDenominatorPrefix lower mod p) (p - 2) p inverse ->
      0 <=
        (DigitNumeratorPrefix upper lower lower mod p) * inverse <=
        2147483647).

(** The digit at [position] in a nonnegative integer's base-[p]
    representation. *)
Definition LucasDigit (value p : Z) (position : nat) : Z :=
  (value / p ^ Z.of_nat position) mod p.

(** Product, modulo [p], of the first [digits] Lucas digit coefficients. *)
Definition LucasPrefixProduct
    (upper lower p : Z) (digits : nat) : Z :=
  fold_right Z.mul 1
    (map
      (fun position =>
        LucasBinomialCoefficient
          (LucasDigit upper p position)
          (LucasDigit lower p position) mod p)
      (seq 0 digits)) mod p.

(** The input-specific machine-safety promise for every digit that the main
    loop can process. *)
Definition LucasMachineSafe (n m p : Z) : Prop :=
  forall processed : nat,
    let upper_digit := LucasDigit (n + m) p processed in
    let lower_digit := LucasDigit n p processed in
    lower_digit <= upper_digit ->
    DigitBinomialMachineSafe upper_digit lower_digit p /\
    0 <=
      LucasPrefixProduct (n + m) n p processed *
      (LucasBinomialCoefficient upper_digit lower_digit mod p) <=
      2147483647.

(** Internal mathematical state for the multiplicative digit helper. *)
