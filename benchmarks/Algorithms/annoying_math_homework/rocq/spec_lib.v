Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import AUXLib.ListLib.

Import ListNotations.
Local Open Scope Z_scope.

Definition digit_sum_modulus : Z := 1000000007.

Inductive Base10DigitSum : Z -> Z -> Prop :=
| Base10DigitSum_zero : Base10DigitSum 0 0
| Base10DigitSum_positive :
    forall n quotient quotient_sum,
      0 < n ->
      quotient = n / 10 ->
      Base10DigitSum quotient quotient_sum ->
      Base10DigitSum n (quotient_sum + n mod 10).

Inductive InclusiveDigitSum (lo : Z) : Z -> Z -> Prop :=
| InclusiveDigitSum_single :
    forall digit_sum,
      Base10DigitSum lo digit_sum ->
      InclusiveDigitSum lo lo digit_sum
| InclusiveDigitSum_extend :
    forall hi total next_digit_sum,
      lo <= hi ->
      InclusiveDigitSum lo hi total ->
      Base10DigitSum (hi + 1) next_digit_sum ->
      InclusiveDigitSum lo (hi + 1) (total + next_digit_sum).

Definition IntervalDigitSum (lo hi answer : Z) : Prop :=
  exists total,
    lo <= hi /\
    InclusiveDigitSum lo hi total /\
    answer = total mod digit_sum_modulus.

Definition PowerTable (power : list Z) : Prop :=
  Zlength power = 20 /\
  forall i, 0 <= i < 20 ->
    Znth i power 0 = (10 ^ i) mod digit_sum_modulus.

Definition DigitDPValue (places leading : Z) : Z :=
  if Z.eq_dec places 1 then leading mod digit_sum_modulus
  else
    (leading * 10 ^ (places - 1) +
     45 * (places - 1) * 10 ^ (places - 2)) mod digit_sum_modulus.

Definition DigitDPTable (dp : list Z) : Prop :=
  Zlength dp = 200 /\
  (forall j, 0 <= j < 10 -> Znth j dp 0 = 0) /\
  forall places leading,
    1 <= places < 20 -> 0 <= leading < 10 ->
    Znth (places * 10 + leading) dp 0 = DigitDPValue places leading.
