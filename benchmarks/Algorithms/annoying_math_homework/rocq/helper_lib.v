Require Import PVbench.Algorithms.annoying_math_homework.rocq.spec_lib.

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import AUXLib.ListLib.

Import ListNotations.
Local Open Scope Z_scope.

Inductive PrefixDigitSum : Z -> Z -> Prop :=
| PrefixDigitSum_nonpositive :
    forall x, x <= 0 -> PrefixDigitSum x 0
| PrefixDigitSum_positive_base :
    PrefixDigitSum 1 1
| PrefixDigitSum_positive_step :
    forall x total next_digit_sum,
      1 <= x ->
      PrefixDigitSum x total ->
      Base10DigitSum (x + 1) next_digit_sum ->
      PrefixDigitSum (x + 1)
        ((total + next_digit_sum) mod digit_sum_modulus).

Definition PowerPrefix (power : list Z) (hi : Z) : Prop :=
  Zlength power = hi /\
  1 <= hi <= 20 /\
  forall i, 0 <= i < hi ->
    Znth i power 0 = (10 ^ i) mod digit_sum_modulus.

Definition ZeroSegment (values : list Z) (hi total : Z) : Prop :=
  Zlength values = hi /\
  0 <= hi <= total /\
  forall k, 0 <= k < hi -> Znth k values 0 = 0.

Definition DigitDPBaseProgress (dp : list Z) (next : Z) : Prop :=
  Zlength dp = 200 /\
  0 <= next <= 10 /\
  (forall j, 0 <= j < next -> Znth (10 + j) dp 0 = j) /\
  (forall k, 0 <= k < 200 ->
     (k < 10 \/ 20 <= k \/ 10 + next <= k) -> Znth k dp 0 = 0).

Definition DigitDPOuterProgress (dp : list Z) (next_places : Z) : Prop :=
  Zlength dp = 200 /\
  2 <= next_places <= 20 /\
  (forall d, 0 <= d < 10 -> Znth d dp 0 = 0) /\
  (forall places leading,
     1 <= places < next_places -> 0 <= leading < 10 ->
     Znth (places * 10 + leading) dp 0 = DigitDPValue places leading) /\
  (forall places leading,
     next_places <= places < 20 -> 0 <= leading < 10 ->
     Znth (places * 10 + leading) dp 0 = 0).

Definition DigitDPRowProgress
    (dp : list Z) (places next_leading : Z) : Prop :=
  Zlength dp = 200 /\
  2 <= places < 20 /\
  0 <= next_leading <= 10 /\
  (forall d, 0 <= d < 10 -> Znth d dp 0 = 0) /\
  (forall p d, 1 <= p < places -> 0 <= d < 10 ->
     Znth (p * 10 + d) dp 0 = DigitDPValue p d) /\
  (forall d, 0 <= d < next_leading ->
     Znth (places * 10 + d) dp 0 = DigitDPValue places d) /\
  (forall d, next_leading <= d < 10 ->
     Znth (places * 10 + d) dp 0 = 0) /\
  forall p d, places < p < 20 -> 0 <= d < 10 ->
    Znth (p * 10 + d) dp 0 = 0.

Inductive InnerCandidateDigitSum
    (dp : list Z) (places : Z) : Z -> Z -> Prop :=
| InnerCandidateDigitSum_zero : InnerCandidateDigitSum dp places 0 0
| InnerCandidateDigitSum_step :
    forall next partial,
      0 <= next ->
      InnerCandidateDigitSum dp places next partial ->
      InnerCandidateDigitSum dp places (next + 1)
        ((partial + Znth (places * 10 + next) dp 0) mod digit_sum_modulus).

Definition DigitDPCellProgress
    (dp : list Z) (places leading next_suffix : Z) : Prop :=
  Zlength dp = 200 /\
  2 <= places < 20 /\
  0 <= leading < 10 /\
  0 <= next_suffix <= 10 /\
  (forall d, 0 <= d < 10 -> Znth d dp 0 = 0) /\
  (forall p d, 1 <= p < places -> 0 <= d < 10 ->
     Znth (p * 10 + d) dp 0 = DigitDPValue p d) /\
  (forall d, 0 <= d < leading ->
     Znth (places * 10 + d) dp 0 = DigitDPValue places d) /\
  (forall d, leading < d < 10 ->
     Znth (places * 10 + d) dp 0 = 0) /\
  (forall p d, places < p < 20 -> 0 <= d < 10 ->
     Znth (p * 10 + d) dp 0 = 0) /\
  exists partial,
    InnerCandidateDigitSum dp (places - 1) next_suffix partial /\
    Znth (places * 10 + leading) dp 0 =
      (partial + next_suffix * (10 ^ (places - 2)) * leading)
        mod digit_sum_modulus.

Definition ExtractedDigitBuffer
    (x : Z) (digits : list Z) (count remaining : Z) : Prop :=
  Zlength digits = 20 /\
  0 <= count <= 19 /\
  remaining = x / 10 ^ count /\
  (forall k, 1 <= k <= count ->
     Znth k digits 0 = (x / 10 ^ (k - 1)) mod 10) /\
  (forall k, count < k < 20 -> Znth k digits 0 = 0).

Definition ExtractedDigitCount (x count : Z) : Prop :=
  1 <= count <= 19 /\
  10 ^ (count - 1) <= x < 10 ^ count.

Definition DigitPositionPower (position power : Z) : Prop :=
  1 <= position <= 19 /\
  power = 10 ^ (position - 1).

Definition OuterDigitPositionPower (position power : Z) : Prop :=
  (position = 0 /\ power = 0) \/
  (1 <= position <= 19 /\ power = 10 ^ (position - 1)).

Definition AccumulatedDigitSumCorrect
    (x position answer : Z) : Prop :=
  (position = 0 /\ PrefixDigitSum x answer) \/
  (1 <= position /\
   exists high high_digit_sum before,
     high = x / 10 ^ position /\
     Base10DigitSum high high_digit_sum /\
     PrefixDigitSum (high - 1) before /\
     answer =
       (10 ^ position * before +
        45 * high * position * 10 ^ (position - 1) +
        (x mod 10 ^ position + 1) * high_digit_sum)
         mod digit_sum_modulus).

Inductive DigitPositionAccumulation
    (x : Z) (dp digits : list Z) : Z -> Z -> Prop :=
| DigitPositionAccumulation_start :
    forall count,
      ExtractedDigitBuffer x digits count 0 ->
      ExtractedDigitCount x count ->
      DigitPositionAccumulation x dp digits count 0
| DigitPositionAccumulation_step :
    forall places answer choice_sum,
      1 <= places ->
      DigitPositionAccumulation x dp digits places answer ->
      InnerCandidateDigitSum dp places (Znth places digits 0) choice_sum ->
      DigitPositionAccumulation x dp digits (places - 1)
        ((answer + choice_sum +
          (((x mod 10 ^ (places - 1)) + 1) mod digit_sum_modulus) *
            Znth places digits 0) mod digit_sum_modulus).

Definition OuterDigitPositionProgress
    (x : Z) (dp digits : list Z) (position answer : Z) : Prop :=
  DigitPositionAccumulation x dp digits position answer.

Definition InnerCandidateDigitProgress
    (x : Z) (dp digits : list Z) (places next_digit answer_before answer : Z) : Prop :=
  1 <= places <= 19 /\
  0 <= next_digit <= Znth places digits 0 /\
  OuterDigitPositionProgress x dp digits places answer_before /\
  exists choice_sum,
    InnerCandidateDigitSum dp places next_digit choice_sum /\
    answer = (answer_before + choice_sum) mod digit_sum_modulus.

