Require Export PVbench.Algorithms.annoying_math_homework.rocq.spec_lib.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Require Import AUXLib.ListLib.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Import ListNotations.
Local Open Scope Z_scope.
Import naive_C_Rules.
Local Open Scope sac.

(** Inclusive sums use the shared finite-range sum. Empty ranges sum to zero. *)
Definition PrefixDigitSum (x answer : Z) : Prop :=
  answer = sum_range 1 x decimal_digit_sum mod digit_sum_modulus.

Definition PowerTable (power : list Z) : Prop :=
  forall i, 0 <= i < 20 ->
    Znth i power 0 = (10 ^ i) mod digit_sum_modulus.

Definition PowerPrefix (power : list Z) (hi : Z) : Prop :=
  forall i, 0 <= i < hi ->
    Znth i power 0 = (10 ^ i) mod digit_sum_modulus.

Definition DigitDPValue (places leading : Z) : Z :=
  if Z.eq_dec places 1 then leading mod digit_sum_modulus
  else
    (leading * 10 ^ (places - 1) +
     45 * (places - 1) * 10 ^ (places - 2)) mod digit_sum_modulus.

Definition DigitDPTable (dp : list Z) : Prop :=
  (Forall (eq 0) (sublist 0 10 dp)) /\
  forall places leading,
    1 <= places < 20 -> 0 <= leading < 10 ->
    Znth (places * 10 + leading) dp 0 = DigitDPValue places leading.

Definition DigitDPBaseProgress (dp : list Z) (next : Z) : Prop :=
  (forall j, 0 <= j < next -> Znth (10 + j) dp 0 = j) /\
  Forall (eq 0) (sublist 0 10 dp ++ sublist (10 + next) 200 dp).

Definition DigitDPOuterProgress (dp : list Z) (next_places : Z) : Prop :=
  (Forall (eq 0) (sublist 0 10 dp)) /\
  (forall places leading,
     1 <= places < next_places -> 0 <= leading < 10 ->
     Znth (places * 10 + leading) dp 0 = DigitDPValue places leading) /\
  Forall (eq 0) (sublist (next_places * 10) 200 dp).

Definition DigitDPRowProgress
    (dp : list Z) (places next_leading : Z) : Prop :=
  (Forall (eq 0) (sublist 0 10 dp)) /\
  (forall p d, 1 <= p < places -> 0 <= d < 10 ->
     Znth (p * 10 + d) dp 0 = DigitDPValue p d) /\
  (forall d, 0 <= d < next_leading ->
     Znth (places * 10 + d) dp 0 = DigitDPValue places d) /\
  Forall (eq 0) (sublist (places * 10 + next_leading) ((places + 1) * 10) dp) /\
  Forall (eq 0) (sublist ((places + 1) * 10) 200 dp).

Definition InnerCandidateDigitSum
    (dp : list Z) (places count partial : Z) : Prop :=
  partial = sum_range 0 (count - 1)
    (fun digit => Znth (places * 10 + digit) dp 0) mod digit_sum_modulus.

Definition DigitDPCellProgress
    (dp : list Z) (places leading next_suffix : Z) : Prop :=
  (Forall (eq 0) (sublist 0 10 dp)) /\
  (forall p d, 1 <= p < places -> 0 <= d < 10 ->
     Znth (p * 10 + d) dp 0 = DigitDPValue p d) /\
  (forall d, 0 <= d < leading ->
     Znth (places * 10 + d) dp 0 = DigitDPValue places d) /\
  Forall (eq 0) (sublist (places * 10 + leading + 1) ((places + 1) * 10) dp) /\
  Forall (eq 0) (sublist ((places + 1) * 10) 200 dp) /\
  exists partial,
    InnerCandidateDigitSum dp (places - 1) next_suffix partial /\
    Znth (places * 10 + leading) dp 0 =
      (partial + next_suffix * (10 ^ (places - 2)) * leading)
        mod digit_sum_modulus.

Definition ExtractedDigitBuffer
    (x : Z) (digits : list Z) (count remaining : Z) : Prop :=
  remaining = x / 10 ^ count /\
  (forall k, 1 <= k <= count ->
     Znth k digits 0 = (x / 10 ^ (k - 1)) mod 10) /\
  Forall (eq 0) (sublist (count + 1) 20 digits).

Definition ExtractedDigitCount (x count : Z) : Prop :=
  10 ^ (count - 1) <= x < 10 ^ count.

Definition DigitPositionPower (position power : Z) : Prop :=
  power = 10 ^ (position - 1).

Definition OuterDigitPositionPower (position power : Z) : Prop :=
  (position = 0 /\ power = 0) \/
  (1 <= position /\ power = 10 ^ (position - 1)).

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

Definition InnerCandidateDigitProgress
    (dp : list Z) (places next_digit answer_before answer : Z) : Prop :=
  exists choice_sum,
    InnerCandidateDigitSum dp places next_digit choice_sum /\
    answer = (answer_before + choice_sum) mod digit_sum_modulus.
