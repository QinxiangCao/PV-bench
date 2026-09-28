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

Definition digit_sum_modulus : Z := 1000000007.

Inductive Base10DigitSum : Z -> Z -> Prop :=
| Base10DigitSum_zero : Base10DigitSum 0 0
| Base10DigitSum_positive :
    forall n quotient quotient_sum,
      0 < n ->
      quotient = n / 10 ->
      Base10DigitSum quotient quotient_sum ->
      Base10DigitSum n (quotient_sum + n mod 10).

(** Decimal decomposition is independent of the DP tables and machine bounds. *)
Definition decimal_digit_sum (n : Z) : Z :=
  epsilon (inhabits 0) (Base10DigitSum n).

Definition IntervalDigitSum (lo hi answer : Z) : Prop :=
  answer = sum_range lo hi decimal_digit_sum mod digit_sum_modulus.
