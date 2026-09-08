Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition DecimalValue (digits : list Z) : Z :=
  fold_left (fun value digit => 10 * value + digit) digits 0.

Definition BadUglyDigits (n : Z) (digits : list Z) : Prop :=
  Zlength digits = n /\
  Forall (fun d => 1 <= d <= 9) digits /\
  DecimalValue digits > 0 /\
  Forall (fun d => ~ (d | DecimalValue digits)) digits.

Definition Pre (n : Z) : Prop :=
  1 <= n <= 100000.

Definition Spec (n : Z) (out : option (list Z)) : Prop :=
  (exists digits, out = Some digits /\ BadUglyDigits n digits) \/
  (out = None /\ forall digits, ~ BadUglyDigits n digits).
