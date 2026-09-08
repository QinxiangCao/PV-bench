Require Import Coq.ZArith.ZArith.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition Manhattan (p q : Z * Z) : Z :=
  Z.abs (fst p - fst q) + Z.abs (snd p - snd q).

Definition RoundTripThroughTwo (start p q : Z * Z) : Z :=
  Manhattan start p + Manhattan p q + Manhattan q start.

Definition InRoom (n m : Z) (p : Z * Z) : Prop :=
  1 <= fst p <= n /\ 1 <= snd p <= m.

Definition Pre (n m : Z) (start : Z * Z) : Prop :=
  1 <= n <= 1000000000 /\
  1 <= m <= 1000000000 /\
  InRoom n m start.

Definition Spec (n m : Z) (start p q : Z * Z) : Prop :=
  max_value_of_subset Z.le
    (fun candidate : (Z * Z) * (Z * Z) =>
      InRoom n m (fst candidate) /\ InRoom n m (snd candidate))
    (fun candidate =>
      RoundTripThroughTwo start (fst candidate) (snd candidate))
    (RoundTripThroughTwo start p q) /\
  InRoom n m p /\ InRoom n m q.
