Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition TwoGroupValue (a : list Z) (first : Z -> Prop) (value : Z) : Prop :=
  value =
    Z.abs (sum (fun i : Z => 0 <= i < Zlength a /\ first i)
               (fun i => Znth i a 0)) -
    Z.abs (sum (fun i : Z => 0 <= i < Zlength a /\ ~ first i)
               (fun i => Znth i a 0)).

Definition Pre (a : list Z) : Prop :=
  1 <= Zlength a <= 100000 /\
  Forall (fun x => -1000000000 <= x <= 1000000000) a.

Definition Spec (a : list Z) (out : Z) : Prop :=
  max_value_of_subset Z.le
    (fun candidate : (Z -> Prop) * Z =>
      TwoGroupValue a (fst candidate) (snd candidate))
    snd out.
