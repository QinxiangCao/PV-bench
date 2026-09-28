Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition DivisionDifference (n : Z) (left : Z -> Prop) (d : Z) : Prop :=
  d = Z.abs
        (sum (fun x : Z => 1 <= x < n + 1 /\ left x) (fun x => x) -
         sum (fun x : Z => 1 <= x < n + 1 /\ ~ left x) (fun x => x)).

Definition Pre (n : Z) : Prop :=
  1 <= n <= 2000000000.

Definition Spec (n out : Z) : Prop :=
  min_value_of_subset Z.le
    (fun candidate : (Z -> Prop) * Z =>
      DivisionDifference n (fst candidate) (snd candidate))
    snd out.

Require Import Coq.micromega.Lia.
