Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition ValidFactorSequence (n : Z) (a : list Z) : Prop :=
  0 < Zlength a /\ Forall (fun x => x > 1) a /\
  fold_right Z.mul 1 a = n /\
  forall i, 0 <= i < Zlength a - 1 -> (Znth i a 0 | Znth (i + 1) a 0).

Definition Pre (n : Z) : Prop := 2 <= n <= 10000000000.

Definition Spec (n : Z) (out : list Z) : Prop :=
  ValidFactorSequence n out /\
  max_value_of_subset Z.le (ValidFactorSequence n)
    (fun candidate => Zlength candidate) (Zlength out).



Import ListNotations.
