Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition Pre (n : Z) (years : list Z) (a b : Z) : Prop :=
  2 <= n <= 100 /\
  Zlength years = n - 1 /\
  Forall (fun d => 1 <= d <= 100) years /\
  1 <= a < b /\ b <= n.

Definition Spec (n : Z) (years : list Z) (a b out : Z) : Prop :=
  out = fold_right Z.add 0 (sublist (a - 1) (b - 1) years).
