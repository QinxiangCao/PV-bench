Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import Coq.Sorting.Permutation.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition GoodWindow (b window : list Z) (k : Z) : Prop :=
  exists rearranged,
    Permutation window rearranged /\ Zlength rearranged = Zlength b /\
    #(fun i : Z => 0 <= i < Zlength b /\
      Znth i rearranged 0 = Znth i b 0) >= k.

Definition Pre (k : Z) (a b : list Z) : Prop :=
  1 <= k <= Zlength b /\ Zlength b <= Zlength a /\ Zlength a <= 200000 /\
  Forall (fun x => 1 <= x <= 1000000) a /\ Forall (fun x => 1 <= x <= 1000000) b.

Definition Spec (k : Z) (a b : list Z) (out : Z) : Prop :=
  out = #(fun l : Z =>
    0 <= l < Zlength a - Zlength b + 1 /\
    GoodWindow b (sublist l (l + Zlength b) a) k).
