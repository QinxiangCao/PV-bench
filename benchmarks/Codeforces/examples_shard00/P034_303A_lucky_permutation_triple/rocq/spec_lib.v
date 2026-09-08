Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import Coq.Sorting.Permutation.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition LuckyTriple (n : Z) (triple : list Z * list Z * list Z) : Prop :=
  let '(a, b, c) := triple in
  Permutation a (Zrange 0 n) /\ Permutation b (Zrange 0 n) /\
  Permutation c (Zrange 0 n) /\
  forall i, 0 <= i < n -> (Znth i a 0 + Znth i b 0) mod n = Znth i c 0.

Definition Pre (n : Z) : Prop := 1 <= n <= 100000.

Definition Spec (n : Z) (out : option (list Z * list Z * list Z)) : Prop :=
  (exists triple, out = Some triple /\ LuckyTriple n triple) \/
  (out = None /\ forall triple, ~ LuckyTriple n triple).
