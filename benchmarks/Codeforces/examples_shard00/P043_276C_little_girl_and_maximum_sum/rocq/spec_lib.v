Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import Coq.Sorting.Permutation.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition QueryReplyTotal (arr : list Z) (queries : list (Z*Z)) : Z :=
  fold_right Z.add 0 (map (fun q => fold_right Z.add 0
    (sublist (fst q) (snd q + 1) arr)) queries).

Definition Pre (a : list Z) (queries : list (Z*Z)) : Prop :=
  1 <= Zlength a <= 200000 /\ 1 <= Zlength queries <= 200000 /\
  Forall (fun x => 1 <= x <= 200000) a /\
  Forall (fun q => 0 <= fst q <= snd q /\ snd q < Zlength a) queries.

Definition Spec (a : list Z) (queries : list (Z*Z)) (out : Z) : Prop :=
  max_value_of_subset Z.le (fun arranged => Permutation a arranged)
    (fun arranged => QueryReplyTotal arranged queries) out.
