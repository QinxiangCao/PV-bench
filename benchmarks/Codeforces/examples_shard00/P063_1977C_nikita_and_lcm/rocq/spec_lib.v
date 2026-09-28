Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition CommonMultipleOfChosen (a : list Z) (indices : Z -> Prop) (x : Z) : Prop :=
  forall i, indices i -> (Znth i a 0 | x).

Definition LeastCommonOfChosen (a : list Z) (indices : Z -> Prop) (x : Z) : Prop :=
  min_value_of_subset (fun left right : Z => (left | right))
    (fun candidate : Z =>
      1 <= candidate /\ CommonMultipleOfChosen a indices candidate)
    (fun candidate => candidate) x.

Definition SpecialChoice (a : list Z) (indices : Z -> Prop) : Prop :=
  (forall i, indices i -> 0 <= i < Zlength a) /\
  exists x, LeastCommonOfChosen a indices x /\ ~ In x a.

Definition Pre (a : list Z) : Prop :=
  1 <= Zlength a <= 2000 /\
  Forall (fun x => 1 <= x <= 1000000000) a.

Definition Spec (a : list Z) (out : Z) : Prop :=
  max_value_of_subset_with_default Z.le
    (fun candidate : (Z -> Prop) * Z =>
      SpecialChoice a (fst candidate) /\
      snd candidate = #(fun i : Z => 0 <= i < Zlength a /\ fst candidate i))
    snd 0 out.

Require Import Coq.Sorting.Permutation.

Require Import Coq.micromega.Lia.

Require Import Coq.micromega.Psatz.

Require Import Coq.ZArith.Zquot.
