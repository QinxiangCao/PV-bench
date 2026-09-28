Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition SimplifiedExams (a : list Z) (k : Z) (result : list Z) : Prop :=
  exists chosen : Z -> Prop,
    (forall i, chosen i -> 0 <= i < Zlength a) /\
    #(fun i : Z => 0 <= i < Zlength a /\ chosen i) <= k /\
    Zlength result = Zlength a /\
    forall i, 0 <= i < Zlength a ->
      Znth i result 0 = if prop_dec (chosen i) then 0 else Znth i a 0.

Definition ExamSadness (a : list Z) (sadness : Z) : Prop :=
  sadness = #(fun i : Z =>
    0 <= i < Zlength a - 1 /\
    Z.gcd (Znth i a 0) (Znth (i+1) a 0) = 1).

Definition Pre (k : Z) (a : list Z) : Prop :=
  1 <= k <= Zlength a /\ Zlength a <= 100000 /\
  Forall (fun x => 0 <= x <= 1000000000) a.

Definition Spec (k : Z) (a : list Z) (out : Z) : Prop :=
  min_value_of_subset Z.le
    (fun candidate : list Z * Z =>
      SimplifiedExams a k (fst candidate) /\
      ExamSadness (fst candidate) (snd candidate)) snd out.

Require Import Coq.Sorting.Permutation.

Import ListNotations.

Require Import Coq.micromega.Lia.

Require Import Coq.ZArith.Zquot.
