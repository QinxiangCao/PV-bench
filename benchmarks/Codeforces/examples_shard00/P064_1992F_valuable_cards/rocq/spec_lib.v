Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition BadCardSegment (x : Z) (seg : list Z) : Prop :=
  forall ids : Z -> Prop,
    fold_right Z.mul 1
      (map (fun i => Znth i seg 0)
        (@enum Z (fun i => 0 <= i < Zlength seg /\ ids i) _)) <> x.

Definition BadPartition (x : Z) (a cuts : list Z) : Prop :=
  2 <= Zlength cuts /\ Znth 0 cuts 0 = 0 /\
  Znth (Zlength cuts - 1) cuts 0 = Zlength a /\
  mono_inc cuts /\
  forall i, 0 <= i < Zlength cuts - 1 ->
    BadCardSegment x (sublist (Znth i cuts 0) (Znth (i + 1) cuts 0) a).

Definition Pre (x : Z) (a : list Z) : Prop :=
  2 <= x <= 100000 /\ 1 <= Zlength a <= 100000 /\
  Forall (fun v => 1 <= v <= 200000 /\ v <> x) a.

Definition Spec (x : Z) (a : list Z) (out : Z) : Prop :=
  min_value_of_subset Z.le (BadPartition x a)
    (fun cuts => Zlength cuts - 1) out.

Require Import Coq.micromega.Lia.

Require Import Coq.ZArith.Zquot.

Require Import Coq.micromega.Psatz.

Require Import Coq.Sorting.Permutation.

Require Import Coq.Logic.Classical_Prop.
