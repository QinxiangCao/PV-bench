Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import PVbench.Codeforces.examples_shard01.P034_1999E_triple_operations.rocq.spec_lib.

Import ListNotations.
Local Open Scope Z_scope.

(* A prefix form of [TripleTablesBridge], used while the two global tables are
   initialized.  The numeric bounds are conservative C-safety facts; the two
   recurrence clauses carry the mathematical table meaning. *)
Definition TripleTablesPrefix (fvs pres : list Z) (n : Z) : Prop :=
  Zlength fvs = n /\
  Zlength pres = n /\
  1 <= n <= 200005 /\
  Znth 0 fvs 0 = 0 /\
  Znth 0 pres 0 = 0 /\
  (forall i, 0 <= i < n -> 0 <= Znth i fvs 0 <= i) /\
  (forall i, 0 <= i < n -> 0 <= Znth i pres 0 <= 200005 * i) /\
  (forall i, 1 <= i < n ->
     Znth i fvs 0 = Znth (i / 3) fvs 0 + 1) /\
  (forall i, 1 <= i < n ->
     Znth i pres 0 = Znth (i - 1) pres 0 + Znth i fvs 0).

(* The already-written output prefix satisfies the frozen per-query result
   relation. *)
Definition TripleOutputsPrefix
    (ls rs outs : list Z) (n : Z) : Prop :=
  Zlength outs = n /\
  (forall i, 0 <= i < n ->
     Spec (Znth i ls 0) (Znth i rs 0) (Znth i outs 0)).

Definition TripleClosedFormBridge (fvs pres : list Z) : Prop :=
  forall l r,
    1 <= l < r /\ r <= 200000 ->
    Spec l r
      (2 * Znth l fvs 0 + (Znth r pres 0 - Znth l pres 0)).
