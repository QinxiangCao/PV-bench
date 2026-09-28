Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import Coq.Sorting.Permutation.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

From SimpleC.SL Require Import Mem SeparationLogic ArrayLib Array2Lib.

Local Open Scope Z_scope.

Import naive_C_Rules.

Local Open Scope sac.

Definition Inversions (a : list Z) (x count : Z) : Prop :=
  count = #(fun p : Z * Z =>
    (0 <= fst p < Zlength a /\ 0 <= snd p < Zlength a) /\
    fst p < snd p /\
    Z.lxor (Znth (fst p) a 0) x > Z.lxor (Znth (snd p) a 0) x).

Definition Pre (a : list Z) : Prop :=
  1 <= Zlength a <= 300000 /\
  Forall (fun x => 0 <= x <= 1000000000) a.

Definition Spec (a : list Z) (out : Z * Z) : Prop :=
  min_value_of_subset
    (fun left right : Z * Z =>
      fst left < fst right \/
      fst left = fst right /\ snd left <= snd right)
    (fun candidate : Z * Z =>
      0 <= snd candidate /\ Inversions a (snd candidate) (fst candidate))
    (fun candidate => candidate) out.

Require Import Coq.micromega.Lia.

Require Import Coq.Logic.FunctionalExtensionality.

Require Import Coq.micromega.Psatz.

Require Import Coq.setoid_ring.Ring.
