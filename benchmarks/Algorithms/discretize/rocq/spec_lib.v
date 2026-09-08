Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Definition strict_increasing_prefix (l : list Z) (len : Z) : Prop :=
  0 <= len <= Zlength l /\
  forall i j,
    0 <= i < j ->
    j < len ->
    Znth i l 0 < Znth j l 0.
Definition same_values_prefix
    (out : list Z) (out_len : Z) (src : list Z) (src_len : Z) : Prop :=
  forall x,
    In x (sublist 0 out_len out) <-> In x (sublist 0 src_len src).
Definition discretize_result
    (src : list Z) (n : Z) (out : list Z) (ret : Z) : Prop :=
  Zlength src = n /\
  Zlength out = n /\
  1 <= n /\
  1 <= ret <= n /\
  strict_increasing_prefix out ret /\
  same_values_prefix out ret src n /\
  (forall i,
      0 <= i < n ->
      exists r,
        0 <= r < ret /\ Znth r out 0 = Znth i src 0) /\
  (forall r,
      0 <= r < ret ->
      exists i,
        0 <= i < n /\ Znth r out 0 = Znth i src 0) /\
  (forall i j ri rj,
      0 <= i < n ->
      0 <= j < n ->
      0 <= ri < ret ->
      0 <= rj < ret ->
      Znth ri out 0 = Znth i src 0 ->
      Znth rj out 0 = Znth j src 0 ->
      (Znth i src 0 = Znth j src 0 -> ri = rj) /\
      (Znth i src 0 < Znth j src 0 -> ri < rj)).
