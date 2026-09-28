Require Export PVbench.Algorithms.choosing_inns.rocq.spec_lib.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
From SumLib Require Import ZRange.

Definition InnsColorCount (colors : list Z) (limit color : Z) : Z :=
  Zlength (filter (fun idx => Z.eqb (Znth idx colors 0) color) (Zrange 0 limit)).

Definition InnsGoodColorCount (colors costs : list Z) (limit p color : Z) : Z :=
  Zlength (filter (fun idx => Z.eqb (Znth idx colors 0) color &&
    InnsAffordable costs p idx (limit - 1)) (Zrange 0 limit)).

Definition InnsPrefixCounts (colors costs : list Z) (limit k p answer : Z)
  (seen good : list Z) : Prop :=
  answer = InnsPairCount colors costs p limit /\
  (forall color, 0 <= color < k -> Znth color seen 0 = InnsColorCount colors limit color) /\
  (forall color, 0 <= color < k -> Znth color good 0 = InnsGoodColorCount colors costs limit p color).

Definition InnsCopiedPrefix (src old dst : list Z) (written k : Z) : Prop :=
  Forall2 eq (sublist 0 written dst) (sublist 0 written src) /\
  Forall2 eq (sublist written k dst) (sublist written k old).
