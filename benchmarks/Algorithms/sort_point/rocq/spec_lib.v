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

Definition point : Type := (Z * Z)%type.
Definition mk_point (x y : Z) : point := (x, y).
Definition point_x (p : point) : Z := fst p.
Definition point_y (p : point) : Z := snd p.
Definition default_point : point := mk_point 0 0.
Definition CoordInBounds (z : Z) : Prop := -10000 <= z <= 10000.
Definition PointCoordsBound (l : list point) : Prop :=
  Forall (fun p => CoordInBounds (point_x p) /\ CoordInBounds (point_y p)) l.
Fixpoint flat_points_rec (flat : list Z) (pts : list point) : Prop :=
  match pts with
  | nil => flat = nil
  | p :: rest =>
      exists flat_rest,
        flat = point_x p :: point_y p :: flat_rest /\
        flat_points_rec flat_rest rest
  end.
Definition FlatPoints (flat : list Z) (pts : list point) : Prop :=
  Zlength flat = 2 * Zlength pts /\ flat_points_rec flat pts.
Definition PointPermutation : list point -> list point -> Prop := @Permutation point.
Definition polar_cross (gp a b : point) : Z :=
  (point_x a - point_x gp) * (point_y b - point_y gp) -
  (point_y a - point_y gp) * (point_x b - point_x gp).
Definition point_dist2 (gp a : point) : Z :=
  (point_x gp - point_x a) * (point_x gp - point_x a) +
  (point_y gp - point_y a) * (point_y gp - point_y a).
Definition polar_upper_half (gp a : point) : bool :=
  let dx := point_x a - point_x gp in
  let dy := point_y a - point_y gp in
  orb (Z.ltb 0 dy) (andb (Z.eqb dy 0) (Z.leb 0 dx)).
Definition PolarCmpResult (gp a b : point) (ret : Z) : Prop :=
  let ha := polar_upper_half gp a in
  let hb := polar_upper_half gp b in
  let cr := polar_cross gp a b in
  let da := point_dist2 gp a in
  let db := point_dist2 gp b in
  (ha = true /\ hb = false /\ ret = -1) \/
  (ha = false /\ hb = true /\ ret = 1) \/
  (ha = hb /\ cr > 0 /\ ret = -1) \/
  (ha = hb /\ cr < 0 /\ ret = 1) \/
  (ha = hb /\ cr = 0 /\ da < db /\ ret = -1) \/
  (ha = hb /\ cr = 0 /\ da > db /\ ret = 1) \/
  (ha = hb /\ cr = 0 /\ da = db /\ point_x a < point_x b /\ ret = -1) \/
  (ha = hb /\ cr = 0 /\ da = db /\ point_x a > point_x b /\ ret = 1) \/
  (ha = hb /\ cr = 0 /\ da = db /\ point_x a = point_x b /\ point_y a < point_y b /\ ret = -1) \/
  (ha = hb /\ cr = 0 /\ da = db /\ point_x a = point_x b /\ point_y a > point_y b /\ ret = 1) \/
  (ha = hb /\ cr = 0 /\ da = db /\ point_x a = point_x b /\ point_y a = point_y b /\ ret = 0).
Definition PolarLe (gp a b : point) : Prop :=
  PolarCmpResult gp a b (-1) \/ PolarCmpResult gp a b 0.
Definition PolarSorted (gp : point) (l : list point) : Prop :=
  forall i j,
    0 <= i ->
    i <= j ->
    j < Zlength l ->
    PolarLe gp (Znth i l default_point) (Znth j l default_point).
