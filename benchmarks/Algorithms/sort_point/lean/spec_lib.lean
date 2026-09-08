import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic

namespace Algorithms.sort_point.lean

open AUXLib

def point : Type := Int × Int

def mk_point (x y : Int) : point := (x, y)

def point_x (p : point) : Int := p.1

def point_y (p : point) : Int := p.2

def default_point : point := mk_point 0 0

def CoordInBounds (z : Int) : Prop := -10000 ≤ z ∧ z ≤ 10000

def PointCoordsBound (l : List point) : Prop := Forall (fun p => CoordInBounds (point_x p) ∧ CoordInBounds (point_y p)) l

def flat_points_rec (flat : List Int) : List point → Prop
  | [] => flat = []
  | p :: rest => ∃ flat_rest, flat = point_x p :: point_y p :: flat_rest ∧ flat_points_rec flat_rest rest

def FlatPoints (flat : List Int) (pts : List point) : Prop := Zlength flat = 2 * Zlength pts ∧ flat_points_rec flat pts

def PointPermutation : List point → List point → Prop := @Permutation point

def polar_cross (gp a b : point) : Int :=
  (point_x a-point_x gp)*(point_y b-point_y gp) - (point_y a-point_y gp)*(point_x b-point_x gp)

def point_dist2 (gp a : point) : Int :=
  (point_x gp-point_x a)*(point_x gp-point_x a) + (point_y gp-point_y a)*(point_y gp-point_y a)

def polar_upper_half (gp a : point) : Bool :=
  let dx := point_x a-point_x gp
  let dy := point_y a-point_y gp
  decide (0 < dy) || (decide (dy = 0) && decide (0 ≤ dx))

def PolarCmpResult (gp a b : point) (ret : Int) : Prop :=
  let ha := polar_upper_half gp a
  let hb := polar_upper_half gp b
  let cr := polar_cross gp a b
  let da := point_dist2 gp a
  let db := point_dist2 gp b
  (ha = true ∧ hb = false ∧ ret = -1) ∨
  (ha = false ∧ hb = true ∧ ret = 1) ∨
  (ha = hb ∧ cr > 0 ∧ ret = -1) ∨
  (ha = hb ∧ cr < 0 ∧ ret = 1) ∨
  (ha = hb ∧ cr = 0 ∧ da < db ∧ ret = -1) ∨
  (ha = hb ∧ cr = 0 ∧ da > db ∧ ret = 1) ∨
  (ha = hb ∧ cr = 0 ∧ da = db ∧ point_x a < point_x b ∧ ret = -1) ∨
  (ha = hb ∧ cr = 0 ∧ da = db ∧ point_x a > point_x b ∧ ret = 1) ∨
  (ha = hb ∧ cr = 0 ∧ da = db ∧ point_x a = point_x b ∧ point_y a < point_y b ∧ ret = -1) ∨
  (ha = hb ∧ cr = 0 ∧ da = db ∧ point_x a = point_x b ∧ point_y a > point_y b ∧ ret = 1) ∨
  (ha = hb ∧ cr = 0 ∧ da = db ∧ point_x a = point_x b ∧ point_y a = point_y b ∧ ret = 0)

def PolarLe (gp a b : point) : Prop := PolarCmpResult gp a b (-1) ∨ PolarCmpResult gp a b 0

def PolarSorted (gp : point) (l : List point) : Prop :=
  ∀ i j, 0 ≤ i → i ≤ j → j < Zlength l → PolarLe gp (Znth i l default_point) (Znth j l default_point)

end Algorithms.sort_point.lean
