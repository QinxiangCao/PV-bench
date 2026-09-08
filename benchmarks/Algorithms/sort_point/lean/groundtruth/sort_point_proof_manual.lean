import Algorithms.sort_point.lean.groundtruth.sort_point_goal
import Algorithms.sort_point.lean.groundtruth.sort_point_proof_auto
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import ListLib.General.Length

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace Algorithms.sort_point.lean.groundtruth.sort_point_proof_manual

open Algorithms.sort_point.lean
open scoped SimpleC

namespace ProofSupport

open AUXLib

private theorem nth_default {A : Type} (l : List A) (i : Int) (a b : A) (hi : 0 ≤ i ∧ i < Zlength l) : Znth i l a = Znth i l b := by
  unfold Znth
  have hb : i.toNat < l.length := by simp only [Zlength, Int.ofNat_eq_coe] at hi; omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb, Option.getD_some]

private theorem nth_mem {A : Type} (l : List A) (i : Int) (d : A) (hi : 0 ≤ i ∧ i < Zlength l) : Znth i l d ∈ l := by
  unfold Znth
  have hb : i.toNat < l.length := by simp only [Zlength, Int.ofNat_eq_coe] at hi; omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb, Option.getD_some]
  exact List.getElem_mem _

theorem polar_upper_half_true_of_pos_y (gx gy x y : Int) (hy : y-gy > 0) :
    polar_upper_half (mk_point gx gy) (mk_point x y) = true := by
  simp [polar_upper_half, mk_point, point_x, point_y, hy]
  omega

theorem polar_upper_half_true_of_zero_y_nonneg_x (gx gy x y : Int) (hx : x-gx ≥ 0) (hy : y-gy = 0) :
    polar_upper_half (mk_point gx gy) (mk_point x y) = true := by
  simp [polar_upper_half, mk_point, point_x, point_y, hy, hx]
  omega

theorem polar_upper_half_false_of_nonpos_nonzero_y (gx gy x y : Int) (hne : y-gy ≠ 0) (hy : y-gy ≤ 0) :
    polar_upper_half (mk_point gx gy) (mk_point x y) = false := by
  simp [polar_upper_half, mk_point, point_x, point_y, hne, show ¬ 0 < y-gy by omega]
  omega

theorem polar_upper_half_false_of_zero_y_neg_x (gx gy x y : Int) (hx : x-gx < 0) (hy : y-gy = 0) :
    polar_upper_half (mk_point gx gy) (mk_point x y) = false := by
  simp [polar_upper_half, mk_point, point_x, point_y, hy, show ¬ 0 ≤ x-gx by omega]
  omega

theorem flat_points_rec_Znth_point (flat : List Int) (pts : List point) (j : Int)
    (hf : flat_points_rec flat pts) (hj : 0 ≤ j ∧ j < Zlength pts) :
    Znth j pts default_point = mk_point (Znth (2*j) flat 0) (Znth (2*j+1) flat 0) := by
  induction pts generalizing flat j with
  | nil => simp only [Zlength_nil] at hj; omega
  | cons p rest ih =>
    obtain ⟨tail, rfl, ht⟩ := hf
    have hl : Zlength (p :: rest) = Zlength rest+1 := Zlength_cons _ _
    by_cases hz : j = 0
    · subst j; cases p; rfl
    · have hjp : 0 < j := by omega
      rw [Znth_cons default_point j p rest hjp]
      have hr := ih tail (j-1) ht (by omega)
      rw [hr]
      rw [Znth_cons 0 (2*j) (point_x p) (point_y p :: tail) (by omega),
        Znth_cons 0 (2*j-1) (point_y p) tail (by omega),
        Znth_cons 0 (2*j+1) (point_x p) (point_y p :: tail) (by omega),
        Znth_cons 0 (2*j+1-1) (point_y p) tail (by omega)]
      congr 2 <;> omega

theorem flat_points_lookup_point (flat : List Int) (pts : List point) (i : Int)
    (hi : 0 ≤ i ∧ i < Zlength pts) (hf : FlatPoints flat pts) :
    mk_point (Znth (2*i) flat 0) (Znth (2*i+1) flat 0) = Znth i pts default_point :=
  (flat_points_rec_Znth_point flat pts i hf.2 hi).symm

theorem point_coords_bound_lookup (pts : List point) (i : Int) (hi : 0 ≤ i ∧ i < Zlength pts) (hb : PointCoordsBound pts) :
    CoordInBounds (point_x (Znth i pts default_point)) ∧ CoordInBounds (point_y (Znth i pts default_point)) :=
  (Forall.iff_forall_mem.mp hb) _ (nth_mem pts i default_point hi)

theorem PolarCmpResult_nonpos_le (gp a b : point) (ret : Int) (hc : PolarCmpResult gp a b ret) (hr : ret ≤ 0) : PolarLe gp a b := by
  unfold PolarCmpResult at hc
  unfold PolarLe PolarCmpResult
  grind (splits := 30)

theorem FlatPoints_Znth_point (flat : List Int) (pts : List point) (j : Int) (hf : FlatPoints flat pts) (hj : 0 ≤ j ∧ j < Zlength pts) :
    Znth j pts default_point = mk_point (Znth (2*j) flat 0) (Znth (2*j+1) flat 0) := flat_points_rec_Znth_point flat pts j hf.2 hj

theorem Zlength_point_swap_points (l : List point) (i j : Int) : Zlength (point_swap_points l i j) = Zlength l := by
  simp only [point_swap_points, Zlength_replace_Znth]

theorem Znth_point_swap_points_right (l : List point) (i j : Int) (d : point)
    (hi : 0 ≤ i ∧ i < Zlength l) (hj : 0 ≤ j ∧ j < Zlength l) : Znth j (point_swap_points l i j) d = Znth i l d := by
  unfold point_swap_points
  rw [Znth_replace_Znth_Same d _ j _ (by simpa only [Zlength_replace_Znth] using hj)]
  exact nth_default l i default_point d hi

theorem Znth_point_swap_points_left (l : List point) (i j : Int) (d : point)
    (hi : 0 ≤ i ∧ i < Zlength l) (hj : 0 ≤ j ∧ j < Zlength l) : Znth i (point_swap_points l i j) d = Znth j l d := by
  by_cases he : i = j
  · subst j; exact Znth_point_swap_points_right l i i d hi hi
  · unfold point_swap_points
    rw [Znth_replace_Znth_Diff d _ j i _ (by simpa only [Zlength_replace_Znth] using hj) (by simpa only [Zlength_replace_Znth] using hi) (Ne.symm he),
      Znth_replace_Znth_Same d l i _ hi]
    exact nth_default l j default_point d hj

theorem Znth_point_swap_points_other (l : List point) (i j k : Int) (d : point)
    (hi : 0 ≤ i ∧ i < Zlength l) (hj : 0 ≤ j ∧ j < Zlength l) (hk : 0 ≤ k ∧ k < Zlength l) (hki : k ≠ i) (hkj : k ≠ j) :
    Znth k (point_swap_points l i j) d = Znth k l d := by
  unfold point_swap_points
  rw [Znth_replace_Znth_Diff d _ j k _ (by simpa only [Zlength_replace_Znth] using hj) (by simpa only [Zlength_replace_Znth] using hk) (Ne.symm hkj),
    Znth_replace_Znth_Diff d l i k _ hi hk (Ne.symm hki)]

theorem PolarCmpResult_one_implies_PolarLt_flip (gp a b : point) (hc : PolarCmpResult gp a b 1) : PolarLt gp b a := by
  have hcross : polar_cross gp b a = - polar_cross gp a b := by unfold polar_cross; grind
  unfold PolarCmpResult at hc
  unfold PolarLt PolarCmpResult
  rw [hcross]
  grind (splits := 30)

theorem flat_points_rec_functional (flat : List Int) (pts1 pts2 : List point)
    (h1 : flat_points_rec flat pts1) (h2 : flat_points_rec flat pts2) : pts1 = pts2 := by
  induction pts1 generalizing flat pts2 with
  | nil =>
    subst flat
    cases pts2 with
    | nil => rfl
    | cons p ps => obtain ⟨tail, he, _⟩ := h2; cases he
  | cons p ps ih =>
    obtain ⟨tail, rfl, ht⟩ := h1
    cases pts2 with
    | nil => cases h2
    | cons q qs =>
      obtain ⟨tail2, he, ht2⟩ := h2
      have heq : p = q := by
        cases p; cases q
        simp only [point_x, point_y, List.cons.injEq] at he
        simp_all
      have htEq : tail = tail2 := (List.cons.inj (List.cons.inj he).2).2
      subst tail2
      rw [heq, ih tail qs ht ht2]

theorem FlatPoints_functional (flat : List Int) (pts1 pts2 : List point) (h1 : FlatPoints flat pts1) (h2 : FlatPoints flat pts2) : pts1 = pts2 :=
  flat_points_rec_functional flat pts1 pts2 h1.2 h2.2

theorem PolarLe_refl (gp p : point) : PolarLe gp p p := by
  unfold PolarLe PolarCmpResult polar_cross
  simp [Int.mul_comm]

theorem PointSameOutsideRange_refl (l : List point) (left right : Int) : PointSameOutsideRange l l left right :=
  ⟨rfl, fun _ _ _ => rfl⟩

theorem PointSortedRange_degenerate (gp : point) (l : List point) (left right : Int) (hb : left ≥ right) : PointSortedRange gp l left right := by
  intro i j hi hij hj
  have he : i = j := by omega
  subst j
  exact PolarLe_refl gp _

theorem PolarLt_implies_PolarLe (gp a b : point) (hl : PolarLt gp a b) : PolarLe gp a b := Or.inl hl

theorem polar_upper_half_true_iff (gp p : point) : polar_upper_half gp p = true ↔
    point_y p-point_y gp > 0 ∨ (point_y p-point_y gp = 0 ∧ point_x p-point_x gp ≥ 0) := by
  simp [polar_upper_half]

theorem polar_upper_half_false_iff (gp p : point) : polar_upper_half gp p = false ↔
    point_y p-point_y gp < 0 ∨ (point_y p-point_y gp = 0 ∧ point_x p-point_x gp < 0) := by
  simp only [polar_upper_half, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  omega

private theorem square_nonneg (x : Int) : 0 ≤ x*x := by
  by_cases hx : 0 ≤ x
  · exact Int.mul_nonneg hx hx
  · have h := Int.mul_nonneg (show 0 ≤ -x by omega) (show 0 ≤ -x by omega)
    have he : -x * -x = x*x := by grind
    rw [he] at h
    exact h

private theorem zero_square_sum (x y : Int) (h : x*x+y*y = 0) : x = 0 ∧ y = 0 := by
  have hx := square_nonneg x
  have hy := square_nonneg y
  have hx0 : x*x = 0 := by omega
  have hy0 : y*y = 0 := by omega
  constructor
  · exact (Int.mul_eq_zero.mp hx0).elim id id
  · exact (Int.mul_eq_zero.mp hy0).elim id id

theorem same_norm_zero_cross_same_or_opposite (dx1 dy1 dx2 dy2 : Int)
    (hc : dx1*dy2-dy1*dx2 = 0) (hn : dx1*dx1+dy1*dy1 = dx2*dx2+dy2*dy2) :
    (dx1 = dx2 ∧ dy1 = dy2) ∨ (dx1 = -dx2 ∧ dy1 = -dy2) := by
  have hp : ((dx1-dx2)*(dx1-dx2)+(dy1-dy2)*(dy1-dy2))*
      ((dx1+dx2)*(dx1+dx2)+(dy1+dy2)*(dy1+dy2)) = 0 := by grind
  rcases Int.mul_eq_zero.mp hp with h | h
  · have he := zero_square_sum (dx1-dx2) (dy1-dy2) h
    left; omega
  · have he := zero_square_sum (dx1+dx2) (dy1+dy2) h
    right; omega

theorem opposite_same_half_zero (gp a b : point)
    (hh : polar_upper_half gp a = polar_upper_half gp b)
    (hx : point_x a-point_x gp = -(point_x b-point_x gp))
    (hy : point_y a-point_y gp = -(point_y b-point_y gp)) : a = gp ∧ b = gp := by
  cases ha : polar_upper_half gp a with
  | false =>
    have hb : polar_upper_half gp b = false := hh ▸ ha
    have h1 := (polar_upper_half_false_iff gp a).mp ha
    have h2 := (polar_upper_half_false_iff gp b).mp hb
    omega
  | true =>
    have hb : polar_upper_half gp b = true := hh ▸ ha
    have h1 := (polar_upper_half_true_iff gp a).mp ha
    have h2 := (polar_upper_half_true_iff gp b).mp hb
    cases gp; cases a; cases b
    simp only [point_x, point_y] at *
    constructor <;> apply Prod.ext <;> omega

theorem polar_cross_eq_dist_eq_same_half_eq (gp a b : point)
    (hh : polar_upper_half gp a = polar_upper_half gp b) (hc : polar_cross gp a b = 0)
    (hd : point_dist2 gp a = point_dist2 gp b) : a = b := by
  have hn : (point_x a-point_x gp)*(point_x a-point_x gp)+(point_y a-point_y gp)*(point_y a-point_y gp) =
      (point_x b-point_x gp)*(point_x b-point_x gp)+(point_y b-point_y gp)*(point_y b-point_y gp) := by
    unfold point_dist2 at hd
    grind
  rcases same_norm_zero_cross_same_or_opposite _ _ _ _ hc hn with ⟨hx,hy⟩ | ⟨hx,hy⟩
  · cases a; cases b
    simp only [point_x, point_y] at *
    apply Prod.ext <;> omega
  · have he := opposite_same_half_zero gp a b hh hx hy
    exact he.1.trans he.2.symm

theorem PolarCmpResult_zero_eq (gp a b : point) (hc : PolarCmpResult gp a b 0) : a = b := by
  unfold PolarCmpResult at hc
  have he : point_x a = point_x b ∧ point_y a = point_y b := by grind (splits := 30)
  cases a; cases b
  simp only [point_x, point_y] at he
  exact Prod.ext he.1 he.2

private theorem cross_identity (ax ay bx byv cx cy : Int) :
    byv*(ax*cy-ay*cx) = ay*(bx*cy-byv*cx)+cy*(ax*byv-ay*bx) := by grind

private theorem cross_pos_implies_middle_y (ax ay bx byv : Int)
    (ha : ay > 0 ∨ (ay = 0 ∧ ax ≥ 0)) (hb : byv > 0 ∨ (byv = 0 ∧ bx ≥ 0))
    (hc : ax*byv-ay*bx > 0) : 0 < byv := by
  rcases hb with h | ⟨he,hx⟩
  · exact h
  · have hy : 0 ≤ ay := by omega
    have hm := Int.mul_nonneg hy hx
    rw [he] at hc
    simp only [Int.mul_zero, Int.zero_sub] at hc
    omega

private theorem pos_of_pos_mul (a b : Int) (ha : 0 ≤ a) (h : 0 < a*b) : 0 < b := by
  by_cases hb : 0 < b
  · exact hb
  · have hm := Int.mul_nonpos_of_nonneg_of_nonpos ha (show b ≤ 0 by omega)
    omega

theorem upper_half_cross_trans_test (ax ay bx byv cx cy : Int)
    (ha : ay > 0 ∨ (ay = 0 ∧ ax ≥ 0)) (hb : byv > 0 ∨ (byv = 0 ∧ bx ≥ 0))
    (hc : cy > 0 ∨ (cy = 0 ∧ cx ≥ 0)) (hab : ax*byv-ay*bx > 0) (hbc : bx*cy-byv*cx > 0) :
    ax*cy-ay*cx > 0 := by
  have hby := cross_pos_implies_middle_y ax ay bx byv ha hb hab
  have hcy := cross_pos_implies_middle_y bx byv cx cy hb hc hbc
  have ha0 : 0 ≤ ay := by omega
  have hm1 := Int.mul_nonneg ha0 (show 0 ≤ bx*cy-byv*cx by omega)
  have hm2 := Int.mul_pos hcy hab
  have hid := cross_identity ax ay bx byv cx cy
  exact pos_of_pos_mul byv _ (by omega) (by omega)

theorem upper_half_cross_ray_right_test (ax ay bx byv cx cy : Int)
    (ha : ay > 0 ∨ (ay = 0 ∧ ax ≥ 0)) (hb : byv > 0 ∨ (byv = 0 ∧ bx ≥ 0))
    (hc : cy > 0 ∨ (cy = 0 ∧ cx ≥ 0)) (hab : ax*byv-ay*bx > 0) (hbc : bx*cy-byv*cx = 0)
    (hd : bx*bx+byv*byv < cx*cx+cy*cy) : ax*cy-ay*cx > 0 := by
  have hby := cross_pos_implies_middle_y ax ay bx byv ha hb hab
  have hcy : 0 < cy := by
    rcases hc with h | ⟨hy,hx⟩
    · exact h
    · rw [hy] at hbc hd
      simp only [Int.mul_zero, Int.zero_sub, Int.zero_mul, Int.add_zero] at hbc hd
      have hcx : cx = 0 := by
        have he : byv*cx = 0 := by omega
        exact (Int.mul_eq_zero.mp he).resolve_left (by omega)
      rw [hcx] at hd
      have h1 := square_nonneg bx
      have h2 := square_nonneg byv
      simp only [Int.mul_zero] at hd
      omega
  have hm := Int.mul_pos hcy hab
  have hid := cross_identity ax ay bx byv cx cy
  rw [hbc, Int.mul_zero, Int.zero_add] at hid
  exact pos_of_pos_mul byv _ (by omega) (by omega)

theorem upper_half_cross_ray_left_test (ax ay bx byv cx cy : Int)
    (ha : ay > 0 ∨ (ay = 0 ∧ ax ≥ 0)) (hb : byv > 0 ∨ (byv = 0 ∧ bx ≥ 0))
    (hc : cy > 0 ∨ (cy = 0 ∧ cx ≥ 0)) (hab : ax*byv-ay*bx = 0)
    (hd : ax*ax+ay*ay < bx*bx+byv*byv) (hbc : bx*cy-byv*cx > 0) :
    ax*cy-ay*cx > 0 ∨ (ax*cy-ay*cx = 0 ∧ ax*ax+ay*ay < cx*cx+cy*cy) := by
  have hcy := cross_pos_implies_middle_y bx byv cx cy hb hc hbc
  have hcNorm : 0 < cx*cx+cy*cy := by
    have h1 := square_nonneg cx
    have h2 := Int.mul_pos hcy hcy
    omega
  by_cases hay : 0 < ay
  · have hby : 0 < byv := by
      rcases hb with h | ⟨hy,hx⟩
      · exact h
      · rw [hy] at hab hbc
        simp only [Int.mul_zero, Int.zero_sub, Int.zero_mul, Int.sub_zero] at hab hbc
        have hxpos := pos_of_pos_mul cy bx (by omega) (by simpa only [Int.mul_comm] using hbc)
        have hm := Int.mul_pos hay hxpos
        omega
    have hm := Int.mul_pos hay hbc
    have hid := cross_identity ax ay bx byv cx cy
    rw [hab, Int.mul_zero, Int.add_zero] at hid
    exact Or.inl (pos_of_pos_mul byv _ (by omega) (by omega))
  · have hy : ay = 0 := by omega
    have hx : 0 ≤ ax := by omega
    rw [hy] at hab ⊢
    simp only [Int.zero_mul, Int.sub_zero, Int.add_zero] at hab ⊢
    by_cases hax : ax = 0
    · right
      rw [hax]
      simp only [Int.zero_mul, Int.mul_zero]
      exact ⟨True.intro, hcNorm⟩
    · exact Or.inl (Int.mul_pos (by omega) hcy)

theorem upper_half_ray_dist_trans_test (ax ay bx byv cx cy : Int)
    (ha : ay > 0 ∨ (ay = 0 ∧ ax ≥ 0)) (hb : byv > 0 ∨ (byv = 0 ∧ bx ≥ 0))
    (hc : cy > 0 ∨ (cy = 0 ∧ cx ≥ 0)) (hab : ax*byv-ay*bx = 0)
    (hd1 : ax*ax+ay*ay < bx*bx+byv*byv) (hbc : bx*cy-byv*cx = 0)
    (hd2 : bx*bx+byv*byv < cx*cx+cy*cy) :
    ax*cy-ay*cx = 0 ∧ ax*ax+ay*ay < cx*cx+cy*cy := by
  refine ⟨?_, by omega⟩
  have hbNonzero : bx ≠ 0 ∨ byv ≠ 0 := by
    have h1 := square_nonneg ax
    have h2 := square_nonneg ay
    by_cases hbx : bx = 0
    · right; intro hy; rw [hbx, hy] at hd1; simp only [Int.mul_zero, Int.add_zero] at hd1; omega
    · exact Or.inl hbx
  rcases hbNonzero with hx | hy
  · have hid : bx*(ax*cy-ay*cx) = ax*(bx*cy-byv*cx)+cx*(ax*byv-ay*bx) := by grind
    rw [hab, hbc, Int.mul_zero, Int.mul_zero, Int.add_zero] at hid
    exact (Int.mul_eq_zero.mp hid).resolve_left hx
  · have hid := cross_identity ax ay bx byv cx cy
    rw [hab, hbc, Int.mul_zero, Int.mul_zero, Int.add_zero] at hid
    exact (Int.mul_eq_zero.mp hid).resolve_left hy


theorem lower_half_cross_trans_test (ax ay bx byv cx cy : Int)
    (ha : ay < 0 ∨ (ay = 0 ∧ ax < 0)) (hb : byv < 0 ∨ (byv = 0 ∧ bx < 0))
    (hc : cy < 0 ∨ (cy = 0 ∧ cx < 0)) (hab : ax*byv-ay*bx > 0) (hbc : bx*cy-byv*cx > 0) :
    ax*cy-ay*cx > 0 := by
  have h := upper_half_cross_trans_test (-ax) (-ay) (-bx) (-byv) (-cx) (-cy)
    (by omega) (by omega) (by omega) (by grind) (by grind)
  grind

theorem lower_half_cross_ray_right_test (ax ay bx byv cx cy : Int)
    (ha : ay < 0 ∨ (ay = 0 ∧ ax < 0)) (hb : byv < 0 ∨ (byv = 0 ∧ bx < 0))
    (hc : cy < 0 ∨ (cy = 0 ∧ cx < 0)) (hab : ax*byv-ay*bx > 0) (hbc : bx*cy-byv*cx = 0)
    (hd : bx*bx+byv*byv < cx*cx+cy*cy) : ax*cy-ay*cx > 0 := by
  have h := upper_half_cross_ray_right_test (-ax) (-ay) (-bx) (-byv) (-cx) (-cy)
    (by omega) (by omega) (by omega) (by grind) (by grind) (by grind)
  grind

theorem lower_half_cross_ray_left_test (ax ay bx byv cx cy : Int)
    (ha : ay < 0 ∨ (ay = 0 ∧ ax < 0)) (hb : byv < 0 ∨ (byv = 0 ∧ bx < 0))
    (hc : cy < 0 ∨ (cy = 0 ∧ cx < 0)) (hab : ax*byv-ay*bx = 0)
    (hd : ax*ax+ay*ay < bx*bx+byv*byv) (hbc : bx*cy-byv*cx > 0) :
    ax*cy-ay*cx > 0 ∨ (ax*cy-ay*cx = 0 ∧ ax*ax+ay*ay < cx*cx+cy*cy) := by
  have h := upper_half_cross_ray_left_test (-ax) (-ay) (-bx) (-byv) (-cx) (-cy)
    (by omega) (by omega) (by omega) (by grind) (by grind) (by grind)
  grind

theorem lower_half_ray_dist_trans_test (ax ay bx byv cx cy : Int)
    (ha : ay < 0 ∨ (ay = 0 ∧ ax < 0)) (hb : byv < 0 ∨ (byv = 0 ∧ bx < 0))
    (hc : cy < 0 ∨ (cy = 0 ∧ cx < 0)) (hab : ax*byv-ay*bx = 0)
    (hd1 : ax*ax+ay*ay < bx*bx+byv*byv) (hbc : bx*cy-byv*cx = 0)
    (hd2 : bx*bx+byv*byv < cx*cx+cy*cy) :
    ax*cy-ay*cx = 0 ∧ ax*ax+ay*ay < cx*cx+cy*cy := by
  have h := upper_half_ray_dist_trans_test (-ax) (-ay) (-bx) (-byv) (-cx) (-cy)
    (by omega) (by omega) (by omega) (by grind) (by grind) (by grind) (by grind)
  grind

theorem PolarLt_simplified_test (gp a b : point) (hl : PolarLt gp a b) :
    (polar_upper_half gp a = true ∧ polar_upper_half gp b = false) ∨
    (polar_upper_half gp a = polar_upper_half gp b ∧ polar_cross gp a b > 0) ∨
    (polar_upper_half gp a = polar_upper_half gp b ∧ polar_cross gp a b = 0 ∧ point_dist2 gp a < point_dist2 gp b) := by
  have hn : ¬(polar_upper_half gp a = polar_upper_half gp b ∧ polar_cross gp a b = 0 ∧ point_dist2 gp a = point_dist2 gp b) := by
    rintro ⟨hh,hc,hd⟩
    have he := polar_cross_eq_dist_eq_same_half_eq gp a b hh hc hd
    subst b
    unfold PolarLt PolarCmpResult at hl
    simp only [gt_iff_lt, Int.lt_irrefl] at hl
    grind (splits := 30)
  unfold PolarLt PolarCmpResult at hl
  grind (splits := 30)

theorem PolarLe_lt_or_eq_test (gp a b : point) (hl : PolarLe gp a b) : PolarLt gp a b ∨ a = b := by
  rcases hl with h | h
  · exact Or.inl h
  · exact Or.inr (PolarCmpResult_zero_eq gp a b h)

private theorem dist_shift (gp a : point) : point_dist2 gp a =
    (point_x a-point_x gp)*(point_x a-point_x gp)+(point_y a-point_y gp)*(point_y a-point_y gp) := by
  unfold point_dist2
  grind

private theorem same_half_trans (gp a b c : point)
    (hab : polar_upper_half gp a = polar_upper_half gp b)
    (hbc : polar_upper_half gp b = polar_upper_half gp c)
    (hl1 : polar_cross gp a b > 0 ∨ (polar_cross gp a b = 0 ∧ point_dist2 gp a < point_dist2 gp b))
    (hl2 : polar_cross gp b c > 0 ∨ (polar_cross gp b c = 0 ∧ point_dist2 gp b < point_dist2 gp c)) :
    polar_cross gp a c > 0 ∨ (polar_cross gp a c = 0 ∧ point_dist2 gp a < point_dist2 gp c) := by
  simp only [dist_shift, polar_cross] at hl1 hl2 ⊢
  cases ha : polar_upper_half gp a with
  | true =>
    have hb : polar_upper_half gp b = true := hab ▸ ha
    have hc : polar_upper_half gp c = true := hbc ▸ hb
    have h1 := (polar_upper_half_true_iff gp a).mp ha
    have h2 := (polar_upper_half_true_iff gp b).mp hb
    have h3 := (polar_upper_half_true_iff gp c).mp hc
    rcases hl1 with h | ⟨h,hd⟩ <;> rcases hl2 with h' | ⟨h',hd'⟩
    · exact Or.inl (upper_half_cross_trans_test _ _ _ _ _ _ h1 h2 h3 h h')
    · exact Or.inl (upper_half_cross_ray_right_test _ _ _ _ _ _ h1 h2 h3 h h' hd')
    · exact upper_half_cross_ray_left_test _ _ _ _ _ _ h1 h2 h3 h hd h'
    · exact Or.inr (upper_half_ray_dist_trans_test _ _ _ _ _ _ h1 h2 h3 h hd h' hd')
  | false =>
    have hb : polar_upper_half gp b = false := hab ▸ ha
    have hc : polar_upper_half gp c = false := hbc ▸ hb
    have h1 := (polar_upper_half_false_iff gp a).mp ha
    have h2 := (polar_upper_half_false_iff gp b).mp hb
    have h3 := (polar_upper_half_false_iff gp c).mp hc
    rcases hl1 with h | ⟨h,hd⟩ <;> rcases hl2 with h' | ⟨h',hd'⟩
    · exact Or.inl (lower_half_cross_trans_test _ _ _ _ _ _ h1 h2 h3 h h')
    · exact Or.inl (lower_half_cross_ray_right_test _ _ _ _ _ _ h1 h2 h3 h h' hd')
    · exact lower_half_cross_ray_left_test _ _ _ _ _ _ h1 h2 h3 h hd h'
    · exact Or.inr (lower_half_ray_dist_trans_test _ _ _ _ _ _ h1 h2 h3 h hd h' hd')

theorem PolarLt_trans_test (gp a b c : point) (hl1 : PolarLt gp a b) (hl2 : PolarLt gp b c) : PolarLt gp a c := by
  have h1 := PolarLt_simplified_test gp a b hl1
  have h2 := PolarLt_simplified_test gp b c hl2
  have hout : (polar_upper_half gp a = true ∧ polar_upper_half gp c = false) ∨
      (polar_upper_half gp a = polar_upper_half gp c ∧
      (polar_cross gp a c > 0 ∨ (polar_cross gp a c = 0 ∧ point_dist2 gp a < point_dist2 gp c))) := by
    by_cases hab : polar_upper_half gp a = polar_upper_half gp b
    · by_cases hbc : polar_upper_half gp b = polar_upper_half gp c
      · right; refine ⟨hab.trans hbc, ?_⟩
        apply same_half_trans gp a b c hab hbc <;> grind
      · left; grind
    · left; grind
  unfold PolarLt PolarCmpResult
  grind (splits := 30)

theorem PolarLe_PolarLt_trans_structured (gp a b c : point) (hle : PolarLe gp a b) (hlt : PolarLt gp b c) : PolarLe gp a c := by
  rcases PolarLe_lt_or_eq_test gp a b hle with h | h
  · exact PolarLt_implies_PolarLe gp a c (PolarLt_trans_test gp a b c h hlt)
  · subst b; exact PolarLt_implies_PolarLe gp a c hlt


private theorem sublist_lengthZ (l : List point) (lo hi : Int)
    (hlo : 0 ≤ lo ∧ lo ≤ hi) (hhi : hi ≤ Zlength l) :
    Zlength (sublist lo hi l) = hi - lo := ListLib.Zlength_sublist lo hi l hlo hhi


private theorem Forall_Znth_d (P : point → Prop) (l : List point) (i : Int) (d : point)
    (hp : Forall P l) (hi : 0 ≤ i ∧ i < Zlength l) : P (Znth i l d) := by
  have hin : i.toNat < l.length := by simp only [Zlength, Int.ofNat_eq_coe] at hi; omega
  have hmem := List.getElem_mem (l := l) hin
  have h := hp.mem hmem
  simpa only [Znth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hin, Option.getD_some] using h


private theorem Forall_of_Znth (P : point → Prop) (l : List point)
    (h : ∀ i, (0 ≤ i ∧ i < Zlength l) → P (Znth i l default_point)) : Forall P l := by
  apply Forall.iff_forall_mem.mpr
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  have hp := h i (by simp only [Zlength, Int.ofNat_eq_coe]; omega)
  simpa only [Znth, Int.toNat_natCast, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, Option.getD_some] using hp


theorem PointSameOutsideRange_trans (l l1 l2 : List point) (left right : Int)
    (h1 : PointSameOutsideRange l l1 left right) (h2 : PointSameOutsideRange l1 l2 left right) :
    PointSameOutsideRange l l2 left right := by
  refine ⟨h1.1.trans h2.1, ?_⟩
  intro k hk ho
  exact (h2.2 k (by have := h1.1; omega) ho).trans (h1.2 k hk ho)


theorem PointSameOutsideRange_weaken (l l1 : List point) (left1 right1 left2 right2 : Int)
    (hl : left2 ≤ left1) (hr : right1 ≤ right2) (h : PointSameOutsideRange l l1 left1 right1) :
    PointSameOutsideRange l l1 left2 right2 := by
  refine ⟨h.1, ?_⟩; intro k hk ho; exact h.2 k hk (by omega)


theorem Forall_permutation_point (P : point → Prop) (l1 l2 : List point)
    (hp : PointPermutation l1 l2) (h : Forall P l1) : Forall P l2 := h.perm hp


theorem Forall_Znth_point (P : point → Prop) (l : List point) (i : Int)
    (hp : Forall P l) (hi : 0 ≤ i ∧ i < Zlength l) : P (Znth i l default_point) :=
  Forall_Znth_d P l i default_point hp hi


theorem sublist_eq_from_Znth_point (l1 l2 : List point) (lo hi : Int)
    (hlen : Zlength l1 = Zlength l2) (hlo : 0 ≤ lo ∧ lo ≤ hi) (hhi : hi ≤ Zlength l1)
    (hp : ∀ k, (lo ≤ k ∧ k < hi) → Znth k l1 default_point = Znth k l2 default_point) :
    sublist lo hi l1 = sublist lo hi l2 := by
  apply (ListLib.list_eq_ext _ _ default_point).mpr
  refine ⟨?_, ?_⟩
  · exact (sublist_lengthZ l1 lo hi hlo hhi).trans (sublist_lengthZ l2 lo hi hlo (by omega)).symm
  · intro i hi'
    have hb : 0 ≤ i ∧ i < hi - lo := by have := sublist_lengthZ l1 lo hi hlo hhi; change 0 ≤ i ∧ i < Zlength (sublist lo hi l1) at hi'; omega
    change Znth i (sublist lo hi l1) default_point = Znth i (sublist lo hi l2) default_point
    rw [Znth_sublist default_point lo i hi l1 hlo.1 hb, Znth_sublist default_point lo i hi l2 hlo.1 hb]
    exact hp _ (by omega)


theorem list_decompose_sublist_point (l : List point) (lo hi : Int)
    (hlo : 0 ≤ lo ∧ lo ≤ hi) (hhi : hi ≤ Zlength l) :
    l = sublist 0 lo l ++ (sublist lo hi l ++ sublist hi (Zlength l) l) := by
  calc
    l = sublist 0 (Zlength l) l := (sublist_self l (Zlength l) rfl).symm
    _ = _ := by rw [sublist_split 0 (Zlength l) lo l (by omega) (by omega),
      sublist_split lo (Zlength l) hi l hlo (by omega)]


theorem PointSameOutsideRange_prefix (l l1 : List point) (left right : Int)
    (h : PointSameOutsideRange l l1 left right) (hl : 0 ≤ left ∧ left ≤ Zlength l) :
    sublist 0 left l1 = sublist 0 left l := by
  apply sublist_eq_from_Znth_point l1 l 0 left h.1.symm (by omega) (by have := h.1; omega)
  intro k hk; exact h.2 k (by omega) (Or.inl hk.2)


theorem PointSameOutsideRange_suffix (l l1 : List point) (left right : Int)
    (h : PointSameOutsideRange l l1 left right) (hr : 0 ≤ right + 1 ∧ right + 1 ≤ Zlength l) :
    sublist (right + 1) (Zlength l1) l1 = sublist (right + 1) (Zlength l) l := by
  rw [← h.1]
  apply sublist_eq_from_Znth_point l1 l (right + 1) (Zlength l) h.1.symm hr (by have := h.1; omega)
  intro k hk; exact h.2 k (by omega) (Or.inr (by omega))


theorem PointPermutation_middle_of_same_outside (l l1 : List point) (left right : Int)
    (hp : PointPermutation l l1) (h : PointSameOutsideRange l l1 left right)
    (hl : 0 ≤ left ∧ left ≤ right + 1) (hr : right + 1 ≤ Zlength l) :
    PointPermutation (sublist left (right + 1) l) (sublist left (right + 1) l1) := by
  have hd := list_decompose_sublist_point l left (right + 1) hl hr
  have hd1 := list_decompose_sublist_point l1 left (right + 1) hl (by have := h.1; omega)
  have hpfx := PointSameOutsideRange_prefix l l1 left right h (by omega)
  have hsfx := PointSameOutsideRange_suffix l l1 left right h (by omega)
  conv at hp => lhs; rw [hd]
  conv at hp => rhs; rw [hd1]
  rw [hpfx, hsfx] at hp
  exact (List.perm_append_right_iff _).mp ((List.perm_append_left_iff _).mp hp)


theorem Forall_sublist_by_Znth_point (P : point → Prop) (l : List point) (lo hi : Int)
    (hlo : 0 ≤ lo ∧ lo ≤ hi) (hhi : hi ≤ Zlength l)
    (hp : ∀ k, (lo ≤ k ∧ k < hi) → P (Znth k l default_point)) : Forall P (sublist lo hi l) := by
  apply Forall_of_Znth
  intro i hi'
  rw [sublist_lengthZ l lo hi hlo hhi] at hi'
  rw [Znth_sublist default_point lo i hi l hlo.1 hi']
  exact hp _ (by omega)


theorem PointPartitionedAt_preserved_by_left (gp : point) (l l1 : List point) (left right p : Int)
    (hp : PointPermutation l l1) (hl : 0 ≤ left) (h : PointSameOutsideRange l l1 left (p - 1))
    (hr : right < Zlength l) (hpart : PointPartitionedAt gp l left right p) : PointPartitionedAt gp l1 left right p := by
  have heq := h.2 p (by have := hpart.1; omega) (Or.inr (by omega))
  refine ⟨hpart.1, ?_, ?_⟩
  · rw [heq]
    have hm := PointPermutation_middle_of_same_outside l l1 left (p - 1) hp h (by have := hpart.1; omega) (by have := hpart.1; omega)
    simp only [Int.sub_add_cancel] at hm
    exact Forall_permutation_point _ _ _ hm hpart.2.1
  · rw [heq]
    have hs : sublist (p + 1) (right + 1) l1 = sublist (p + 1) (right + 1) l := by
      apply sublist_eq_from_Znth_point l1 l _ _ h.1.symm (by have := hpart.1; omega) (by have := h.1; omega)
      intro k hk; exact h.2 k (by have := hpart.1; omega) (Or.inr (by omega))
    rw [hs]; exact hpart.2.2


theorem PointPartitionedAt_preserved_by_right (gp : point) (l l1 : List point) (left right p : Int)
    (hp : PointPermutation l l1) (hl : 0 ≤ left) (h : PointSameOutsideRange l l1 (p + 1) right)
    (hr : right < Zlength l) (hpart : PointPartitionedAt gp l left right p) : PointPartitionedAt gp l1 left right p := by
  have heq := h.2 p (by have := hpart.1; omega) (Or.inl (by omega))
  refine ⟨hpart.1, ?_, ?_⟩
  · rw [heq]
    have hs : sublist left p l1 = sublist left p l := by
      apply sublist_eq_from_Znth_point l1 l _ _ h.1.symm (by have := hpart.1; omega) (by have := h.1; have := hpart.1; omega)
      intro k hk; exact h.2 k (by have := hpart.1; omega) (Or.inl (by omega))
    rw [hs]; exact hpart.2.1
  · rw [heq]
    exact Forall_permutation_point _ _ _ (PointPermutation_middle_of_same_outside l l1 (p + 1) right hp h (by have := hpart.1; omega) (by omega)) hpart.2.2


theorem PointCoordsBound_permutation (l1 l2 : List point) (hp : PointPermutation l1 l2)
    (h : PointCoordsBound l1) : PointCoordsBound l2 := h.perm hp

theorem Forall_sublist_lookup_point (P : point → Prop) (l : List point) (lo hi k : Int)
    (hl : 0 ≤ lo ∧ lo ≤ hi) (hh : hi ≤ Zlength l) (hf : Forall P (sublist lo hi l))
    (hk : lo ≤ k ∧ k < hi) : P (Znth k l default_point) := by
  have h := Forall_Znth_point P (sublist lo hi l) (k-lo) hf (by rw [sublist_lengthZ l lo hi hl hh]; omega)
  rw [Znth_sublist default_point lo (k-lo) hi l hl.1 (by omega)] at h
  simpa only [Int.sub_add_cancel] using h

theorem PointSameOutsideRange_swap_inside (l : List point) (low high i j : Int)
    (hlo : 0 ≤ low) (hi : low ≤ i ∧ i ≤ high) (hj : low ≤ j ∧ j ≤ high)
    (hh : high < Zlength l) : PointSameOutsideRange l (point_swap_points l i j) low high := by
  refine ⟨(Zlength_point_swap_points l i j).symm, ?_⟩
  intro k hk ho
  exact Znth_point_swap_points_other l i j k default_point (by omega) (by omega) hk (by omega) (by omega)

private theorem replace_boundary (l1 l2 : List point) (v x : point) :
    replace_Znth (Zlength l1) v (l1 ++ (x::l2)) = l1 ++ (v::l2) := by
  unfold replace_Znth Zlength
  change replace_nth l1.length (l1 ++ (x::l2)) v = l1 ++ (v::l2)
  induction l1 with
  | nil => rfl
  | cons a l ih => simpa only [List.length_cons, List.cons_append, replace_nth] using congrArg (List.cons a) ih

theorem replace_Znth_swap_form_point (l1 l2 l3 : List point) (xi xj : point) :
    replace_Znth (Zlength l1 + 1 + Zlength l2) xi
      (replace_Znth (Zlength l1) xj (l1 ++ (xi :: (l2 ++ (xj :: l3))))) =
    l1 ++ (xj :: (l2 ++ (xi :: l3))) := by
  rw [replace_boundary]
  have he : Zlength l1 + 1 + Zlength l2 = Zlength (l1 ++ (xj :: l2)) := by simp [Zlength]; omega
  rw [he]
  have ha : l1 ++ (xj :: (l2 ++ (xj :: l3))) = (l1 ++ (xj :: l2)) ++ (xj :: l3) := by simp only [List.append_assoc, List.cons_append]
  rw [ha, replace_boundary]
  simp only [List.append_assoc, List.cons_append]

private theorem perm_cons_replace (l : List point) (i : Nat) (x d : point) (hi : i < l.length) :
    List.Perm (x::l) (l.getD i d :: replace_nth i l x) := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih =>
    cases i with
    | zero => simpa only [List.getD_cons_zero, replace_nth] using List.Perm.swap a x l
    | succ i =>
      have hp := ih i (by simpa using hi)
      simpa only [List.getD_cons_succ, replace_nth] using
        (List.Perm.swap a x l).trans ((List.Perm.cons a hp).trans (List.Perm.swap (l.getD i d) a (replace_nth i l x)))

private theorem perm_swap_nat (l : List point) (i j : Nat) (d : point)
    (hi : i < l.length) (hj : j < l.length) :
    List.Perm l (replace_nth j (replace_nth i l (l.getD j d)) (l.getD i d)) := by
  induction l generalizing i j with
  | nil => simp at hi
  | cons a l ih =>
    cases i with
    | zero =>
      cases j with
      | zero => simp only [List.getD_cons_zero, replace_nth]; exact List.Perm.refl _
      | succ j => simpa only [List.getD_cons_zero, List.getD_cons_succ, replace_nth] using perm_cons_replace l j a d (by simpa using hj)
    | succ i =>
      cases j with
      | zero => simpa only [List.getD_cons_zero, List.getD_cons_succ, replace_nth] using perm_cons_replace l i a d (by simpa using hi)
      | succ j => simpa only [List.getD_cons_succ, replace_nth] using List.Perm.cons a (ih i j (by simpa using hi) (by simpa using hj))

theorem PointPermutation_swap_points (l : List point) (i j : Int)
    (hr : 0 ≤ i ∧ i < j ∧ j < Zlength l) : PointPermutation l (point_swap_points l i j) := by
  apply perm_swap_nat
  all_goals simp only [Zlength, Int.ofNat_eq_coe] at hr; omega

theorem point_swap_points_comm (l : List point) (i j : Int)
    (hi : 0 ≤ i ∧ i < Zlength l) (hj : 0 ≤ j ∧ j < Zlength l) :
    point_swap_points l i j = point_swap_points l j i := by
  apply (ListLib.list_eq_ext _ _ default_point).mpr
  refine ⟨?_, ?_⟩
  · change Zlength (point_swap_points l i j) = Zlength (point_swap_points l j i)
    rw [Zlength_point_swap_points, Zlength_point_swap_points]
  · intro k hk
    change 0 ≤ k ∧ k < Zlength (point_swap_points l i j) at hk
    rw [Zlength_point_swap_points] at hk
    change Znth k (point_swap_points l i j) default_point = Znth k (point_swap_points l j i) default_point
    by_cases he : k = i
    · subst k; rw [Znth_point_swap_points_left l i j _ hi hj, Znth_point_swap_points_right l j i _ hj hi]
    · by_cases he' : k = j
      · subst k; rw [Znth_point_swap_points_right l i j _ hi hj, Znth_point_swap_points_left l j i _ hj hi]
      · rw [Znth_point_swap_points_other l i j k _ hi hj hk he he', Znth_point_swap_points_other l j i k _ hj hi hk he' he]

theorem PointPermutation_swap_points_any (l : List point) (i j : Int)
    (hi : 0 ≤ i ∧ i < Zlength l) (hj : 0 ≤ j ∧ j < Zlength l) : PointPermutation l (point_swap_points l i j) := by
  apply perm_swap_nat
  all_goals simp only [Zlength, Int.ofNat_eq_coe] at hi hj; omega


theorem PointPartitionedAt_after_final_swap (gp : point) (l l1 : List point) (low high : Int) (pivot : point) (i : Int)
    (hlo : 0 ≤ low) (hh : high < Zlength l1) (hi : low-1 ≤ i) (hi' : i < high)
    (hs : PointPartitionScanInv gp l l1 low high pivot i high) :
    PointPartitionedAt gp (point_swap_points l1 (i+1) high) low high (i+1) := by
  have hpiv : Znth (i+1) (point_swap_points l1 (i+1) high) default_point = pivot :=
    (Znth_point_swap_points_left l1 (i+1) high _ (by omega) (by omega)).trans hs.2.2.1
  refine ⟨by omega, ?_, ?_⟩
  · rw [hpiv]
    apply Forall_sublist_by_Znth_point _ _ low (i+1) (by omega) (by rw [Zlength_point_swap_points]; omega)
    intro k hk
    rw [Znth_point_swap_points_other l1 (i+1) high k _ (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact hs.2.2.2.1 k (by omega)
  · rw [hpiv]
    apply Forall_sublist_by_Znth_point _ _ (i+1+1) (high+1) (by omega) (by rw [Zlength_point_swap_points]; omega)
    intro k hk
    by_cases he : k = high
    · subst k
      rw [Znth_point_swap_points_right l1 (i+1) high _ (by omega) (by omega)]
      exact hs.2.2.2.2 (i+1) (by omega)
    · rw [Znth_point_swap_points_other l1 (i+1) high k _ (by omega) (by omega) (by omega) (by omega) he]
      exact hs.2.2.2.2 k (by omega)

private theorem partition_sorted_combine (gp : point) (l : List point) (left right p : Int)
    (hl : 0 ≤ left) (hr : right < Zlength l) (hp : PointPartitionedAt gp l left right p)
    (hs1 : PointSortedRange gp l left (p-1)) (hs2 : PointSortedRange gp l (p+1) right) :
    PointSortedRange gp l left right := by
  have hb := hp.1
  have hleft : ∀ k, left ≤ k ∧ k < p → PolarLe gp (Znth k l default_point) (Znth p l default_point) := by
    intro k hk
    exact Forall_sublist_lookup_point _ l left p k (by omega) (by omega) hp.2.1 hk
  have hright : ∀ k, p < k ∧ k ≤ right → PolarLt gp (Znth p l default_point) (Znth k l default_point) := by
    intro k hk
    exact Forall_sublist_lookup_point _ l (p+1) (right+1) k (by omega) (by omega) hp.2.2 (by omega)
  intro i j hi hij hj
  by_cases hjl : j < p
  · exact hs1 i j hi hij (by omega)
  · by_cases hir : p < i
    · exact hs2 i j (by omega) hij hj
    · by_cases hip : i = p
      · subst i
        by_cases hjp : j = p
        · subst j; exact PolarLe_refl gp _
        · exact PolarLt_implies_PolarLe gp _ _ (hright j (by omega))
      · by_cases hjp : j = p
        · subst j; exact hleft i (by omega)
        · exact PolarLe_PolarLt_trans_structured gp _ _ _ (hleft i (by omega)) (hright j (by omega))

theorem PointSortedRange_from_left_boundary (gp : point) (l : List point) (left right p : Int)
    (hl : 0 ≤ left) (hp : p ≥ right) (hr : right < Zlength l) (hpart : PointPartitionedAt gp l left right p)
    (hs : PointSortedRange gp l left (p-1)) : PointSortedRange gp l left right :=
  partition_sorted_combine gp l left right p hl hr hpart hs (PointSortedRange_degenerate gp l (p+1) right (by omega))

theorem PointSortedRange_from_right_boundary (gp : point) (l : List point) (left right p : Int)
    (hl : 0 ≤ left) (hp : p ≤ left) (hr : right < Zlength l) (hpart : PointPartitionedAt gp l left right p)
    (hs : PointSortedRange gp l (p+1) right) : PointSortedRange gp l left right :=
  partition_sorted_combine gp l left right p hl hr hpart (PointSortedRange_degenerate gp l left (p-1) (by omega)) hs

theorem PointSortedRange_from_middle_partition (gp : point) (l : List point) (left right p : Int)
    (hl : 0 ≤ left) (hlp : left < p) (hpr : p < right) (hr : right < Zlength l)
    (hpart : PointPartitionedAt gp l left right p)
    (hs1 : PointSortedRange gp l left (p-1)) (hs2 : PointSortedRange gp l (p+1) right) : PointSortedRange gp l left right :=
  partition_sorted_combine gp l left right p hl hr hpart hs1 hs2

theorem PointSortedRange_ext (gp : point) (l l1 : List point) (left right : Int)
    (hl : 0 ≤ left) (hr : right < Zlength l) (hn : Zlength l = Zlength l1)
    (he : ∀ k, left ≤ k ∧ k ≤ right → Znth k l1 default_point = Znth k l default_point)
    (hs : PointSortedRange gp l left right) : PointSortedRange gp l1 left right := by
  intro i j hi hij hj
  rw [he i (by omega), he j (by omega)]
  exact hs i j hi hij hj

theorem Zlength_point_swap_flat (flat : List Int) (i j : Int) : Zlength (point_swap_flat flat i j) = Zlength flat := by
  simp only [point_swap_flat, Zlength_replace_Znth]

theorem point_swap_flat_preprocess_form (flat : List Int) (n i j : Int) (hn : Zlength flat = 2*n)
    (hi : 0 ≤ i ∧ i < n) (hj : 0 ≤ j ∧ j < n) :
    replace_Znth (2*j+1) (Znth (2*i+1) flat 0)
      (replace_Znth (2*j) (Znth (2*i) flat 0)
        (replace_Znth (2*i+1) (Znth (2*j+1) (replace_Znth (2*i) (Znth (2*j) flat 0) flat) 0)
          (replace_Znth (2*i) (Znth (2*j) flat 0) flat))) = point_swap_flat flat i j := by
  rw [Znth_replace_Znth_Diff 0 flat (2*i) (2*j+1) _ (by omega) (by omega) (by omega)]
  rfl

theorem flat_points_rec_from_lookup (flat : List Int) (pts : List point)
    (hn : Zlength flat = 2*Zlength pts)
    (he : ∀ j, 0 ≤ j ∧ j < Zlength pts → Znth j pts default_point = mk_point (Znth (2*j) flat 0) (Znth (2*j+1) flat 0)) :
    flat_points_rec flat pts := by
  induction pts generalizing flat with
  | nil =>
    change flat = []
    have hlen : flat.length = 0 := by simp only [Zlength, List.length_nil, Int.ofNat_eq_coe] at hn; omega
    cases flat with
    | nil => rfl
    | cons x xs => simp at hlen
  | cons p pts ih =>
    have hp := he 0 (by simp only [Zlength, List.length_cons, Int.ofNat_eq_coe]; omega)
    cases flat with
    | nil => simp only [Zlength, List.length_nil, List.length_cons, Int.ofNat_eq_coe] at hn; omega
    | cons x tail =>
      cases tail with
      | nil => simp only [Zlength, List.length_nil, List.length_cons, Int.ofNat_eq_coe] at hn; omega
      | cons y tail =>
        have hp' : p = mk_point x y := hp
        subst p
        refine ⟨tail, rfl, ih tail ?_ ?_⟩
        · simp only [Zlength, List.length_cons, Int.ofNat_eq_coe] at hn ⊢; omega
        · intro j hj
          have h := he (j+1) (by have := Zlength_cons (mk_point x y) pts; omega)
          rw [Znth_cons default_point (j+1) (mk_point x y) pts (by omega), Int.add_sub_cancel] at h
          rw [Znth_cons 0 (2*(j+1)) x (y::tail) (by omega),
            Znth_cons 0 (2*(j+1)-1) y tail (by omega),
            Znth_cons 0 (2*(j+1)+1) x (y::tail) (by omega),
            Znth_cons 0 (2*(j+1)+1-1) y tail (by omega)] at h
          have he1 : 2*(j+1)-1-1 = 2*j := by omega
          have he2 : 2*(j+1)+1-1-1 = 2*j+1 := by omega
          simpa only [he1, he2] using h

theorem FlatPoints_from_lookup (flat : List Int) (pts : List point)
    (hn : Zlength flat = 2*Zlength pts)
    (he : ∀ j, 0 ≤ j ∧ j < Zlength pts → Znth j pts default_point = mk_point (Znth (2*j) flat 0) (Znth (2*j+1) flat 0)) :
    FlatPoints flat pts := ⟨hn, flat_points_rec_from_lookup flat pts hn he⟩

private theorem read_int_replace (l : List Int) (i k v : Int)
    (hi : 0 ≤ i ∧ i < Zlength l) (hk : 0 ≤ k ∧ k < Zlength l) :
    Znth k (replace_Znth i v l) 0 = if k = i then v else Znth k l 0 := by
  by_cases h : k = i
  · subst k; simp only [ite_true]; exact Znth_replace_Znth_Same 0 l i v hi
  · rw [if_neg h]; exact Znth_replace_Znth_Diff 0 l i k v hi hk (Ne.symm h)

private theorem read_flat_swap (flat : List Int) (n i j k : Int) (hn : Zlength flat = 2*n)
    (hi : 0 ≤ i ∧ i < n) (hj : 0 ≤ j ∧ j < n) (hk : 0 ≤ k ∧ k < 2*n) :
    Znth k (point_swap_flat flat i j) 0 =
      if k = 2*j+1 then Znth (2*i+1) flat 0 else
      if k = 2*j then Znth (2*i) flat 0 else
      if k = 2*i+1 then Znth (2*j+1) flat 0 else
      if k = 2*i then Znth (2*j) flat 0 else Znth k flat 0 := by
  unfold point_swap_flat
  rw [read_int_replace _ (2*j+1) k _ (by simp only [Zlength_replace_Znth]; omega) (by simp only [Zlength_replace_Znth]; omega),
    read_int_replace _ (2*j) k _ (by simp only [Zlength_replace_Znth]; omega) (by simp only [Zlength_replace_Znth]; omega),
    read_int_replace _ (2*i+1) k _ (by simp only [Zlength_replace_Znth]; omega) (by simp only [Zlength_replace_Znth]; omega),
    read_int_replace _ (2*i) k _ (by omega) (by omega)]

theorem Znth_point_swap_flat_x_left (flat : List Int) (n i j : Int)
    (hn : Zlength flat = 2*n) (hi : 0 ≤ i ∧ i < n) (hj : 0 ≤ j ∧ j < n)
    : Znth (2*i) (point_swap_flat flat i j) 0 = Znth (2*j) flat 0 := by
  rw [read_flat_swap flat n i j (2*i) hn hi hj (by omega)]
  grind

theorem Znth_point_swap_flat_x_right (flat : List Int) (n i j : Int)
    (hn : Zlength flat = 2*n) (hi : 0 ≤ i ∧ i < n) (hj : 0 ≤ j ∧ j < n)
    : Znth (2*j) (point_swap_flat flat i j) 0 = Znth (2*i) flat 0 := by
  rw [read_flat_swap flat n i j (2*j) hn hi hj (by omega)]
  grind

theorem Znth_point_swap_flat_x_other (flat : List Int) (n i j k : Int)
    (hn : Zlength flat = 2*n) (hi : 0 ≤ i ∧ i < n) (hj : 0 ≤ j ∧ j < n)
    (hk : 0 ≤ k ∧ k < n) (hki : k ≠ i) (hkj : k ≠ j)
    : Znth (2*k) (point_swap_flat flat i j) 0 = Znth (2*k) flat 0 := by
  rw [read_flat_swap flat n i j (2*k) hn hi hj (by omega)]
  grind

theorem Znth_point_swap_flat_y_left (flat : List Int) (n i j : Int)
    (hn : Zlength flat = 2*n) (hi : 0 ≤ i ∧ i < n) (hj : 0 ≤ j ∧ j < n)
    : Znth (2*i+1) (point_swap_flat flat i j) 0 = Znth (2*j+1) flat 0 := by
  rw [read_flat_swap flat n i j (2*i+1) hn hi hj (by omega)]
  grind

theorem Znth_point_swap_flat_y_right (flat : List Int) (n i j : Int)
    (hn : Zlength flat = 2*n) (hi : 0 ≤ i ∧ i < n) (hj : 0 ≤ j ∧ j < n)
    : Znth (2*j+1) (point_swap_flat flat i j) 0 = Znth (2*i+1) flat 0 := by
  rw [read_flat_swap flat n i j (2*j+1) hn hi hj (by omega)]
  grind

theorem Znth_point_swap_flat_y_other (flat : List Int) (n i j k : Int)
    (hn : Zlength flat = 2*n) (hi : 0 ≤ i ∧ i < n) (hj : 0 ≤ j ∧ j < n)
    (hk : 0 ≤ k ∧ k < n) (hki : k ≠ i) (hkj : k ≠ j)
    : Znth (2*k+1) (point_swap_flat flat i j) 0 = Znth (2*k+1) flat 0 := by
  rw [read_flat_swap flat n i j (2*k+1) hn hi hj (by omega)]
  grind

theorem FlatPoints_swap_points (flat : List Int) (pts : List point) (i j : Int)
    (hf : FlatPoints flat pts) (hi : 0 ≤ i ∧ i < Zlength pts) (hj : 0 ≤ j ∧ j < Zlength pts) :
    FlatPoints (point_swap_flat flat i j) (point_swap_points pts i j) := by
  apply FlatPoints_from_lookup
  · rw [Zlength_point_swap_flat, Zlength_point_swap_points]; exact hf.1
  · intro k hk
    rw [Zlength_point_swap_points] at hk
    by_cases he : k = i
    · subst k
      rw [Znth_point_swap_points_left pts i j _ hi hj, FlatPoints_Znth_point flat pts j hf hj,
        Znth_point_swap_flat_x_left flat (Zlength pts) i j hf.1 hi hj,
        Znth_point_swap_flat_y_left flat (Zlength pts) i j hf.1 hi hj]
    · by_cases he' : k = j
      · subst k
        rw [Znth_point_swap_points_right pts i j _ hi hj, FlatPoints_Znth_point flat pts i hf hi,
          Znth_point_swap_flat_x_right flat (Zlength pts) i j hf.1 hi hj,
          Znth_point_swap_flat_y_right flat (Zlength pts) i j hf.1 hi hj]
      · rw [Znth_point_swap_points_other pts i j k _ hi hj hk he he', FlatPoints_Znth_point flat pts k hf hk,
          Znth_point_swap_flat_x_other flat (Zlength pts) i j k hf.1 hi hj hk he he',
          Znth_point_swap_flat_y_other flat (Zlength pts) i j k hf.1 hi hj hk he he']

end ProofSupport

open ProofSupport
open Algorithms.sort_point.lean.groundtruth.sort_point_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open Algorithms.sort_point.lean.groundtruth.sort_point_goal
open ProofSupport
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

private theorem coord_product (x y : Int) (hx : -20000 ≤ x ∧ x ≤ 20000) (hy : -20000 ≤ y ∧ y ≤ 20000) :
    -400000000 ≤ x*y ∧ x*y ≤ 400000000 := by
  have h1 := Int.mul_nonneg (show 0 ≤ 20000-x by omega) (show 0 ≤ 20000-y by omega)
  have h2 := Int.mul_nonneg (show 0 ≤ 20000+x by omega) (show 0 ≤ 20000+y by omega)
  have h3 := Int.mul_nonneg (show 0 ≤ 20000-x by omega) (show 0 ≤ 20000+y by omega)
  have h4 := Int.mul_nonneg (show 0 ≤ 20000+x by omega) (show 0 ≤ 20000-y by omega)
  have he1 : (20000-x)*(20000-y)+(20000+x)*(20000+y) = 800000000+2*(x*y) := by grind
  have he2 : (20000-x)*(20000+y)+(20000+x)*(20000-y) = 800000000-2*(x*y) := by grind
  omega

private theorem perm_length (l l1 : List point) (hp : PointPermutation l l1) : Zlength l = Zlength l1 :=
  congrArg Int.ofNat hp.length_eq

private theorem bound_head (p : point) (l : List point) (h : PointCoordsBound (p::l)) : CoordInBounds (point_x p) ∧ CoordInBounds (point_y p) := by
  cases h with | cons hp _ => exact hp

private theorem bound_tail (p : point) (l : List point) (h : PointCoordsBound (p::l)) : PointCoordsBound l := by
  cases h with | cons _ ht => exact ht

theorem proof_of_cmp_polar_values_safety_wit_1 : cmp_polar_values_safety_wit_1 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  have h1 := coord_product (a_x_pre-gx_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h2 := coord_product (a_y_pre-gy_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h3 := coord_product (a_x_pre-gx_pre) (a_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h4 := coord_product (a_y_pre-gy_pre) (a_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h5 := coord_product (b_x_pre-gx_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h6 := coord_product (b_y_pre-gy_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  split_pures <;> dump_pre_spatial
  all_goals unfold CoordInBounds at *; simp only [INT_MAX, INT_MIN]; omega

theorem proof_of_cmp_polar_values_safety_wit_2 : cmp_polar_values_safety_wit_2 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  have h1 := coord_product (a_x_pre-gx_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h2 := coord_product (a_y_pre-gy_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h3 := coord_product (a_x_pre-gx_pre) (a_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h4 := coord_product (a_y_pre-gy_pre) (a_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h5 := coord_product (b_x_pre-gx_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h6 := coord_product (b_y_pre-gy_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  split_pures <;> dump_pre_spatial
  all_goals unfold CoordInBounds at *; simp only [INT_MAX, INT_MIN]; omega

theorem proof_of_cmp_polar_values_safety_wit_3 : cmp_polar_values_safety_wit_3 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  have h1 := coord_product (a_x_pre-gx_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h2 := coord_product (a_y_pre-gy_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h3 := coord_product (a_x_pre-gx_pre) (a_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h4 := coord_product (a_y_pre-gy_pre) (a_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h5 := coord_product (b_x_pre-gx_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h6 := coord_product (b_y_pre-gy_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  split_pures <;> dump_pre_spatial
  all_goals unfold CoordInBounds at *; simp only [INT_MAX, INT_MIN]; omega

theorem proof_of_cmp_polar_values_safety_wit_4 : cmp_polar_values_safety_wit_4 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  have h1 := coord_product (a_x_pre-gx_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h2 := coord_product (a_y_pre-gy_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h3 := coord_product (a_x_pre-gx_pre) (a_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h4 := coord_product (a_y_pre-gy_pre) (a_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h5 := coord_product (b_x_pre-gx_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h6 := coord_product (b_y_pre-gy_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  split_pures <;> dump_pre_spatial
  all_goals unfold CoordInBounds at *; simp only [INT_MAX, INT_MIN]; omega

theorem proof_of_cmp_polar_values_safety_wit_5 : cmp_polar_values_safety_wit_5 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  have h1 := coord_product (a_x_pre-gx_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h2 := coord_product (a_y_pre-gy_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h3 := coord_product (a_x_pre-gx_pre) (a_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h4 := coord_product (a_y_pre-gy_pre) (a_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h5 := coord_product (b_x_pre-gx_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h6 := coord_product (b_y_pre-gy_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  split_pures <;> dump_pre_spatial
  all_goals unfold CoordInBounds at *; simp only [INT_MAX, INT_MIN]; omega

theorem proof_of_cmp_polar_values_safety_wit_6 : cmp_polar_values_safety_wit_6 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  have h1 := coord_product (a_x_pre-gx_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h2 := coord_product (a_y_pre-gy_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h3 := coord_product (a_x_pre-gx_pre) (a_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h4 := coord_product (a_y_pre-gy_pre) (a_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h5 := coord_product (b_x_pre-gx_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h6 := coord_product (b_y_pre-gy_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  split_pures <;> dump_pre_spatial
  all_goals unfold CoordInBounds at *; simp only [INT_MAX, INT_MIN]; omega

theorem proof_of_cmp_polar_values_safety_wit_7 : cmp_polar_values_safety_wit_7 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  have h1 := coord_product (a_x_pre-gx_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h2 := coord_product (a_y_pre-gy_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h3 := coord_product (a_x_pre-gx_pre) (a_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h4 := coord_product (a_y_pre-gy_pre) (a_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h5 := coord_product (b_x_pre-gx_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h6 := coord_product (b_y_pre-gy_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  split_pures <;> dump_pre_spatial
  all_goals unfold CoordInBounds at *; simp only [INT_MAX, INT_MIN]; omega

theorem proof_of_cmp_polar_values_safety_wit_8 : cmp_polar_values_safety_wit_8 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  have h1 := coord_product (a_x_pre-gx_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h2 := coord_product (a_y_pre-gy_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h3 := coord_product (a_x_pre-gx_pre) (a_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h4 := coord_product (a_y_pre-gy_pre) (a_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h5 := coord_product (b_x_pre-gx_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h6 := coord_product (b_y_pre-gy_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  split_pures <;> dump_pre_spatial
  all_goals unfold CoordInBounds at *; simp only [INT_MAX, INT_MIN]; omega

theorem proof_of_cmp_polar_values_safety_wit_9 : cmp_polar_values_safety_wit_9 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  have h1 := coord_product (a_x_pre-gx_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h2 := coord_product (a_y_pre-gy_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h3 := coord_product (a_x_pre-gx_pre) (a_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h4 := coord_product (a_y_pre-gy_pre) (a_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h5 := coord_product (b_x_pre-gx_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h6 := coord_product (b_y_pre-gy_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  split_pures <;> dump_pre_spatial
  all_goals unfold CoordInBounds at *; simp only [INT_MAX, INT_MIN]; omega

theorem proof_of_cmp_polar_values_safety_wit_10 : cmp_polar_values_safety_wit_10 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  have h1 := coord_product (a_x_pre-gx_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h2 := coord_product (a_y_pre-gy_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h3 := coord_product (a_x_pre-gx_pre) (a_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h4 := coord_product (a_y_pre-gy_pre) (a_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h5 := coord_product (b_x_pre-gx_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h6 := coord_product (b_y_pre-gy_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  split_pures <;> dump_pre_spatial
  all_goals unfold CoordInBounds at *; simp only [INT_MAX, INT_MIN]; omega

theorem proof_of_cmp_polar_values_safety_wit_11 : cmp_polar_values_safety_wit_11 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  have h1 := coord_product (a_x_pre-gx_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h2 := coord_product (a_y_pre-gy_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h3 := coord_product (a_x_pre-gx_pre) (a_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h4 := coord_product (a_y_pre-gy_pre) (a_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h5 := coord_product (b_x_pre-gx_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h6 := coord_product (b_y_pre-gy_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  split_pures <;> dump_pre_spatial
  all_goals unfold CoordInBounds at *; simp only [INT_MAX, INT_MIN]; omega

theorem proof_of_cmp_polar_values_safety_wit_12 : cmp_polar_values_safety_wit_12 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  have h1 := coord_product (a_x_pre-gx_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h2 := coord_product (a_y_pre-gy_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h3 := coord_product (a_x_pre-gx_pre) (a_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h4 := coord_product (a_y_pre-gy_pre) (a_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h5 := coord_product (b_x_pre-gx_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h6 := coord_product (b_y_pre-gy_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  split_pures <;> dump_pre_spatial
  all_goals unfold CoordInBounds at *; simp only [INT_MAX, INT_MIN]; omega

theorem proof_of_cmp_polar_values_safety_wit_13 : cmp_polar_values_safety_wit_13 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  have h1 := coord_product (a_x_pre-gx_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h2 := coord_product (a_y_pre-gy_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h3 := coord_product (a_x_pre-gx_pre) (a_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h4 := coord_product (a_y_pre-gy_pre) (a_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h5 := coord_product (b_x_pre-gx_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h6 := coord_product (b_y_pre-gy_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  split_pures <;> dump_pre_spatial
  all_goals unfold CoordInBounds at *; simp only [INT_MAX, INT_MIN]; omega

theorem proof_of_cmp_polar_values_return_wit_1 : cmp_polar_values_return_wit_1 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have hx : a_x_pre = b_x_pre := by omega
  subst b_x_pre
  have hy : a_y_pre = b_y_pre := by omega
  subst b_y_pre
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_2 : cmp_polar_values_return_wit_2 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have hx : a_x_pre = b_x_pre := by omega
  subst b_x_pre
  have hy : a_y_pre = b_y_pre := by omega
  subst b_y_pre
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_3 : cmp_polar_values_return_wit_3 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have hx : a_x_pre = b_x_pre := by omega
  subst b_x_pre
  have hy : a_y_pre = b_y_pre := by omega
  subst b_y_pre
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_4 : cmp_polar_values_return_wit_4 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hx : a_x_pre = b_x_pre := by omega
  subst b_x_pre
  have hy : a_y_pre = b_y_pre := by omega
  subst b_y_pre
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_5 : cmp_polar_values_return_wit_5 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have hx : a_x_pre = b_x_pre := by omega
  subst b_x_pre
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_6 : cmp_polar_values_return_wit_6 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hx : a_x_pre = b_x_pre := by omega
  subst b_x_pre
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_7_split_goal_1 : cmp_polar_values_return_wit_7_split_goal_1 := by
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hx : a_x_pre = b_x_pre := by omega
  subst b_x_pre
  simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  grind (splits := 40)

theorem proof_of_cmp_polar_values_return_wit_7 : cmp_polar_values_return_wit_7 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hx : a_x_pre = b_x_pre := by omega
  subst b_x_pre
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_8 : cmp_polar_values_return_wit_8 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hx : a_x_pre = b_x_pre := by omega
  subst b_x_pre
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_9 : cmp_polar_values_return_wit_9 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hx : a_x_pre = b_x_pre := by omega
  subst b_x_pre
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_10 : cmp_polar_values_return_wit_10 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hx : a_x_pre = b_x_pre := by omega
  subst b_x_pre
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_11 : cmp_polar_values_return_wit_11 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_12 : cmp_polar_values_return_wit_12 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_13 : cmp_polar_values_return_wit_13 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_14 : cmp_polar_values_return_wit_14 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_15 : cmp_polar_values_return_wit_15 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_16 : cmp_polar_values_return_wit_16 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_17 : cmp_polar_values_return_wit_17 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_18 : cmp_polar_values_return_wit_18 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_19 : cmp_polar_values_return_wit_19 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_20 : cmp_polar_values_return_wit_20 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_21 : cmp_polar_values_return_wit_21 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_22 : cmp_polar_values_return_wit_22 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_23 : cmp_polar_values_return_wit_23 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_24 : cmp_polar_values_return_wit_24 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_25 : cmp_polar_values_return_wit_25 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_26 : cmp_polar_values_return_wit_26 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_27 : cmp_polar_values_return_wit_27 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_28 : cmp_polar_values_return_wit_28 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_29 : cmp_polar_values_return_wit_29 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_30 : cmp_polar_values_return_wit_30 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_31 : cmp_polar_values_return_wit_31 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_32 : cmp_polar_values_return_wit_32 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_33 : cmp_polar_values_return_wit_33 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_34 : cmp_polar_values_return_wit_34 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_35 : cmp_polar_values_return_wit_35 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_36 : cmp_polar_values_return_wit_36 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_37 : cmp_polar_values_return_wit_37 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_38 : cmp_polar_values_return_wit_38 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_39 : cmp_polar_values_return_wit_39 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_40 : cmp_polar_values_return_wit_40 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_41 : cmp_polar_values_return_wit_41 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_42 : cmp_polar_values_return_wit_42 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_43 : cmp_polar_values_return_wit_43 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_44 : cmp_polar_values_return_wit_44 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_45 : cmp_polar_values_return_wit_45 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_46 : cmp_polar_values_return_wit_46 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_47 : cmp_polar_values_return_wit_47 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_48 : cmp_polar_values_return_wit_48 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_49 : cmp_polar_values_return_wit_49 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_50 : cmp_polar_values_return_wit_50 := by
  right
  intro b_y_pre b_x_pre a_y_pre a_x_pre gy_pre gx_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind (splits := 40))

theorem proof_of_swap_points_return_wit_1 : swap_points_return_wit_1 := by
  right
  intro j_pre i_pre n_pre pts_l flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have hi : 0 ≤ i_pre ∧ i_pre < Zlength pts_l := by omega
  have hj : 0 ≤ j_pre ∧ j_pre < Zlength pts_l := by omega
  have hp := PointPermutation_swap_points_any pts_l i_pre j_pre hi hj
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact PointCoordsBound_permutation _ _ hp PreH9
      | exact hp
      | exact FlatPoints_swap_points flat pts_l i_pre j_pre PreH8 hi hj
      | exact point_swap_flat_preprocess_form flat n_pre i_pre j_pre (by have := PreH8.1; omega) (by omega) (by omega)

theorem proof_of_partition_points_entail_wit_1 : partition_points_entail_wit_1 := by
  right
  intro gy_pre gx_pre high_pre low_pre n_pre pts_l flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have hp := flat_points_lookup_point flat pts_l high_pre (by omega) PreH7
  Exists pts_l
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try first | assumption | omega
    · refine ⟨List.Perm.refl _, PointSameOutsideRange_refl _ _ _, hp.symm, ?_, ?_⟩
      · intro k hk; omega
      · intro k hk; omega
    · exact bound_tail _ _ PreH8

theorem proof_of_partition_points_entail_wit_2_1 : partition_points_entail_wit_2_1 := by
  right
  intro gy_pre gx_pre high_pre low_pre n_pre pts_l pivot_x pivot_y j i retval flat_cur_2 pts_cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have hj : 0 ≤ j ∧ j < Zlength pts_cur_2 := by omega
  have hi : 0 ≤ i+1 ∧ i+1 < Zlength pts_cur_2 := by omega
  have hh : 0 ≤ high_pre ∧ high_pre < Zlength pts_cur_2 := by omega
  have hpt := FlatPoints_Znth_point flat_cur_2 pts_cur_2 j PreH20 hj
  have hle := PolarCmpResult_nonpos_le _ _ _ _ PreH5 PreH4
  rw [← hpt] at hle
  have hpiv := Znth_point_swap_points_other pts_cur_2 (i+1) j high_pre default_point hi hj hh (by omega) (by omega)
  have hscan : PointPartitionScanInv (mk_point gx_pre gy_pre) pts_l (point_swap_points pts_cur_2 (i+1) j) low_pre high_pre (mk_point pivot_x pivot_y) (i+1) (j+1) := by
    refine ⟨PreH23.1.trans PreH2, ?_, hpiv.trans PreH23.2.2.1, ?_, ?_⟩
    · exact PointSameOutsideRange_trans _ _ _ _ _ PreH23.2.1 (PointSameOutsideRange_swap_inside _ _ _ _ _ PreH9 (by omega) (by omega) (by omega))
    · intro k hk
      by_cases he : k = i+1
      · subst k; rw [Znth_point_swap_points_left _ _ _ _ hi hj]; exact hle
      · rw [Znth_point_swap_points_other _ _ _ _ _ hi hj (by omega) he (by omega)]
        exact PreH23.2.2.2.1 k (by omega)
    · intro k hk
      by_cases he : k = j
      · subst k; rw [Znth_point_swap_points_right _ _ _ _ hi hj]
        exact PreH23.2.2.2.2 (i+1) (by omega)
      · rw [Znth_point_swap_points_other _ _ _ _ _ hi hj (by omega) (by omega) he]
        exact PreH23.2.2.2.2 k (by omega)
  Exists (point_swap_points pts_cur_2 (i+1) j)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try first | assumption | omega
    all_goals first
      | (rw [Zlength_point_swap_points]; omega)
      | exact PreH19.trans hpiv.symm
      | exact Forall.cons (bound_head _ _ PreH22) PreH3

theorem proof_of_partition_points_entail_wit_2_2 : partition_points_entail_wit_2_2 := by
  right
  intro gy_pre gx_pre high_pre low_pre n_pre pts_l pivot_x pivot_y j i retval flat_cur_2 pts_cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have he : retval = 1 := by omega
  rw [he] at PreH2
  have hp := FlatPoints_Znth_point flat_cur_2 pts_cur_2 j PreH17 (by omega)
  have hlt := PolarCmpResult_one_implies_PolarLt_flip _ _ _ PreH2
  rw [← hp] at hlt
  have hscan : PointPartitionScanInv (mk_point gx_pre gy_pre) pts_l pts_cur_2 low_pre high_pre (mk_point pivot_x pivot_y) i (j+1) := by
    refine ⟨PreH20.1, PreH20.2.1, PreH20.2.2.1, PreH20.2.2.2.1, ?_⟩
    intro k hk
    by_cases he : k = j
    · subst k; exact hlt
    · exact PreH20.2.2.2.2 k (by omega)
  Exists pts_cur_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try first | assumption | omega

theorem proof_of_partition_points_return_wit_1 : partition_points_return_wit_1 := by
  right
  intro gy_pre gx_pre high_pre low_pre n_pre pts_l pivot_x pivot_y j i flat_cur pts_cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have he : j = high_pre := by omega
  subst j
  have hp := PointPartitionedAt_after_final_swap _ pts_l pts_cur low_pre high_pre (mk_point pivot_x pivot_y) i PreH5 (by omega) PreH10 (by omega) PreH19
  have hs := PointSameOutsideRange_trans _ _ _ _ _ PreH19.2.1
    (PointSameOutsideRange_swap_inside pts_cur low_pre high_pre (i+1) high_pre PreH5 (by omega) (by omega) (by omega))
  have hperm := PreH19.1.trans PreH2
  Exists (point_swap_points pts_cur (i+1) high_pre)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try first | assumption | omega
    exact Forall.cons (bound_head _ _ PreH18) PreH3

theorem proof_of_partition_points_partial_solve_wit_5_pure : partition_points_partial_solve_wit_5_pure := by
  right
  intro gy_pre gx_pre high_pre low_pre n_pre coords_pre pts_l flat_cur pivot_x pivot_y pts_cur j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  have hg := bound_head _ _ PreH37
  have hj := point_coords_bound_lookup pts_cur j (by omega) PreH36
  have hp := point_coords_bound_lookup pts_cur high_pre (by omega) PreH36
  have hpt := flat_points_lookup_point flat_cur pts_cur j (by omega) PreH35
  rw [← PreH34] at hp
  rw [← hpt] at hj
  change CoordInBounds gx_pre ∧ CoordInBounds gy_pre at hg
  change CoordInBounds pivot_x ∧ CoordInBounds pivot_y at hp
  change CoordInBounds (Znth (2*j) flat_cur 0) ∧ CoordInBounds (Znth (2*j+1) flat_cur 0) at hj
  split_pures <;> dump_pre_spatial
  all_goals first | exact hg.1 | exact hg.2 | exact hj.1 | exact hj.2 | exact hp.1 | exact hp.2

theorem proof_of_quicksort_points_range_entail_wit_1 : quicksort_points_range_entail_wit_1 := by
  right
  intro gy_pre gx_pre right_pre left_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  obtain ⟨pts, hn, hf, hb⟩ := PreH7
  Exists pts
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> assumption

theorem proof_of_quicksort_points_range_return_wit_4 : quicksort_points_range_return_wit_4 := by
  right
  intro gy_pre gx_pre right_pre left_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  obtain ⟨pts, hn, hf, hb⟩ := PreH7
  Exists pts
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try assumption
    intro pts_in hf' hb'
    have he := FlatPoints_functional flat pts_in pts hf' hf
    subst pts_in
    exact ⟨List.Perm.refl _, PointSameOutsideRange_refl _ _ _, PointSortedRange_degenerate _ _ _ _ PreH1⟩

theorem proof_of_quicksort_points_range_return_wit_3 : quicksort_points_range_return_wit_3 := by
  right
  intro gy_pre gx_pre right_pre left_pre n_pre flat pts_l flat_out_2 pts_out_2 retval flat_out_3 pts_out_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  obtain ⟨hp, hs, hsort⟩ := PreH4 pts_out_2 PreH8 PreH9
  have hn2 : Zlength pts_out_2 = n_pre := by have := perm_length _ _ PreH10; omega
  have hn3 : Zlength pts_out_3 = n_pre := by have := perm_length _ _ hp; omega
  have hpart := PointPartitionedAt_preserved_by_left _ _ _ _ _ _ hp PreH15 hs (by omega) PreH12
  have hsorted := PointSortedRange_from_left_boundary _ _ _ _ _ PreH15 PreH1 (by omega) hpart hsort
  Exists pts_out_3
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try assumption
    intro pts_in hf hb
    have he := FlatPoints_functional flat pts_in pts_l hf PreH20
    subst pts_in
    refine ⟨PreH10.trans hp, ?_, hsorted⟩
    exact PointSameOutsideRange_trans _ _ _ _ _ PreH11
      (PointSameOutsideRange_weaken _ _ _ _ _ _ (by omega) (by omega) hs)

theorem proof_of_quicksort_points_range_return_wit_1 : quicksort_points_range_return_wit_1 := by
  right
  intro gy_pre gx_pre right_pre left_pre n_pre flat pts_l flat_out_2 pts_out_2 retval flat_out_3 pts_out_3 flat_out_4 pts_out_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  obtain ⟨hp23, hs23, hsort23⟩ := PreH7 pts_out_2 PreH11 PreH12
  obtain ⟨hp34, hs34, hsort34⟩ := PreH3 pts_out_3 PreH5 PreH6
  have hn2 : Zlength pts_out_2 = n_pre := by have := perm_length _ _ PreH13; omega
  have hn3 : Zlength pts_out_3 = n_pre := by have := perm_length _ _ hp23; omega
  have hn4 : Zlength pts_out_4 = n_pre := by have := perm_length _ _ hp34; omega
  have hpart3 := PointPartitionedAt_preserved_by_left _ _ _ _ _ _ hp23 PreH18 hs23 (by omega) PreH15
  have hpart4 := PointPartitionedAt_preserved_by_right _ _ _ _ _ _ hp34 PreH18 hs34 (by omega) hpart3
  have hleft : PointSortedRange (mk_point gx_pre gy_pre) pts_out_4 left_pre (retval-1) := by
    apply PointSortedRange_ext _ pts_out_3 _ _ _ PreH18 (by omega) (by omega) _ hsort23
    intro k hk
    exact hs34.2 k (by omega) (Or.inl (by omega))
  have hsorted := PointSortedRange_from_middle_partition _ _ _ _ _ PreH18 PreH8 PreH4 (by omega) hpart4 hleft hsort34
  Exists pts_out_4
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try assumption
    intro pts_in hf hb
    have he := FlatPoints_functional flat pts_in pts_l hf PreH23
    subst pts_in
    refine ⟨PreH13.trans (hp23.trans hp34), ?_, hsorted⟩
    apply PointSameOutsideRange_trans _ pts_out_3 _ _ _
    · exact PointSameOutsideRange_trans _ _ _ _ _ PreH14
        (PointSameOutsideRange_weaken _ _ _ _ _ _ (by omega) (by omega) hs23)
    · exact PointSameOutsideRange_weaken _ _ _ _ _ _ (by omega) (by omega) hs34

theorem proof_of_quicksort_points_range_return_wit_2 : quicksort_points_range_return_wit_2 := by
  right
  intro gy_pre gx_pre right_pre left_pre n_pre flat pts_l flat_out_2 pts_out_2 retval flat_out_3 pts_out_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  obtain ⟨hp, hs, hsort⟩ := PreH3 pts_out_2 PreH8 PreH9
  have hn2 : Zlength pts_out_2 = n_pre := by have := perm_length _ _ PreH10; omega
  have hn3 : Zlength pts_out_3 = n_pre := by have := perm_length _ _ hp; omega
  have hpart := PointPartitionedAt_preserved_by_right _ _ _ _ _ _ hp PreH15 hs (by omega) PreH12
  have hsorted := PointSortedRange_from_right_boundary _ _ _ _ _ PreH15 PreH5 (by omega) hpart hsort
  Exists pts_out_3
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try assumption
    intro pts_in hf hb
    have he := FlatPoints_functional flat pts_in pts_l hf PreH20
    subst pts_in
    refine ⟨PreH10.trans hp, ?_, hsorted⟩
    exact PointSameOutsideRange_trans _ _ _ _ _ PreH11
      (PointSameOutsideRange_weaken _ _ _ _ _ _ (by omega) (by omega) hs)

theorem proof_of_quicksort_points_range_partial_solve_wit_2_pure : quicksort_points_range_partial_solve_wit_2_pure := by
  right
  intro gy_pre gx_pre right_pre left_pre n_pre coords_pre flat pts_l flat_out pts_out retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  have hn : Zlength pts_out = n_pre := by have := perm_length _ _ PreH18; omega
  dump_pre_spatial
  exact ⟨pts_out, hn, PreH16, PreH17⟩

theorem proof_of_quicksort_points_range_partial_solve_wit_3_pure : quicksort_points_range_partial_solve_wit_3_pure := by
  right
  intro gy_pre gx_pre right_pre left_pre n_pre coords_pre flat pts_l flat_out_2 pts_out retval flat_out pts_out_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  have hp := (PreH16 pts_out PreH20 PreH21).1
  have hn : Zlength pts_out_2 = n_pre := by have := perm_length _ _ (PreH22.trans hp); omega
  dump_pre_spatial
  exact ⟨pts_out_2, hn, PreH14, PreH15⟩

theorem proof_of_quicksort_points_range_partial_solve_wit_4_pure : quicksort_points_range_partial_solve_wit_4_pure := by
  right
  intro gy_pre gx_pre right_pre left_pre n_pre coords_pre flat pts_l flat_out pts_out retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have hn : Zlength pts_out = n_pre := by have := perm_length _ _ PreH19; omega
  dump_pre_spatial
  exact ⟨pts_out, hn, PreH17, PreH18⟩

theorem proof_of_sort_return_wit_1 : sort_return_wit_1 := by
  right
  intro n_pre gy gx pts_l flat flat_out_2 pts_out_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  obtain ⟨hp, hs, hsort⟩ := PreH3 pts_l PreH7 PreH8
  have hn : Zlength pts_out_2 = n_pre := by have := perm_length _ _ hp; omega
  Exists pts_out_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try first | assumption
    intro i j hi hij hj
    exact hsort i j hi hij (by omega)

theorem proof_of_sort_partial_solve_wit_1_pure : sort_partial_solve_wit_1_pure := by
  right
  intro n_pre pts_pre gy gx pts_l flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  dump_pre_spatial
  exact ⟨pts_l, PreH9, PreH10, PreH11⟩

end Algorithms.sort_point.lean.groundtruth.sort_point_proof_manual
