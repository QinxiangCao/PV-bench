import SimpleC.EE.LLM_bench.Algorithms.sort_point.sort_point_goal
import SimpleC.EE.LLM_bench.Algorithms.sort_point.sort_point_proof_auto

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.sort_point.sort_point_proof_manual
open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open sort_point_goal sort_point_lib
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

end SimpleC.EE.LLM_bench.Algorithms.sort_point.sort_point_proof_manual
