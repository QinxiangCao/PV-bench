import Algorithms.discretize.lean.groundtruth.discretize_goal
import Algorithms.discretize.lean.groundtruth.discretize_proof_auto
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import SimpleC.EE.LLM_bench.Algorithms.quicksort_hoare_swap_index.quicksort_lib

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace Algorithms.discretize.lean.groundtruth.discretize_proof_manual

open Algorithms.discretize.lean

open AUXLib
open SimpleC.EE.LLM_bench.Algorithms.quicksort_hoare_swap_index.quicksort_lib

theorem same_outside_range_refl__partition_scan (l : List Int) (left right : Int) :
    same_outside_range l l left right := ⟨rfl, by intros; rfl⟩

theorem same_outside_range_swap_inside__partition_scan (l l1 : List Int) (low high i j : Int)
    (hs : same_outside_range l l1 low high) (hi : low ≤ i ∧ i ≤ high) (hj : low ≤ j ∧ j ≤ high)
    (hir : 0 ≤ i ∧ i < Zlength l1) (hjr : 0 ≤ j ∧ j < Zlength l1) :
    same_outside_range l (replace_Znth j (Znth i l1 0) (replace_Znth i (Znth j l1 0) l1)) low high := by
  refine ⟨by simpa only [Zlength_replace_Znth] using hs.1, ?_⟩
  intro k hk ho
  have hl := hs.1
  rw [Znth_replace_Znth_Diff 0 _ j k _ (by simpa only [Zlength_replace_Znth] using hjr)
    (by simp only [Zlength_replace_Znth]; omega) (by omega),
    Znth_replace_Znth_Diff 0 l1 i k _ hir (by omega) (by omega)]
  exact hs.2 k hk ho

theorem replace_Znth_swap_form__partition_scan (l1 l2 l3 : List Int) (xi xj : Int) :
    replace_Znth (Zlength l1+1+Zlength l2) xi
      (replace_Znth (Zlength l1) xj (l1 ++ (xi :: (l2 ++ (xj :: l3)))) ) =
        l1 ++ (xj :: (l2 ++ (xi :: l3))) := by
  rw [Sorting.replace_Znth_boundary_local]
  have hlen1 := Zlength_nonneg l1
  have hlen2 := Zlength_nonneg l2
  rw [replace_Znth_app_r (Zlength l1+1+Zlength l2) xi l1 (xj::(l2++(xj::l3))) (by omega),
    replace_Znth_nothing (Zlength l1+1+Zlength l2) l1 xi (by omega)]
  rw [show Zlength l1+1+Zlength l2-Zlength l1 = Zlength l2+1 by omega,
    replace_Znth_cons (Zlength l2+1) xi xj (l2++(xj::l3)) (by omega)]
  simp only [Int.add_sub_cancel, Sorting.replace_Znth_boundary_local]

theorem permutation_swap_Znth_lt__partition_scan (l : List Int) (i j d : Int)
    (h : 0 ≤ i ∧ i < j ∧ j < Zlength l) :
    permutation l (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)) :=
  SimpleC.EE.LLM_bench.Algorithms.selection_sort.selection_sort_lib.permutation_swap_Znth_lt l i j d h

theorem replace_nth_comm_Z__partition_scan (ni nj : Nat) (l : List Int) (a b : Int) (hne : ni ≠ nj) :
    replace_nth nj (replace_nth ni l a) b = replace_nth ni (replace_nth nj l b) a := by
  induction l generalizing ni nj with
  | nil => cases ni <;> cases nj <;> rfl
  | cons x l ih =>
    cases ni with
    | zero => cases nj with
      | zero => omega
      | succ nj => rfl
    | succ ni => cases nj with
      | zero => rfl
      | succ nj => exact congrArg (List.cons x) (ih ni nj (by omega))

theorem replace_Znth_comm__partition_scan (l : List Int) (i j a b : Int)
    (hi : 0 ≤ i) (hj : 0 ≤ j) (hne : i ≠ j) :
    replace_Znth j b (replace_Znth i a l) = replace_Znth i a (replace_Znth j b l) :=
  replace_nth_comm_Z__partition_scan i.toNat j.toNat l a b (by omega)

theorem permutation_swap_Znth__partition_scan (l : List Int) (i j d : Int)
    (hi : 0 ≤ i ∧ i < Zlength l) (hj : 0 ≤ j ∧ j < Zlength l) :
    permutation l (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)) := by
  by_cases he : i=j
  · subst j
    rw [replace_Znth_Znth, replace_Znth_Znth]
    exact List.Perm.refl l
  · by_cases hlt : i<j
    · exact permutation_swap_Znth_lt__partition_scan l i j d (by omega)
    · rw [replace_Znth_comm__partition_scan l i j _ _ hi.1 hj.1 he]
      exact permutation_swap_Znth_lt__partition_scan l j i d (by omega)

theorem partition_scan_inv_init__partition_scan (l : List Int) (low high : Int)
    (hlo : 0 ≤ low) (hh : low ≤ high) :
    partition_scan_inv l l low high (Znth high l 0) (low-1) low :=
  ⟨List.Perm.refl l, same_outside_range_refl__partition_scan l low high, rfl,
    by intro k hk; omega, by intro k hk; omega⟩

theorem partition_scan_inv_step_gt__partition_scan (l l1 : List Int) (low high pivot i j : Int)
    (hgt : pivot < Znth j l1 0) (hj : j < high) (hs : partition_scan_inv l l1 low high pivot i j) :
    partition_scan_inv l l1 low high pivot i (j+1) := by
  refine ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_⟩
  intro k hk
  by_cases he : k=j
  · simpa only [he] using hgt
  · exact hs.2.2.2.2 k (by omega)

theorem Forall_sublist_by_Znth__partition_scan (P : Int → Prop) (l : List Int) (lo hi : Int)
    (hlo : 0 ≤ lo ∧ lo ≤ hi) (hhi : hi ≤ Zlength l)
    (h : ∀ k, (lo ≤ k ∧ k < hi) → P (Znth k l 0)) : Forall P (sublist lo hi l) :=
  Forall_sublist_by_Znth_local P l lo hi hlo hhi h

theorem same_outside_range_refl__quicksort_range (l : List Int) (left right : Int) :
    same_outside_range l l left right := same_outside_range_refl__partition_scan l left right

theorem same_outside_range_trans__quicksort_range (l l1 l2 : List Int) (left right : Int)
    (h : same_outside_range l l1 left right) (h1 : same_outside_range l1 l2 left right) :
    same_outside_range l l2 left right := same_outside_range_trans_local l l1 l2 left right h h1

theorem same_outside_range_weaken__quicksort_range (l l1 : List Int) (left1 right1 left2 right2 : Int)
    (hl : left2 ≤ left1) (hr : right1 ≤ right2) (h : same_outside_range l l1 left1 right1) :
    same_outside_range l l1 left2 right2 := same_outside_range_weaken_local l l1 left1 right1 left2 right2 hl hr h

theorem Forall_permutation__quicksort_range (P : Int → Prop) (l1 l2 : List Int)
    (hp : permutation l1 l2) (h : Forall P l1) : Forall P l2 := h.perm hp

theorem Forall_Znth__quicksort_range (P : Int → Prop) (l : List Int) (i d : Int)
    (hp : Forall P l) (hi : 0 ≤ i ∧ i < Zlength l) : P (Znth i l d) := by
  have hin : i.toNat < l.length := by simp only [Zlength, Int.ofNat_eq_coe] at hi; omega
  have h := hp.mem (List.getElem_mem (l := l) hin)
  simpa only [Znth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hin, Option.getD_some] using h

theorem sublist_eq_from_Znth__quicksort_range (l1 l2 : List Int) (lo hi : Int)
    (hlen : Zlength l1 = Zlength l2) (hlo : 0 ≤ lo ∧ lo ≤ hi) (hhi : hi ≤ Zlength l1)
    (h : ∀ k, (lo ≤ k ∧ k < hi) → Znth k l1 0 = Znth k l2 0) :
    sublist lo hi l1 = sublist lo hi l2 := sublist_eq_from_Znth_local l1 l2 lo hi hlen hlo hhi h

theorem list_decompose_sublist__quicksort_range (l : List Int) (lo hi : Int)
    (hlo : 0 ≤ lo ∧ lo ≤ hi) (hhi : hi ≤ Zlength l) :
    l = sublist 0 lo l ++ (sublist lo hi l ++ sublist hi (Zlength l) l) :=
  list_decompose_sublist_local l lo hi hlo hhi

theorem same_outside_range_prefix__quicksort_range (l l1 : List Int) (left right : Int)
    (h : same_outside_range l l1 left right) (hl : 0 ≤ left ∧ left ≤ Zlength l) :
    sublist 0 left l1 = sublist 0 left l := same_outside_range_prefix_local l l1 left right h hl

theorem same_outside_range_suffix__quicksort_range (l l1 : List Int) (left right : Int)
    (h : same_outside_range l l1 left right) (hr : 0 ≤ right+1 ∧ right+1 ≤ Zlength l) :
    sublist (right+1) (Zlength l1) l1 = sublist (right+1) (Zlength l) l := same_outside_range_suffix_local l l1 left right h hr

theorem middle_permutation_of_same_outside__quicksort_range (l l1 : List Int) (left right : Int)
    (hp : permutation l l1) (h : same_outside_range l l1 left right)
    (hl : 0 ≤ left ∧ left ≤ right+1) (hr : right+1 ≤ Zlength l) :
    permutation (sublist left (right+1) l) (sublist left (right+1) l1) :=
  middle_permutation_of_same_outside_local l l1 left right hp h hl hr

theorem Forall_sublist_by_Znth__quicksort_range (P : Int → Prop) (l : List Int) (lo hi : Int)
    (hlo : 0 ≤ lo ∧ lo ≤ hi) (hhi : hi ≤ Zlength l)
    (h : ∀ k, (lo ≤ k ∧ k < hi) → P (Znth k l 0)) : Forall P (sublist lo hi l) :=
  Forall_sublist_by_Znth_local P l lo hi hlo hhi h

theorem partitioned_at_preserved_by_left__quicksort_range (l l1 : List Int) (left right p : Int)
    (hp : Permutation l l1) (hl : 0 ≤ left) (h : same_outside_range l l1 left (p - 1))
    (hr : right < Zlength l) (hpart : partitioned_at l left right p) : partitioned_at l1 left right p := by
  have heq := h.2 p (by have := hpart.1; omega) (Or.inr (by omega))
  refine ⟨hpart.1, ?_, ?_⟩
  · rw [heq]
    have hm := middle_permutation_of_same_outside_local l l1 left (p - 1) hp h (by have := hpart.1; omega) (by have := hpart.1; omega)
    simp only [Int.sub_add_cancel] at hm
    exact Forall_permutation_local _ _ _ hm hpart.2.1
  · rw [heq]
    have hs : sublist (p + 1) (right + 1) l1 = sublist (p + 1) (right + 1) l := by
      apply sublist_eq_from_Znth_local l1 l _ _ h.1.symm (by have := hpart.1; omega) (by have := h.1; omega)
      intro k hk; exact h.2 k (by have := hpart.1; omega) (Or.inr (by omega))
    rw [hs]; exact hpart.2.2

theorem partitioned_at_preserved_by_right__quicksort_range (l l1 : List Int) (left right p : Int)
    (hp : Permutation l l1) (hl : 0 ≤ left) (h : same_outside_range l l1 (p + 1) right)
    (hr : right < Zlength l) (hpart : partitioned_at l left right p) : partitioned_at l1 left right p := by
  have heq := h.2 p (by have := hpart.1; omega) (Or.inl (by omega))
  refine ⟨hpart.1, ?_, ?_⟩
  · rw [heq]
    have hs : sublist left p l1 = sublist left p l := by
      apply sublist_eq_from_Znth_local l1 l _ _ h.1.symm (by have := hpart.1; omega) (by have := h.1; have := hpart.1; omega)
      intro k hk; exact h.2 k (by have := hpart.1; omega) (Or.inl (by omega))
    rw [hs]; exact hpart.2.1
  · rw [heq]
    exact Forall_permutation_local _ _ _ (middle_permutation_of_same_outside_local l l1 (p + 1) right hp h (by have := hpart.1; omega) (by omega)) hpart.2.2

private theorem read_swap (l : List Int) (i j k : Int)
    (hi : 0 ≤ i ∧ i < Zlength l) (hj : 0 ≤ j ∧ j < Zlength l) (hk : 0 ≤ k ∧ k < Zlength l) :
    Znth k (replace_Znth j (Znth i l 0) (replace_Znth i (Znth j l 0) l)) 0 =
      if k=j then Znth i l 0 else if k=i then Znth j l 0 else Znth k l 0 := by
  by_cases hkj : k=j
  · subst k
    rw [if_pos rfl, Znth_replace_Znth_Same 0 _ j _ (by simpa only [Zlength_replace_Znth] using hj)]
  · rw [if_neg hkj, Znth_replace_Znth_Diff 0 _ j k _ (by simpa only [Zlength_replace_Znth] using hj)
      (by simpa only [Zlength_replace_Znth] using hk) (Ne.symm hkj)]
    by_cases hki : k=i
    · subst k
      rw [if_pos rfl, Znth_replace_Znth_Same 0 l i _ hi]
    · rw [if_neg hki, Znth_replace_Znth_Diff 0 l i k _ hi hk (Ne.symm hki)]

theorem partition_scan_inv_step_le__partition_scan (l l1 : List Int) (low high pivot i j : Int)
    (hlo : 0 ≤ low) (hlh : low ≤ high) (hhl : high < Zlength l1) (hle : Znth j l1 0 ≤ pivot)
    (hjh : j < high) (hli : low-1 ≤ i) (hij : i < j) (hjle : j ≤ high)
    (hs : partition_scan_inv l l1 low high pivot i j) :
    partition_scan_inv l (replace_Znth j (Znth (i+1) l1 0) (replace_Znth (i+1) (Znth j l1 0) l1))
      low high pivot (i+1) (j+1) := by
  have hir : 0 ≤ i+1 ∧ i+1 < Zlength l1 := by omega
  have hjr : 0 ≤ j ∧ j < Zlength l1 := by omega
  have hread := read_swap l1 (i+1) j
  refine ⟨hs.1.trans (permutation_swap_Znth__partition_scan l1 (i+1) j 0 hir hjr),
    same_outside_range_swap_inside__partition_scan l l1 low high (i+1) j hs.2.1 (by omega) (by omega) hir hjr, ?_, ?_, ?_⟩
  · rw [hread high hir hjr (by omega), if_neg (by omega), if_neg (by omega)]
    exact hs.2.2.1
  · intro k hk
    rw [hread k hir hjr (by omega)]
    split
    · rename_i he
      have : i+1=j := by omega
      simpa only [this] using hle
    · split
      · exact hle
      · exact hs.2.2.2.1 k (by omega)
  · intro k hk
    rw [hread k hir hjr (by omega)]
    split
    · have hg := hs.2.2.2.2 (i+1) (by omega)
      exact hg
    · rw [if_neg (by omega)]
      exact hs.2.2.2.2 k (by omega)

theorem partition_scan_inv_final_swap_partitioned_at__partition_scan (l l1 : List Int) (low high pivot i j : Int)
    (hlo : 0 ≤ low) (hlh : low ≤ high) (hli : low-1 ≤ i) (hhl : high < Zlength l1)
    (hjd : j ≥ high) (hij : i < j) (hjh : j ≤ high)
    (hs : partition_scan_inv l l1 low high pivot i j) :
    partitioned_at (replace_Znth high (Znth (i+1) l1 0) (replace_Znth (i+1) (Znth high l1 0) l1)) low high (i+1) := by
  have hir : 0 ≤ i+1 ∧ i+1 < Zlength l1 := by omega
  have hhr : 0 ≤ high ∧ high < Zlength l1 := by omega
  have hread := read_swap l1 (i+1) high
  have hpiv : Znth (i+1) (replace_Znth high (Znth (i+1) l1 0) (replace_Znth (i+1) (Znth high l1 0) l1)) 0 = pivot := by
    rw [hread (i+1) hir hhr hir]
    split
    · rename_i he
      simpa only [he] using hs.2.2.1
    · rw [if_pos rfl]
      exact hs.2.2.1
  refine ⟨by omega, ?_, ?_⟩
  · apply Forall_sublist_by_Znth__partition_scan _ _ low (i+1) (by omega) (by simp only [Zlength_replace_Znth]; omega)
    intro k hk
    rw [hpiv, hread k hir hhr (by omega), if_neg (by omega), if_neg (by omega)]
    exact hs.2.2.2.1 k (by omega)
  · apply Forall_sublist_by_Znth__partition_scan _ _ (i+1+1) (high+1) (by omega) (by simp only [Zlength_replace_Znth]; omega)
    intro k hk
    rw [hpiv, hread k hir hhr (by omega)]
    split
    · exact hs.2.2.2.2 (i+1) (by omega)
    · rw [if_neg (by omega)]
      exact hs.2.2.2.2 k (by omega)

theorem partition_scan_inv_final_same_outside__partition_scan (l l1 : List Int) (low high pivot i j : Int)
    (hlo : 0 ≤ low) (hlh : low ≤ high) (hli : low-1 ≤ i) (hhl : high < Zlength l1)
    (hjd : j ≥ high) (hij : i < j) (hjh : j ≤ high)
    (hs : partition_scan_inv l l1 low high pivot i j) :
    same_outside_range l (replace_Znth high (Znth (i+1) l1 0) (replace_Znth (i+1) (Znth high l1 0) l1)) low high :=
  same_outside_range_swap_inside__partition_scan l l1 low high (i+1) high hs.2.1 (by omega) (by omega) (by omega) (by omega)

theorem partition_scan_inv_final_permutation__partition_scan (l l1 : List Int) (low high pivot i j : Int)
    (hlo : 0 ≤ low) (hlh : low ≤ high) (hli : low-1 ≤ i) (hhl : high < Zlength l1)
    (hjd : j ≥ high) (hij : i < j) (hjh : j ≤ high)
    (hs : partition_scan_inv l l1 low high pivot i j) :
    permutation l (replace_Znth high (Znth (i+1) l1 0) (replace_Znth (i+1) (Znth high l1 0) l1)) :=
  hs.1.trans (permutation_swap_Znth__partition_scan l1 (i+1) high 0 (by omega) (by omega))

theorem partitioned_at_ext__quicksort_range (l l1 : List Int) (left right p : Int)
    (hl : 0 ≤ left) (hr : right < Zlength l) (hlen : Zlength l = Zlength l1)
    (he : ∀ k, (left ≤ k ∧ k ≤ right) → Znth k l1 0 = Znth k l 0)
    (hs : partitioned_at l left right p) : partitioned_at l1 left right p := by
  have hp := hs.1
  have hpiv := he p hp
  refine ⟨hp, ?_, ?_⟩
  · rw [hpiv, sublist_eq_from_Znth__quicksort_range l1 l left p hlen.symm (by omega) (by omega)
      (fun k hk => he k (by omega))]
    exact hs.2.1
  · rw [hpiv, sublist_eq_from_Znth__quicksort_range l1 l (p+1) (right+1) hlen.symm (by omega) (by omega)
      (fun k hk => he k (by omega))]
    exact hs.2.2

theorem sorted_range_ext__quicksort_range (l l1 : List Int) (left right : Int)
    (hl : 0 ≤ left) (hr : right < Zlength l) (hlen : Zlength l = Zlength l1)
    (he : ∀ k, (left ≤ k ∧ k ≤ right) → Znth k l1 0 = Znth k l 0)
    (hs : sorted_range l left right) : sorted_range l1 left right := by
  induction hs with
  | sorted_range_base left right hb => exact .sorted_range_base left right hb
  | sorted_range_from_left left right p hpr hp hs ih =>
    have hpbound := hp.1
    exact .sorted_range_from_left left right p hpr (partitioned_at_ext__quicksort_range l l1 left right p hl hr hlen he hp)
      (ih hl (by omega) (fun k hk => he k (by omega)))
  | sorted_range_from_right left right p hpl hp hs ih =>
    have hpbound := hp.1
    exact .sorted_range_from_right left right p hpl (partitioned_at_ext__quicksort_range l l1 left right p hl hr hlen he hp)
      (ih (by omega) hr (fun k hk => he k (by omega)))
  | sorted_range_from_both left right p hpr hp hls hrs ihl ihr =>
    have hpbound := hp.1
    exact .sorted_range_from_both left right p hpr (partitioned_at_ext__quicksort_range l l1 left right p hl hr hlen he hp)
      (ihl hl (by omega) (fun k hk => he k (by omega))) (ihr (by omega) hr (fun k hk => he k (by omega)))

private theorem sublist_lengthZ (lo hi : Int) (l : List Int)
    (hlo : 0 ≤ lo ∧ lo ≤ hi) (hhi : hi ≤ Zlength l) :
    Zlength (sublist lo hi l) = hi-lo := ListLib.Zlength_sublist lo hi l hlo hhi

theorem increasing_aux_tail_increasing__quicksort_range (l : List Int) (x : Int)
    (h : increasing_aux l x) : increasing l := by
  cases l with
  | nil => trivial
  | cons y l => exact h.2

theorem increasing_aux_head_le_all__quicksort_range (l : List Int) (x k : Int)
    (h : increasing_aux l x) (hk : 0 ≤ k ∧ k < Zlength l) : x ≤ Znth k l 0 := by
  induction l generalizing x k with
  | nil => simp only [Zlength_nil] at hk; omega
  | cons y l ih =>
    by_cases hz : k=0
    · subst k; exact h.1
    · rw [Znth_cons 0 k y l (by omega)]
      exact Int.le_trans h.1 (ih y (k-1) h.2 (by simp only [Zlength_cons] at hk; omega))

theorem partitioned_at_left_Znth_le__quicksort_range (l : List Int) (left right p k : Int)
    (hl : 0 ≤ left) (hp : p ≤ Zlength l) (hs : partitioned_at l left right p)
    (hk : left ≤ k ∧ k < p) : Znth k l 0 ≤ Znth p l 0 := by
  have hlen := sublist_lengthZ left p l (by have := hs.1; omega) hp
  have h := Forall_Znth__quicksort_range _ _ (k-left) 0 hs.2.1 (by omega)
  rw [Znth_sublist 0 left (k-left) p l hl (by omega)] at h
  simpa only [Int.sub_add_cancel] using h

theorem partitioned_at_right_Znth_lt__quicksort_range (l : List Int) (left right p k : Int)
    (hl : 0 ≤ left) (hr : right < Zlength l) (hs : partitioned_at l left right p)
    (hk : p < k ∧ k ≤ right) : Znth p l 0 < Znth k l 0 := by
  have hlen := sublist_lengthZ (p+1) (right+1) l (by have := hs.1; omega) (by omega)
  have h := Forall_Znth__quicksort_range _ _ (k-(p+1)) 0 hs.2.2 (by omega)
  rw [Znth_sublist 0 (p+1) (k-(p+1)) (right+1) l (by have := hs.1; omega) (by omega)] at h
  simpa only [Int.sub_add_cancel] using h

private theorem partition_relax (l : List Int) (left right p : Int) (hs : partitioned_at l left right p) :
    SimpleC.EE.LLM_bench.Algorithms.quicksort_hoare_swap_index.quicksort_lib.partitioned_at l left right p := by
  refine ⟨hs.1, hs.2.1, Forall.iff_forall_mem.mpr ?_⟩
  intro x hx
  exact Int.le_of_lt (hs.2.2.mem hx)

theorem sorted_range_ordered__quicksort_range (l : List Int) (left right : Int)
    (hl : 0 ≤ left) (hr : right < Zlength l) (hs : sorted_range l left right) :
    ∀ i j, left ≤ i → i ≤ j → j ≤ right → Znth i l 0 ≤ Znth j l 0 := by
  induction hs with
  | sorted_range_base left right hb =>
    intro i j hi hij hj
    have : i=j := by omega
    simpa only [this] using Int.le_refl (Znth j l 0)
  | sorted_range_from_left left right p hpr hp hs ih =>
    have hpb := hp.1
    exact quicksort_partition_combine_left_only_local l left right p hl hr (by omega) (partition_relax l left right p hp)
      (ih hl (by omega))
  | sorted_range_from_right left right p hpl hp hs ih =>
    have hpb := hp.1
    exact quicksort_partition_combine_right_only_local l left right p hl hr (by omega) (partition_relax l left right p hp)
      (ih (by omega) hr)
  | sorted_range_from_both left right p hpr hp hls hrs ihl ihr =>
    exact quicksort_partition_combine_both_sides_local l left right p hl hr hpr (partition_relax l left right p hp)
      (ihl hl (by omega)) (ihr (by omega) hr)

theorem ordered_full_implies_increasing__quicksort_range (l : List Int)
    (h : ∀ i j, 0 ≤ i → i ≤ j → j ≤ Zlength l-1 → Znth i l 0 ≤ Znth j l 0) : increasing l := by
  have haux : ∀ t : List Int, ∀ x : Int, Sorting.increasing_aux t x → increasing_aux t x := by
    intro t
    induction t with
    | nil => intros; trivial
    | cons y t ih => intro x hx; exact ⟨hx.1, ih y hx.2⟩
  have hs := range_nondecreasing_full_to_increasing l h
  cases l with
  | nil => trivial
  | cons x l => exact haux l x hs

theorem sorted_range_implies_increasing__quicksort_range (l : List Int)
    (h : sorted_range l 0 (Zlength l-1)) : increasing l :=
  ordered_full_implies_increasing__quicksort_range l (sorted_range_ordered__quicksort_range l 0 (Zlength l-1) (by decide) (by omega) h)

theorem dedup_scan_inv_init__discretize_dedup (src sorted : List Int) (n : Int)
    (hp : permutation src sorted) (hi : increasing sorted) (hn : Zlength src=n) (hn1 : 1 ≤ n) :
    dedup_scan_inv src sorted sorted 0 1 := by
  have hlen : Zlength src = Zlength sorted := congrArg Int.ofNat hp.length_eq
  refine ⟨hlen, rfl, hp, hi, by omega, by omega, ⟨by omega, ?_⟩, ?_, ?_, ?_⟩
  · intro i j hij hj; omega
  · intro x; rfl
  · intros; rfl
  · rfl

theorem increasing_aux_tail_increasing__discretize_dedup (l : List Int) (x : Int)
    (h : increasing_aux l x) : increasing l := increasing_aux_tail_increasing__quicksort_range l x h

theorem increasing_aux_head_le_all__discretize_dedup (l : List Int) (x k : Int)
    (h : increasing_aux l x) (hk : 0 ≤ k ∧ k < Zlength l) : x ≤ Znth k l 0 :=
  increasing_aux_head_le_all__quicksort_range l x k h hk

theorem increasing_order__discretize_dedup (l : List Int) (i j : Int)
    (h : increasing l) (hij : 0 ≤ i ∧ i ≤ j) (hj : j < Zlength l) : Znth i l 0 ≤ Znth j l 0 := by
  induction l generalizing i j with
  | nil => simp only [Zlength_nil] at hj; omega
  | cons x l ih =>
    have hlen : Zlength (x::l) = Zlength l+1 := Zlength_cons x l
    by_cases hi0 : i=0
    · subst i
      by_cases hj0 : j=0
      · subst j; exact Int.le_refl _
      · rw [Znth_cons 0 j x l (by omega)]
        exact increasing_aux_head_le_all__quicksort_range l x (j-1) h (by omega)
    · rw [Znth_cons 0 i x l (by omega), Znth_cons 0 j x l (by omega)]
      exact ih (i-1) (j-1) (increasing_aux_tail_increasing__quicksort_range l x h) (by omega) (by omega)

theorem sublist0_extend_in_iff__discretize_dedup (l : List Int) (n x : Int)
    (hn : 0 ≤ n ∧ n < Zlength l) : x ∈ sublist 0 (n+1) l ↔ x ∈ sublist 0 n l ∨ x=Znth n l 0 := by
  rw [sublist_split 0 (n+1) n l (by omega) (by omega), sublist_single 0 n l hn, List.mem_append, List.mem_singleton]

theorem sublist0_Znth_In__discretize_dedup (l : List Int) (n i : Int)
    (hi : 0 ≤ i ∧ i < n) (hn : n ≤ Zlength l) : Znth i l 0 ∈ sublist 0 n l := by
  have hlen := sublist_lengthZ 0 n l (by omega) hn
  have hin : i.toNat < (sublist 0 n l).length := by simp only [Zlength, Int.ofNat_eq_coe] at hlen; omega
  have hmem : Znth i (sublist 0 n l) 0 ∈ sublist 0 n l := by
    simpa only [Znth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hin, Option.getD_some] using List.getElem_mem hin
  rw [Znth_sublist 0 0 i n l (by decide) (by omega), Int.add_zero] at hmem
  exact hmem

theorem sublist0_In_Znth_exists__discretize_dedup (l : List Int) (n x : Int)
    (hn : 0 ≤ n ∧ n ≤ Zlength l) (hx : x ∈ sublist 0 n l) :
    ∃ i, (0 ≤ i ∧ i < n) ∧ Znth i l 0=x := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hx
  have hlen := sublist_lengthZ 0 n l (by omega) hn.2
  have hib : 0 ≤ (i : Int) ∧ (i : Int)<n := by simp only [Zlength, Int.ofNat_eq_coe] at hlen; omega
  refine ⟨i, hib, ?_⟩
  have heq : Znth (i : Int) (sublist 0 n l) 0=x := by
    simpa only [Znth, Int.toNat_natCast, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] using he
  rw [Znth_sublist 0 0 i n l (by decide) (by omega), Int.add_zero] at heq
  exact heq

theorem sublist0_replace_prefix__discretize_dedup (l : List Int) (i v : Int)
    (hi : 0 ≤ i ∧ i ≤ Zlength l) : sublist 0 i (replace_Znth i v l)=sublist 0 i l := by
  by_cases he : i=Zlength l
  · rw [replace_Znth_nothing i l v (by omega)]
  · apply sublist_eq_from_Znth__quicksort_range _ l 0 i (Zlength_replace_Znth l i v) (by omega) (by simp only [Zlength_replace_Znth]; omega)
    intro k hk
    exact Znth_replace_Znth_Diff 0 l i k v (by omega) (by omega) (by omega)

theorem sublist0_replace_next_in_iff__discretize_dedup (l : List Int) (i v x : Int)
    (hi : 0 ≤ i ∧ i < Zlength l) :
    x ∈ sublist 0 (i+1) (replace_Znth i v l) ↔ x ∈ sublist 0 i l ∨ x=v := by
  rw [sublist0_extend_in_iff__discretize_dedup _ i x (by simpa only [Zlength_replace_Znth] using hi),
    sublist0_replace_prefix__discretize_dedup l i v (by omega), Znth_replace_Znth_Same 0 l i v hi]

theorem dedup_scan_inv_step_duplicate__discretize_dedup (src sorted cur : List Int) (slow fast : Int)
    (hs : dedup_scan_inv src sorted cur slow fast) (hf : fast < Zlength sorted)
    (he : Znth fast cur 0=Znth slow cur 0) : dedup_scan_inv src sorted cur slow (fast+1) := by
  obtain ⟨hsrc, hcur, hp, hi, hfb, hsb, hstrict, hsame, htail, hlast⟩ := hs
  have hfast := htail fast (by omega)
  refine ⟨hsrc, hcur, hp, hi, by omega, by omega, hstrict, ?_, ?_, ?_⟩
  · intro x
    rw [sublist0_extend_in_iff__discretize_dedup sorted fast x (by omega)]
    constructor
    · intro hx; exact Or.inl ((hsame x).mp hx)
    · rintro (hx|heq)
      · exact (hsame x).mpr hx
      · rw [heq, ← hfast, he]
        exact sublist0_Znth_In__discretize_dedup cur (slow+1) slow (by omega) (by omega)
  · intro k hk; exact htail k (by omega)
  · simp only [Int.add_sub_cancel]
    omega

theorem dedup_scan_inv_step_new__discretize_dedup (src sorted cur : List Int) (slow fast : Int)
    (hs : dedup_scan_inv src sorted cur slow fast) (hf : fast < Zlength sorted)
    (hne : Znth fast cur 0≠Znth slow cur 0) :
    dedup_scan_inv src sorted (replace_Znth (slow+1) (Znth fast cur 0) cur) (slow+1) (fast+1) := by
  obtain ⟨hsrc, hcur, hp, hi, hfb, hsb, hstrict, hsame, htail, hlast⟩ := hs
  have hfast := htail fast (by omega)
  have hsfl : Znth slow cur 0 < Znth fast cur 0 := by
    have ho := increasing_order__discretize_dedup sorted (fast-1) fast hi (by omega) hf
    omega
  have hir : 0 ≤ slow+1 ∧ slow+1 < Zlength cur := by omega
  refine ⟨hsrc, by simpa only [Zlength_replace_Znth] using hcur, hp, hi, by omega, by omega,
    ⟨by simp only [Zlength_replace_Znth]; omega, ?_⟩, ?_, ?_, ?_⟩
  · intro i j hij hj
    by_cases hjold : j < slow+1
    · rw [Znth_replace_Znth_Diff 0 cur (slow+1) i _ hir (by omega) (by omega),
        Znth_replace_Znth_Diff 0 cur (slow+1) j _ hir (by omega) (by omega)]
      exact hstrict.2 i j hij hjold
    · have hej : j=slow+1 := by omega
      subst j
      rw [Znth_replace_Znth_Same 0 cur (slow+1) _ hir,
        Znth_replace_Znth_Diff 0 cur (slow+1) i _ hir (by omega) (by omega)]
      by_cases his : i=slow
      · simpa only [his] using hsfl
      · have ho := hstrict.2 i slow (by omega) (by omega)
        omega
  · intro x
    rw [sublist0_replace_next_in_iff__discretize_dedup cur (slow+1) (Znth fast cur 0) x hir,
      sublist0_extend_in_iff__discretize_dedup sorted fast x (by omega), hsame x, hfast]
  · intro k hk
    rw [Znth_replace_Znth_Diff 0 cur (slow+1) k _ hir (by omega) (by omega)]
    exact htail k (by omega)
  · rw [Znth_replace_Znth_Same 0 cur (slow+1) _ hir, Int.add_sub_cancel]
    exact hfast

theorem dedup_scan_inv_to_discretize_result__discretize_dedup (src sorted cur : List Int) (slow n : Int)
    (hs : dedup_scan_inv src sorted cur slow n) (hlen : Zlength src=n) (hn : 1 ≤ n) :
    discretize_result src n cur (slow+1) := by
  obtain ⟨hsrc, hcur, hp, hi, hnb, hsb, hstrict, hsame, htail, hlast⟩ := hs
  have hsorted : Zlength sorted=n := by omega
  have hcur_n : Zlength cur=n := by omega
  have hsame_src : same_values_prefix cur (slow+1) src n := by
    intro x
    have he := hsame x
    rw [sublist_self sorted n hsorted.symm] at he
    rw [sublist_self src n hlen.symm]
    exact he.trans (List.Perm.mem_iff hp).symm
  refine ⟨hlen, hcur_n, hn, by omega, hstrict, hsame_src, ?_, ?_, ?_⟩
  · intro i hi
    have hmem := sublist0_Znth_In__discretize_dedup src n i hi (by omega)
    exact sublist0_In_Znth_exists__discretize_dedup cur (slow+1) (Znth i src 0) (by omega) ((hsame_src _).mpr hmem)
  · intro r hr
    have hmem := sublist0_Znth_In__discretize_dedup cur (slow+1) r hr (by omega)
    obtain ⟨i, hi, he⟩ := sublist0_In_Znth_exists__discretize_dedup src n (Znth r cur 0) (by omega) ((hsame_src _).mp hmem)
    exact ⟨i, hi, he.symm⟩
  · intro i j ri rj hi hj hri hrj hei hej
    have hless : ri<rj → Znth ri cur 0<Znth rj cur 0 := fun hlt => hstrict.2 ri rj (by omega) (by omega)
    have hgreater : rj<ri → Znth rj cur 0<Znth ri cur 0 := fun hlt => hstrict.2 rj ri (by omega) (by omega)
    constructor
    · intro heq
      by_cases hlt : ri<rj
      · have := hless hlt; omega
      · by_cases hgt : rj<ri
        · have := hgreater hgt; omega
        · omega
    · intro hlt
      by_cases heq : ri=rj
      · subst rj; omega
      · by_cases hgt : rj<ri
        · have := hgreater hgt; omega
        · omega

theorem midpoint_between_bounds__query_forward_search (low high : Int) (h : low ≤ high) :
    low ≤ low+Z.quot (high-low) 2 ∧ low+Z.quot (high-low) 2 ≤ high := by
  have he := Z.quot_rem (high-low) 2 (by decide)
  have hb := rem_nonneg_bounds (high-low) 2 (by omega) (by decide)
  omega

theorem strict_increasing_Znth_lt__query_forward_search (l : List Int) (i j : Int)
    (hs : strict_increasing l) (hi : 0 ≤ i ∧ i<j) (hj : j<Zlength l) : Znth i l 0<Znth j l 0 := hs.2 i j hi hj

theorem query_forward_search_inv_init__query_forward_search (map : List Int) (map_size target : Int)
    (hm : 0 ≤ map_size) : query_forward_search_inv map map_size target 0 (map_size-1) :=
  ⟨by decide, by omega, by omega, by intro i hi; omega, by intro i hi; omega⟩

theorem query_forward_search_inv_step_right__query_forward_search (map : List Int) (map_size target low mid high : Int)
    (hlen : Zlength map=map_size) (hs : strict_increasing map) (hi : query_forward_search_inv map map_size target low high)
    (hlm : low ≤ mid) (hmh : mid ≤ high) (hlt : Znth mid map 0<target) :
    query_forward_search_inv map map_size target (mid+1) high := by
  obtain ⟨hl, hh, hlh, hbefore, hafter⟩ := hi
  refine ⟨by omega, hh, by omega, ?_, hafter⟩
  intro i hir
  by_cases hil : i<low
  · exact hbefore i (by omega)
  · by_cases him : i=mid
    · simpa only [him] using hlt
    · have ho := strict_increasing_Znth_lt__query_forward_search map i mid hs (by omega) (by omega)
      omega

theorem query_forward_search_inv_step_left__query_forward_search (map : List Int) (map_size target low mid high : Int)
    (hlen : Zlength map=map_size) (hs : strict_increasing map) (hi : query_forward_search_inv map map_size target low high)
    (hlm : low ≤ mid) (hmh : mid ≤ high) (hge : Znth mid map 0 ≥ target) (hne : Znth mid map 0≠target) :
    query_forward_search_inv map map_size target low (mid-1) := by
  obtain ⟨hl, hh, hlh, hbefore, hafter⟩ := hi
  refine ⟨hl, by omega, by omega, hbefore, ?_⟩
  intro i hir
  by_cases hhi : high<i
  · exact hafter i (by omega)
  · by_cases him : i=mid
    · subst i; omega
    · have ho := strict_increasing_Znth_lt__query_forward_search map mid i hs (by omega) (by omega)
      omega

theorem query_forward_result_not_found__query_forward_search (map : List Int) (map_size target low high : Int)
    (hi : query_forward_search_inv map map_size target low high) (hgt : low>high) (hle : low ≤ high+1) :
    query_forward_result map map_size target (-1) := by
  obtain ⟨hl, hh, hlh, hbefore, hafter⟩ := hi
  refine Or.inr ⟨?_, rfl⟩
  intro i hir he
  by_cases hil : i<low
  · have := hbefore i (by omega); omega
  · have := hafter i (by omega); omega

theorem query_forward_result_found_unique__query_forward_search (map : List Int) (map_size target mid : Int)
    (hlen : Zlength map=map_size) (hs : strict_increasing map) (hm : 0 ≤ mid ∧ mid<map_size)
    (he : Znth mid map 0=target) : query_forward_result map map_size target mid := by
  refine Or.inl ⟨⟨mid, hm, he, rfl⟩, ?_⟩
  intro j hj hej
  by_cases hmj : mid<j
  · have := strict_increasing_Znth_lt__query_forward_search map mid j hs (by omega) (by omega)
    omega
  · by_cases hjm : j<mid
    · have := strict_increasing_Znth_lt__query_forward_search map j mid hs (by omega) (by omega)
      omega
    · omega


set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open Algorithms.discretize.lean.groundtruth.discretize_goal
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

theorem proof_of_partition_entail_wit_1 : partition_entail_wit_1 := by
  unfold partition_entail_wit_1
  left
  intro high_pre low_pre n_pre arr_pre l PreH1 PreH2 PreH3
  Exists l
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact partition_scan_inv_init__partition_scan l low_pre high_pre PreH1 PreH2
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_partition_entail_wit_2_1 : partition_entail_wit_2_1 := by
  unfold partition_entail_wit_2_1
  left
  intro high_pre low_pre n_pre arr_pre l l1_2 j i pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  prop_apply naive_C_Rules.IntArray.full_Zlength
  Intros_p hlen
  simp only [Zlength_replace_Znth] at hlen
  Exists (replace_Znth j (Znth (i+1) l1_2 0) (replace_Znth (i+1) (Znth j l1_2 0) l1_2))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact partition_scan_inv_step_le__partition_scan l l1_2 low_pre high_pre pivot i j PreH4 PreH5 (by omega) PreH1 PreH2 PreH7 PreH8 PreH9 PreH10
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_partition_entail_wit_2_2 : partition_entail_wit_2_2 := by
  unfold partition_entail_wit_2_2
  left
  intro high_pre low_pre n_pre arr_pre l l1_2 j i pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  Exists l1_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact partition_scan_inv_step_gt__partition_scan l l1_2 low_pre high_pre pivot i j PreH1 PreH2 PreH10
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_partition_return_wit_1 : partition_return_wit_1 := by
  unfold partition_return_wit_1
  left
  intro high_pre low_pre n_pre arr_pre l l1_2 j i pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  prop_apply naive_C_Rules.IntArray.full_Zlength
  Intros_p hlen
  simp only [Zlength_replace_Znth] at hlen
  Exists (replace_Znth high_pre (Znth (i+1) l1_2 0) (replace_Znth (i+1) (Znth high_pre l1_2 0) l1_2))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact partition_scan_inv_final_permutation__partition_scan l l1_2 low_pre high_pre pivot i j PreH3 PreH4 PreH6 (by omega) PreH1 PreH7 PreH8 PreH9
    | exact partition_scan_inv_final_same_outside__partition_scan l l1_2 low_pre high_pre pivot i j PreH3 PreH4 PreH6 (by omega) PreH1 PreH7 PreH8 PreH9
    | exact partition_scan_inv_final_swap_partitioned_at__partition_scan l l1_2 low_pre high_pre pivot i j PreH3 PreH4 PreH6 (by omega) PreH1 PreH7 PreH8 PreH9
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_quicksort_range_return_wit_1 : quicksort_range_return_wit_1 := by
  unfold quicksort_range_return_wit_1
  left
  intro right_pre left_pre n_pre arr_pre l l1_2 retval l1_3 l1_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  prop_apply (naive_C_Rules.IntArray.full_Zlength arr_pre n_pre l1_4)
  Intros_p hlen
  have hlen34 := PreH2.1
  have hlen23 := PreH6.1
  have hp3 := partitioned_at_preserved_by_left__quicksort_range l1_2 l1_3 left_pre right_pre retval PreH5 PreH16 PreH6 (by omega) PreH13
  have hp4 := partitioned_at_preserved_by_right__quicksort_range l1_3 l1_4 left_pre right_pre retval PreH1 PreH16 PreH2 (by omega) hp3
  have hleft : sorted_range l1_4 left_pre (retval-1) := by
    apply sorted_range_ext__quicksort_range l1_3 l1_4 left_pre (retval-1) PreH16 (by omega) hlen34 _ PreH7
    intro k hk
    exact PreH2.2 k (by omega) (Or.inl (by omega))
  have hs := sorted_range_from_both l1_4 left_pre right_pre retval ⟨PreH9,PreH10⟩ hp4 hleft PreH3
  have hsame23 := same_outside_range_weaken__quicksort_range l1_2 l1_3 left_pre (retval-1) left_pre right_pre (by omega) (by omega) PreH6
  have hsame34 := same_outside_range_weaken__quicksort_range l1_3 l1_4 (retval+1) right_pre left_pre right_pre (by omega) (by omega) PreH2
  have hsame := same_outside_range_trans__quicksort_range l l1_3 l1_4 left_pre right_pre
    (same_outside_range_trans__quicksort_range l l1_2 l1_3 left_pre right_pre PreH12 hsame23) hsame34
  Exists l1_4
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact PreH11.trans (PreH5.trans PreH1)
    | exact hsame
    | exact hs
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_quicksort_range_return_wit_2 : quicksort_range_return_wit_2 := by
  unfold quicksort_range_return_wit_2
  left
  intro right_pre left_pre n_pre arr_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  prop_apply (naive_C_Rules.IntArray.full_Zlength arr_pre n_pre l1_3)
  Intros_p hlen
  have hlen23 := PreH2.1
  have hp := partitioned_at_preserved_by_right__quicksort_range l1_2 l1_3 left_pre right_pre retval PreH1 PreH13 PreH2 (by omega) PreH10
  have hs := sorted_range_from_right l1_3 left_pre right_pre retval PreH5 hp PreH3
  have hsame23 := same_outside_range_weaken__quicksort_range l1_2 l1_3 (retval+1) right_pre left_pre right_pre (by omega) (by omega) PreH2
  have hsame := same_outside_range_trans__quicksort_range l l1_2 l1_3 left_pre right_pre PreH9 hsame23
  Exists l1_3
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact PreH8.trans PreH1
    | exact hsame
    | exact hs
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_quicksort_range_return_wit_3 : quicksort_range_return_wit_3 := by
  unfold quicksort_range_return_wit_3
  left
  intro right_pre left_pre n_pre arr_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  prop_apply (naive_C_Rules.IntArray.full_Zlength arr_pre n_pre l1_3)
  Intros_p hlen
  have hlen23 := PreH3.1
  have hp := partitioned_at_preserved_by_left__quicksort_range l1_2 l1_3 left_pre right_pre retval PreH2 PreH13 PreH3 (by omega) PreH10
  have hs := sorted_range_from_left l1_3 left_pre right_pre retval PreH1 hp PreH4
  have hsame23 := same_outside_range_weaken__quicksort_range l1_2 l1_3 left_pre (retval-1) left_pre right_pre (by omega) (by omega) PreH3
  have hsame := same_outside_range_trans__quicksort_range l l1_2 l1_3 left_pre right_pre PreH9 hsame23
  Exists l1_3
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact PreH8.trans PreH2
    | exact hsame
    | exact hs
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_quicksort_range_return_wit_4 : quicksort_range_return_wit_4 := by
  unfold quicksort_range_return_wit_4
  left
  intro right_pre left_pre n_pre arr_pre l PreH1 PreH2 PreH3 PreH4 PreH5
  Exists l
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact List.Perm.refl l
    | exact same_outside_range_refl__quicksort_range l left_pre right_pre
    | exact sorted_range_base l left_pre right_pre PreH1
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_int_array_quicksort_return_wit_1 : int_array_quicksort_return_wit_1 := by
  unfold int_array_quicksort_return_wit_1
  left
  intro n_pre arr_pre l l1_2 PreH1 PreH2 PreH3 PreH4 PreH5
  prop_apply (naive_C_Rules.IntArray.full_Zlength arr_pre n_pre l1_2)
  Intros_p hlen
  have hs := sorted_range_implies_increasing__quicksort_range l1_2 (by rw [hlen]; exact PreH3)
  Exists l1_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact hs
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_discretize_safety_wit_8 : discretize_safety_wit_8 := by
  unfold discretize_safety_wit_8
  left
  intro dest_map_pre n_pre src_pre src_l out_l slow PreH1 PreH2 PreH3 PreH4
  have hb := PreH4.2.2.2.1
  split_pures <;> dump_pre_spatial
  · change _≤2147483647
    omega
  · change (-2147483648:Int)≤_
    omega

theorem proof_of_discretize_entail_wit_1 : discretize_entail_wit_1 := by
  unfold discretize_entail_wit_1
  left
  intro dest_map_pre n_pre src_pre src_l PreH1 PreH2 PreH3
  sep_apply (naive_C_Rules.IntArray.undef_full_to_undef_seg dest_map_pre n_pre)
  have he : sublist 0 0 src_l=[] := by simp [sublist]
  rw [he]
  sep_apply_right (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp
    (naive_C_Rules.IntArray.full_empty dest_map_pre 0)).2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_discretize_entail_wit_2 : discretize_entail_wit_2 := by
  unfold discretize_entail_wit_2
  left
  intro dest_map_pre n_pre src_pre src_l i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  rw [sublist_split 0 (i+1) i src_l (by omega) (by omega),sublist_single 0 i src_l (by omega)]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_discretize_entail_wit_3 : discretize_entail_wit_3 := by
  unfold discretize_entail_wit_3
  left
  intro dest_map_pre n_pre src_pre src_l i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  have hi : i=n_pre := by omega
  subst i
  rw [sublist_self src_l n_pre PreH2.symm]
  sep_apply (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp
    (naive_C_Rules.IntArray.undef_seg_empty dest_map_pre n_pre)).1)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_discretize_entail_wit_4 : discretize_entail_wit_4 := by
  unfold discretize_entail_wit_4
  left
  intro dest_map_pre n_pre src_pre src_l l1 PreH1 PreH2 PreH3 PreH4 PreH5
  Exists l1
  Exists l1
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact dedup_scan_inv_init__discretize_dedup src_l l1 n_pre PreH1 PreH2 PreH3 PreH4
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_discretize_entail_wit_5_1 : discretize_entail_wit_5_1 := by
  unfold discretize_entail_wit_5_1
  left
  intro dest_map_pre n_pre src_pre src_l sorted_l_2 cur_l_2 fast slow PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hlen := PreH10.1
  Exists sorted_l_2
  Exists (replace_Znth (slow+1) (Znth fast cur_l_2 0) cur_l_2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact dedup_scan_inv_step_new__discretize_dedup src_l sorted_l_2 cur_l_2 slow fast PreH10 (by omega) PreH1
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_discretize_entail_wit_5_2 : discretize_entail_wit_5_2 := by
  unfold discretize_entail_wit_5_2
  left
  intro dest_map_pre n_pre src_pre src_l sorted_l_2 cur_l_2 fast slow PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hlen := PreH10.1
  Exists sorted_l_2
  Exists cur_l_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact dedup_scan_inv_step_duplicate__discretize_dedup src_l sorted_l_2 cur_l_2 slow fast PreH10 (by omega) PreH1
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_discretize_entail_wit_6 : discretize_entail_wit_6 := by
  unfold discretize_entail_wit_6
  left
  intro dest_map_pre n_pre src_pre src_l sorted_l cur_l fast slow PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have hf : fast=n_pre := by omega
  subst fast
  Exists cur_l
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact dedup_scan_inv_to_discretize_result__discretize_dedup src_l sorted_l cur_l slow n_pre PreH9 PreH2 PreH3
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_query_forward_safety_wit_4 : query_forward_safety_wit_4 := by
  unfold query_forward_safety_wit_4
  left
  intro target_pre map_size_pre map_pre map_l high low PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have hm := midpoint_between_bounds__query_forward_search low high PreH1
  split_pures <;> dump_pre_spatial
  · change _≤2147483647
    omega
  · change (-2147483648:Int)≤_
    omega

theorem proof_of_query_forward_entail_wit_1 : query_forward_entail_wit_1 := by
  unfold query_forward_entail_wit_1
  left
  intro target_pre map_size_pre map_pre map_l PreH1 PreH2 PreH3 PreH4
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact query_forward_search_inv_init__query_forward_search map_l map_size_pre target_pre PreH2
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_query_forward_entail_wit_2 : query_forward_entail_wit_2 := by
  unfold query_forward_entail_wit_2
  left
  intro target_pre map_size_pre map_pre map_l high low PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have hm := midpoint_between_bounds__query_forward_search low high PreH1
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_query_forward_entail_wit_3_1 : query_forward_entail_wit_3_1 := by
  unfold query_forward_entail_wit_3_1
  left
  intro target_pre map_size_pre map_pre map_l low mid high PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact query_forward_search_inv_step_right__query_forward_search map_l map_size_pre target_pre low mid high PreH3 PreH6 PreH11 PreH8 PreH9 PreH1
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_query_forward_entail_wit_3_2 : query_forward_entail_wit_3_2 := by
  unfold query_forward_entail_wit_3_2
  left
  intro target_pre map_size_pre map_pre map_l low mid high PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact query_forward_search_inv_step_left__query_forward_search map_l map_size_pre target_pre low mid high PreH3 PreH6 PreH11 PreH8 PreH9 PreH1 PreH2
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_query_forward_entail_wit_4 : query_forward_entail_wit_4 := by
  unfold query_forward_entail_wit_4
  left
  intro target_pre map_size_pre map_pre map_l high low PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact query_forward_result_not_found__query_forward_search map_l map_size_pre target_pre low high PreH9 PreH1 PreH7
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_query_forward_return_wit_2 : query_forward_return_wit_2 := by
  unfold query_forward_return_wit_2
  left
  intro target_pre map_size_pre map_pre map_l low mid high PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact query_forward_result_found_unique__query_forward_search map_l map_size_pre target_pre mid PreH2 PreH5 (by omega) PreH1
    | assumption
    | omega
    | rfl
    | trivial

end Algorithms.discretize.lean.groundtruth.discretize_proof_manual
