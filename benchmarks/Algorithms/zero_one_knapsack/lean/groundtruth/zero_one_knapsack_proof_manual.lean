import Algorithms.zero_one_knapsack.lean.groundtruth.zero_one_knapsack_goal
import Algorithms.zero_one_knapsack.lean.groundtruth.zero_one_knapsack_proof_auto
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import ListLib.General.Length
import Mathlib.Data.List.Nodup

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace Algorithms.zero_one_knapsack.lean.groundtruth.zero_one_knapsack_proof_manual

open Algorithms.zero_one_knapsack.lean
open scoped SimpleC

namespace ProofSupport

open AUXLib

private theorem maximum_iff (P : Int → Prop) (v : Int) :
    MaxMinLib.max_value_of_subset (· ≤ ·) P id v ↔ P v ∧ ∀ x, P x → x ≤ v := by
  constructor
  · rintro ⟨x, ⟨hx, hm⟩, rfl⟩; exact ⟨hx, hm⟩
  · rintro ⟨hx, hm⟩; exact ⟨v, ⟨hx, hm⟩, rfl⟩

private theorem cell_iff (w v : List Int) (i c a : Int) :
    KnapsackCellCorrect w v i c a ↔ KnapsackPlan w v i c a ∧
      ∀ x, KnapsackPlan w v i c x → x ≤ a := maximum_iff _ _

 theorem KnapsackRowsDone_to_RowProgress0 (weights values : List Int) (capacity : Int)
    (dp : List Int) (row : Int) (_ : 0 ≤ capacity)
    (h : KnapsackRowsDone weights values capacity dp row) :
    KnapsackRowProgress weights values capacity dp row 0 := by
  simpa [KnapsackRowProgress, KnapsackRowsDone] using h

theorem KnapsackRowProgress_end_to_RowsDone (weights values : List Int) (capacity : Int)
    (dp : List Int) (row col : Int) (hc : col = capacity + 1)
    (h : KnapsackRowProgress weights values capacity dp row col) :
    KnapsackRowsDone weights values capacity dp (row + 1) := by
  unfold KnapsackRowsDone
  have he : (row+1)*(capacity+1) = row*(capacity+1)+col := by nlinarith
  rw [he]
  exact h

theorem KnapsackRowProgress_index_bound (weights values : List Int) (capacity : Int)
    (dp : List Int) (row col idx : Int)
    (hs : KnapsackTablePrefixShape dp (row * (capacity + 1) + col))
    (_ : KnapsackRowProgress weights values capacity dp row col)
    (hi : 0 ≤ idx ∧ idx < row * (capacity + 1) + col) :
    0 ≤ idx ∧ idx < Zlength dp := by rw [hs.2]; exact hi

theorem KnapsackRowProgress_lookup_cell (weights values : List Int) (capacity : Int)
    (dp : List Int) (row col lookup_row lookup_col : Int)
    (h : KnapsackRowProgress weights values capacity dp row col)
    (hr : 0 ≤ lookup_row) (hc : 0 ≤ lookup_col ∧ lookup_col ≤ capacity)
    (hi : 0 ≤ KnapsackCellIndex capacity lookup_row lookup_col ∧
      KnapsackCellIndex capacity lookup_row lookup_col < row * (capacity + 1) + col) :
    KnapsackCellCorrect weights values lookup_row lookup_col
      (Znth (KnapsackCellIndex capacity lookup_row lookup_col) dp 0) := h _ _ hr hc hi

theorem KnapsackRowsDone_index_bound (weights values : List Int) (capacity : Int)
    (dp : List Int) (rows_done idx : Int)
    (hs : KnapsackTablePrefixShape dp (rows_done * (capacity + 1)))
    (_ : KnapsackRowsDone weights values capacity dp rows_done)
    (hi : 0 ≤ idx ∧ idx < rows_done * (capacity + 1)) :
    0 ≤ idx ∧ idx < Zlength dp := by rw [hs.2]; exact hi

theorem KnapsackRowsDone_lookup_cell (weights values : List Int) (capacity : Int)
    (dp : List Int) (rows_done lookup_row lookup_col : Int)
    (h : KnapsackRowsDone weights values capacity dp rows_done)
    (hr : 0 ≤ lookup_row) (hc : 0 ≤ lookup_col ∧ lookup_col ≤ capacity)
    (hi : 0 ≤ KnapsackCellIndex capacity lookup_row lookup_col ∧
      KnapsackCellIndex capacity lookup_row lookup_col < rows_done * (capacity + 1)) :
    KnapsackCellCorrect weights values lookup_row lookup_col
      (Znth (KnapsackCellIndex capacity lookup_row lookup_col) dp 0) := h _ _ hr hc hi

theorem Forall_Z_lt_0_nil (l : List Int) (h : Forall (fun i => 0 ≤ i ∧ i < 0) l) : l = [] := by
  cases h with
  | nil => rfl
  | cons ha _ => omega

theorem sum_map_weights_nonnegative (weights : List Int) (n : Int) (picks : List Int)
    (hw : ∀ k, (0 ≤ k ∧ k < n) → 1 ≤ Znth k weights 0)
    (hp : Forall (fun i => 0 ≤ i ∧ i < n) picks) :
    0 ≤ sum (picks.map (fun i => Znth i weights 0)) := by
  induction hp with
  | nil => simp [sum]
  | @cons x xs hx ht ih =>
    have hh := hw x hx
    simp only [List.map_cons, sum, List.foldr_cons] at *
    omega

theorem KnapsackPlan_empty (weights values : List Int) (item_count cap : Int)
    (hi : 0 ≤ item_count ∧ item_count ≤ Zlength weights)
    (hl : Zlength weights = Zlength values) (hc : 0 ≤ cap) :
    KnapsackPlan weights values item_count cap 0 := by
  exact ⟨hi, hl, hc, [], 0, by simp, .nil, rfl, hc, hl, rfl⟩

theorem KnapsackPlan_row0_value_zero (weights values : List Int) (cap value : Int)
    (h : KnapsackPlan weights values 0 cap value) : value = 0 := by
  rcases h with ⟨_, _, _, picks, weight, _, hp, _, _, hv⟩
  rw [Forall_Z_lt_0_nil picks hp] at hv
  exact hv.2

theorem KnapsackPlan_col0_value_zero (weights values : List Int) (item_count value : Int)
    (hw : ∀ k, (0 ≤ k ∧ k < item_count) → 1 ≤ Znth k weights 0)
    (h : KnapsackPlan weights values item_count 0 value) : value = 0 := by
  rcases h with ⟨_, _, _, picks, weight, _, hp, hwgt, hcap, hv⟩
  cases hp with
  | nil => exact hv.2
  | @cons x xs hx ht =>
    have ha := hw x hx
    have hb := sum_map_weights_nonnegative weights item_count xs hw ht
    simp only [KnapsackPlanWeight, List.map_cons, sum, List.foldr_cons] at hwgt
    change 0 ≤ List.foldr (fun x y => x + y) 0 (List.map (fun i => Znth i weights 0) xs) at hb
    omega

theorem KnapsackCellCorrect_row0_zero (weights values : List Int) (cap : Int)
    (hc : 0 ≤ cap) (hl : Zlength weights = Zlength values) :
    KnapsackCellCorrect weights values 0 cap 0 := by
  apply (cell_iff _ _ _ _ _).mpr
  refine ⟨KnapsackPlan_empty _ _ _ _ ⟨by omega, Zlength_nonneg _⟩ hl hc, ?_⟩
  intro value hp; have := KnapsackPlan_row0_value_zero _ _ _ _ hp; omega

theorem KnapsackCellCorrect_col0_zero (weights values : List Int) (item_count : Int)
    (hi : 0 ≤ item_count ∧ item_count ≤ Zlength weights)
    (hl : Zlength weights = Zlength values)
    (hw : ∀ k, (0 ≤ k ∧ k < item_count) → 1 ≤ Znth k weights 0) :
    KnapsackCellCorrect weights values item_count 0 0 := by
  apply (cell_iff _ _ _ _ _).mpr
  refine ⟨KnapsackPlan_empty _ _ _ _ hi hl (by omega), ?_⟩
  intro value hp; have := KnapsackPlan_col0_value_zero _ _ _ _ hw hp; omega

theorem Z_index_unique (r i c j C : Int) (hC : 0 ≤ C)
    (hc : 0 ≤ c ∧ c ≤ C) (hj : 0 ≤ j ∧ j ≤ C)
    (he : r * (C + 1) + c = i * (C + 1) + j) : r = i ∧ c = j := by
  have hr : r = i := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hh | hh
    · have h := mul_le_mul_of_nonneg_right (show r+1 ≤ i by omega) (show 0 ≤ C+1 by omega)
      nlinarith
    · have h := mul_le_mul_of_nonneg_right (show i+1 ≤ r by omega) (show 0 ≤ C+1 by omega)
      nlinarith
  exact ⟨hr, by rw [hr] at he; omega⟩

private theorem append_old (dp : List Int) (value k : Int) (hk : 0 ≤ k ∧ k < Zlength dp) :
    Znth k (dp ++ [value]) 0 = Znth k dp 0 :=
  ListLib.app_Znth1 0 dp [value] k hk

private theorem append_new (dp : List Int) (value : Int) :
    Znth (Zlength dp) (dp ++ [value]) 0 = value := by
  rw [app_Znth2 0 dp [value] (Zlength dp) (by omega)]
  simp [Znth0_cons]

theorem KnapsackRowProgress_append_cell (weights values : List Int) (capacity : Int)
    (dp : List Int) (row col value : Int)
    (hl : Zlength dp = KnapsackCellIndex capacity row col)
    (hp : KnapsackRowProgress weights values capacity dp row col)
    (hc : 0 ≤ col ∧ col ≤ capacity)
    (hv : KnapsackCellCorrect weights values row col value) :
    KnapsackRowProgress weights values capacity (dp ++ [value]) row (col + 1) := by
  intro r c hr hcc hidx
  by_cases hi : KnapsackCellIndex capacity r c < Zlength dp
  · rw [append_old dp value _ ⟨hidx.1, hi⟩]
    apply hp _ _ hr hcc
    exact ⟨hidx.1, by change _ < KnapsackCellIndex capacity row col; omega⟩
  · have he : KnapsackCellIndex capacity r c = KnapsackCellIndex capacity row col := by
      have hh := hidx.2
      change _ < row*(capacity+1)+(col+1) at hh
      unfold KnapsackCellIndex at *
      omega
    rcases Z_index_unique r row c col capacity (by omega) hcc hc he with ⟨rfl, rfl⟩
    rw [← hl, append_new]
    exact hv

private theorem append_bounded (dp : List Int) (value : Int)
    (hb : KnapsackTableValuesBounded dp) (hv : 0 ≤ value ∧ value ≤ 4000000) :
    KnapsackTableValuesBounded (dp ++ [value]) := by
  intro k hk
  have hl : Zlength (dp ++ [value]) = Zlength dp + 1 := by simp [Zlength]
  by_cases hi : k < Zlength dp
  · rw [append_old dp value k ⟨hk.1, hi⟩]; exact hb k ⟨hk.1, hi⟩
  · have he : k = Zlength dp := by omega
    rw [he, append_new]; exact hv

theorem append_zero_range (dp : List Int) (k : Int)
    (hb : ∀ i, (0 ≤ i ∧ i < Zlength dp) → 0 ≤ Znth i dp 0 ∧ Znth i dp 0 ≤ 4000000)
    (hk : 0 ≤ k ∧ k < Zlength (dp ++ [0])) :
    0 ≤ Znth k (dp ++ [0]) 0 ∧ Znth k (dp ++ [0]) 0 ≤ 4000000 :=
  append_bounded dp 0 hb ⟨by omega, by omega⟩ k hk

-- Coq's [remove] deletes every occurrence, so its direct Lean representation is filter.
theorem NoDup_remove_Z (x : Int) (l : List Int) (h : NoDup l) :
    NoDup (l.filter (· != x)) := List.Nodup.filter _ h

theorem Forall_remove_Z (P : Int → Prop) (x : Int) (l : List Int) (h : Forall P l) :
    Forall P (l.filter (· != x)) := by
  apply Forall.iff_forall_mem.mpr
  intro y hy
  exact h.mem (List.mem_filter.mp hy).1

theorem sum_map_remove_NoDup (f : Int → Int) (x : Int) (l : List Int)
    (hd : NoDup l) (hx : x ∈ l) :
    sum (l.map f) = f x + sum ((l.filter (· != x)).map f) := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    rcases List.nodup_cons.mp hd with ⟨ha, ht⟩
    by_cases he : a = x
    · subst a
      have hf : l.filter (· != x) = l := by
        apply List.filter_eq_self.mpr
        intro a hh
        simp only [bne_iff_ne]
        intro he; subst a; exact ha hh
      simp [List.filter_cons, hf, sum]
    · have hi : x ∈ l := by rcases List.mem_cons.mp hx with hh | hh; exact False.elim (he hh.symm); exact hh
      have hh := ih ht hi
      have hf : (a::l).filter (· != x) = a :: l.filter (· != x) := by simp [he]
      rw [hf]
      simp only [List.map_cons, sum, List.foldr_cons] at *
      omega

theorem KnapsackPlan_promote_item (weights values : List Int) (item cap value : Int)
    (hi : item < Zlength weights) (h : KnapsackPlan weights values item cap value) :
    KnapsackPlan weights values (item + 1) cap value := by
  rcases h with ⟨hic, hl, hc, picks, wt, hd, hp, hw, hb, hv⟩
  refine ⟨⟨by omega, by omega⟩, hl, hc, picks, wt, hd, ?_, hw, hb, hv⟩
  apply Forall.iff_forall_mem.mpr
  intro x hx; have := hp.mem hx; omega

theorem KnapsackPlan_add_item (weights values : List Int) (item cap value w v : Int)
    (hi : 0 ≤ item ∧ item < Zlength weights) (hw : 0 ≤ w)
    (hl : Zlength weights = Zlength values) (hwe : w = Znth item weights 0)
    (hve : v = Znth item values 0) (h : KnapsackPlan weights values item (cap - w) value) :
    KnapsackPlan weights values (item + 1) cap (value + v) := by
  rcases h with ⟨hic, hl', hc, picks, wt, hd, hp, hwt, hb, hv⟩
  refine ⟨⟨by omega, by omega⟩, hl, by omega, item :: picks, w + wt, ?_, ?_, ?_, by omega, hl, ?_⟩
  · apply List.nodup_cons.mpr; refine ⟨?_, hd⟩
    intro hin; have := hp.mem hin; omega
  · apply Forall.cons ⟨hi.1, by omega⟩
    apply Forall.iff_forall_mem.mpr
    intro x hx; have := hp.mem hx; omega
  · simp only [KnapsackPlanWeight, List.map_cons, sum, List.foldr_cons] at *
    omega
  · have hh := hv.2
    simp only [List.map_cons, sum, List.foldr_cons] at *
    omega

theorem sum_map_nonneg (f : Int → Int) (l : List Int)
    (h : ∀ x, x ∈ l → 0 ≤ f x) : 0 ≤ sum (l.map f) := by
  induction l with
  | nil => simp [sum]
  | cons a l ih =>
    have ha := h a (by simp)
    have ht := ih (by intro x hx; exact h x (by simp [hx]))
    simp only [List.map_cons, sum, List.foldr_cons] at *
    omega

theorem KnapsackPlan_split_last_item (weights values : List Int) (item cap value w v : Int)
    (hi : 0 ≤ item ∧ item < Zlength weights) (hl : Zlength weights = Zlength values)
    (hwe : w = Znth item weights 0) (hve : v = Znth item values 0)
    (hw : ∀ k, (0 ≤ k ∧ k < Zlength weights) → 0 ≤ Znth k weights 0)
    (h : KnapsackPlan weights values (item + 1) cap value) :
    (∃ old_value, KnapsackPlan weights values item (cap - w) old_value ∧ value = old_value + v) ∨
      KnapsackPlan weights values item cap value := by
  rcases h with ⟨hic, hl', hc, picks, wt, hd, hp, hwt, hb, hv⟩
  by_cases hin : item ∈ picks
  · left
    have hsumw := sum_map_remove_NoDup (fun i => Znth i weights 0) item picks hd hin
    have hsumv := sum_map_remove_NoDup (fun i => Znth i values 0) item picks hd hin
    have hnonneg : 0 ≤ sum ((picks.filter (· != item)).map (fun i => Znth i weights 0)) := by
      apply sum_map_nonneg
      intro x hx
      have hh := hp.mem (List.mem_filter.mp hx).1
      exact hw x ⟨hh.1, by omega⟩
    have hew : wt = w + sum ((picks.filter (· != item)).map (fun i => Znth i weights 0)) := by
      exact hwt.trans (by simpa [hwe] using hsumw)
    refine ⟨value-v, ?_, by omega⟩
    refine ⟨⟨hi.1, by omega⟩, hl, by omega, picks.filter (· != item), wt-w,
      NoDup_remove_Z _ _ hd, ?_, ?_, by omega, hl, ?_⟩
    · apply Forall.iff_forall_mem.mpr
      intro x hx
      rcases List.mem_filter.mp hx with ⟨hx, hne⟩
      have hh := hp.mem hx
      simp only [bne_iff_ne] at hne
      omega
    · unfold KnapsackPlanWeight; omega
    · change value-v = _
      rw [hv.2, hsumv, hve]
      dsimp
      omega
  · right
    refine ⟨⟨hi.1, by omega⟩, hl, hc, picks, wt, hd, ?_, hwt, hb, hv⟩
    apply Forall.iff_forall_mem.mpr
    intro x hx
    have hh := hp.mem hx
    have hn : x ≠ item := by intro he; subst x; exact hin hx
    omega

theorem KnapsackCellCorrect_take_better (weights values : List Int) (item j w v without prev : Int)
    (hi : 0 ≤ item ∧ item < Zlength weights) (hl : Zlength weights = Zlength values)
    (hwe : w = Znth item weights 0) (hve : v = Znth item values 0) (hw : 0 ≤ w)
    (hwn : ∀ k, (0 ≤ k ∧ k < Zlength weights) → 0 ≤ Znth k weights 0)
    (ho : KnapsackCellCorrect weights values item j without)
    (hp : KnapsackCellCorrect weights values item (j-w) prev) (hb : prev+v > without) :
    KnapsackCellCorrect weights values (item+1) j (prev+v) := by
  rcases (cell_iff _ _ _ _ _).mp ho with ⟨ho, hmo⟩
  rcases (cell_iff _ _ _ _ _).mp hp with ⟨hp, hmp⟩
  apply (cell_iff _ _ _ _ _).mpr
  refine ⟨KnapsackPlan_add_item _ _ _ _ _ _ _ hi hw hl hwe hve hp, ?_⟩
  intro b hplan
  rcases KnapsackPlan_split_last_item _ _ _ _ _ _ _ hi hl hwe hve hwn hplan with ⟨old, hpo, he⟩ | hpo
  · have := hmp old hpo; omega
  · have := hmo b hpo; omega

theorem KnapsackCellCorrect_keep_without_when_better_or_equal (weights values : List Int)
    (item j w v without prev : Int) (hi : 0 ≤ item ∧ item < Zlength weights)
    (hl : Zlength weights = Zlength values) (hwe : w = Znth item weights 0)
    (hve : v = Znth item values 0) (hw : 0 ≤ w)
    (hwn : ∀ k, (0 ≤ k ∧ k < Zlength weights) → 0 ≤ Znth k weights 0)
    (ho : KnapsackCellCorrect weights values item j without)
    (hp : KnapsackCellCorrect weights values item (j-w) prev) (hb : prev+v ≤ without) :
    KnapsackCellCorrect weights values (item+1) j without := by
  rcases (cell_iff _ _ _ _ _).mp ho with ⟨ho, hmo⟩
  rcases (cell_iff _ _ _ _ _).mp hp with ⟨hp, hmp⟩
  apply (cell_iff _ _ _ _ _).mpr
  refine ⟨KnapsackPlan_promote_item _ _ _ _ _ hi.2 ho, ?_⟩
  intro b hplan
  rcases KnapsackPlan_split_last_item _ _ _ _ _ _ _ hi hl hwe hve hwn hplan with ⟨old, hpo, he⟩ | hpo
  · have := hmp old hpo; omega
  · have := hmo b hpo; omega

theorem KnapsackCellCorrect_too_heavy (weights values : List Int) (item j w v without : Int)
    (hi : 0 ≤ item ∧ item < Zlength weights) (hl : Zlength weights = Zlength values)
    (hwe : w = Znth item weights 0) (hve : v = Znth item values 0) (hw : w > j)
    (hwn : ∀ k, (0 ≤ k ∧ k < Zlength weights) → 0 ≤ Znth k weights 0)
    (ho : KnapsackCellCorrect weights values item j without) :
    KnapsackCellCorrect weights values (item+1) j without := by
  rcases (cell_iff _ _ _ _ _).mp ho with ⟨ho, hmo⟩
  apply (cell_iff _ _ _ _ _).mpr
  refine ⟨KnapsackPlan_promote_item _ _ _ _ _ hi.2 ho, ?_⟩
  intro b hplan
  rcases KnapsackPlan_split_last_item _ _ _ _ _ _ _ hi hl hwe hve hwn hplan with ⟨old, hpo, he⟩ | hpo
  · have := hpo.2.2.1; omega
  · exact hmo b hpo

theorem Forall_range_incl_seq (picks : List Int) (n : Int) (hn : 0 ≤ n)
    (hp : Forall (fun i => 0 ≤ i ∧ i < n) picks) :
    incl picks ((seq 0 n.toNat).map Int.ofNat) := by
  intro x hx
  have hh := hp.mem hx
  apply List.mem_map.mpr
  refine ⟨x.toNat, ?_, Int.toNat_of_nonneg hh.1⟩
  apply List.mem_range'.mpr
  exact ⟨x.toNat, by omega, by omega⟩

theorem NoDup_Forall_range_length_le (picks : List Int) (n : Int) (hn : 0 ≤ n)
    (hd : NoDup picks) (hp : Forall (fun i => 0 ≤ i ∧ i < n) picks) :
    (picks.length : Int) ≤ n := by
  have hsub := Forall_range_incl_seq picks n hn hp
  have hh := (List.subperm_of_subset hd (by intro x hx; exact hsub x hx)).length_le
  simp only [List.length_map, seq, List.length_range'] at hh
  omega

theorem sum_map_values_bound (values picks : List Int) (n b : Int)
    (hp : Forall (fun i => 0 ≤ i ∧ i < n) picks)
    (hb : ∀ k, (0 ≤ k ∧ k < n) → 0 ≤ Znth k values 0 ∧ Znth k values 0 ≤ b) :
    0 ≤ sum (picks.map (fun i => Znth i values 0)) ∧
      sum (picks.map (fun i => Znth i values 0)) ≤ Zlength picks * b := by
  induction hp with
  | nil => simp [sum, Zlength]
  | @cons a l ha ht ih =>
    have hh := hb a ha
    simp only [List.map_cons, sum, List.foldr_cons] at *
    have hl : Zlength (a::l) = Zlength l + 1 := by simp [Zlength]
    rw [hl]
    constructor <;> nlinarith

theorem KnapsackCellCorrect_value_bound (weights values : List Int) (item cap value n : Int)
    (hlv : Zlength values = n) (hn : 0 ≤ n ∧ n ≤ 300)
    (hb : ∀ k, (0 ≤ k ∧ k < n) → 0 ≤ Znth k values 0 ∧ Znth k values 0 ≤ 10000)
    (hc : KnapsackCellCorrect weights values item cap value) : 0 ≤ value ∧ value ≤ 4000000 := by
  rcases (cell_iff _ _ _ _ _).mp hc with ⟨⟨hi, hl, _, picks, wt, hd, hp, _, _, hv⟩, _⟩
  have hpn : Forall (fun i => 0 ≤ i ∧ i < n) picks := by
    apply Forall.iff_forall_mem.mpr
    intro x hx; have := hp.mem hx; omega
  have hlen := NoDup_Forall_range_length_le picks n hn.1 hd hpn
  have hsum := sum_map_values_bound values picks n 10000 hpn hb
  rw [hv.2]
  change (picks.length : Int) ≤ n at hlen
  change 0 ≤ _ ∧ _ ≤ (picks.length : Int) * 10000 at hsum
  omega

theorem KnapsackRowProgress_append_cell_recurrence (weights values : List Int) (capacity : Int)
    (dp : List Int) (row col value : Int) (hc : 0 ≤ col ∧ col ≤ capacity)
    (hp : KnapsackRowProgress weights values capacity dp row col)
    (hl : Zlength dp = row * (capacity+1)+col)
    (hv : KnapsackCellCorrect weights values row col value) :
    KnapsackRowProgress weights values capacity (dp ++ [value]) row (col+1) :=
  KnapsackRowProgress_append_cell _ _ _ _ _ _ _ hl hp hc hv

theorem KnapsackMaxValue_parameters_nonnegative__dp_refinement_and_exit
    (weights values : List Int) (item_count capacity answer : Int)
    (h : KnapsackMaxValue weights values item_count capacity answer) : 0 ≤ item_count ∧ 0 ≤ capacity := by
  have hp := ((cell_iff _ _ _ _ _).mp h).1
  exact ⟨hp.1.1, hp.2.2.1⟩

theorem KnapsackRowAnnotationState_append_cell__row_state_result_refactor
    (weights values : List Int) (item_count capacity width : Int) (dp : List Int) (row col value : Int)
    (h : KnapsackRowAnnotationState weights values item_count capacity width dp row col)
    (hc : 0 ≤ col ∧ col ≤ capacity) (hcell : KnapsackCellCorrect weights values row col value)
    (hv : 0 ≤ value ∧ value ≤ 4000000) :
    KnapsackRowAnnotationState weights values item_count capacity width (dp ++ [value]) row (col+1) := by
  rcases h with ⟨hs, hr, hcol, hwritten, hshape, hb, hp⟩
  have hw := hs.2.2.1
  have hcap := hs.2.1
  refine ⟨hs, hr, ⟨by omega, by omega⟩, ?_, ?_, append_bounded dp value hb hv, ?_⟩
  · have hm := mul_le_mul_of_nonneg_right hr.2 (show 0 ≤ width by omega)
    constructor <;> nlinarith
  · refine ⟨by have := hshape.1; omega, ?_⟩
    have hl : Zlength (dp ++ [value]) = Zlength dp + 1 := by simp [Zlength]
    rw [hl, hshape.2]; omega
  · exact KnapsackRowProgress_append_cell_recurrence _ _ _ _ _ _ _ hc hp (by rw [hshape.2, hw]) hcell

theorem KnapsackRowsAnnotationState_to_Result__row_state_result_refactor
    (weights values : List Int) (item_count capacity width : Int) (dp : List Int)
    (h : KnapsackRowsAnnotationState weights values item_count capacity width dp (item_count+1)) :
    KnapsackResultState weights values item_count capacity dp (Znth (item_count*width+capacity) dp 0) := by
  rcases h with ⟨hs, _, _, hshape, hb, hd⟩
  have hi := hs.1
  have hc := hs.2.1
  have hw := hs.2.2.1
  have hidx : 0 ≤ KnapsackCellIndex capacity item_count capacity ∧
      KnapsackCellIndex capacity item_count capacity < (item_count+1)*(capacity+1) := by
    unfold KnapsackCellIndex
    constructor
    · exact add_nonneg (mul_nonneg hi.1 (by omega)) hc.1
    · nlinarith
  have he : item_count*width+capacity = KnapsackCellIndex capacity item_count capacity := by rw [hw]; rfl
  refine ⟨?_, ?_, ?_, hb, hd⟩
  · rw [he]; exact hd item_count capacity hi.1 ⟨hc.1, by omega⟩ hidx
  · apply hb
    rw [he, hshape.2, hw]; exact hidx
  · simpa only [hw] using hshape

end ProofSupport

open ProofSupport
open Algorithms.zero_one_knapsack.lean.groundtruth.zero_one_knapsack_goal

open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open Algorithms.zero_one_knapsack.lean.groundtruth.zero_one_knapsack_goal
open ProofSupport
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

private theorem previous_cell (weights values dp : List Int) (n capacity width i j col : Int)
    (hs : KnapsackRowAnnotationState weights values n capacity width dp i j)
    (hi : 1 ≤ i) (hcol : 0 ≤ col ∧ col ≤ capacity) (hcj : col ≤ j) :
    KnapsackCellCorrect weights values (i-1) col (Znth (((i-1)*width+col)-0) dp 0) := by
  have hw := hs.1.2.2.1
  have hcap := hs.1.2.1
  have he : ((i-1)*width+col)-0 = KnapsackCellIndex capacity (i-1) col := by rw [hw]; simp [KnapsackCellIndex]
  rw [he]
  apply hs.2.2.2.2.2.2 (i-1) col (by omega) hcol
  unfold KnapsackCellIndex
  constructor
  · exact add_nonneg (mul_nonneg (by omega) (by omega)) hcol.1
  · nlinarith

theorem proof_of_zeroOneKnapsack_safety_wit_22_split_goal_1 : zeroOneKnapsack_safety_wit_22_split_goal_1 := by
  unfold zeroOneKnapsack_safety_wit_22_split_goal_1
  intro dp_pre capacity_pre n_pre values_pre weights_pre values_l weights_l dp_l j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42
  have hs := PreH42.2.2.2.2.1
  have hb := PreH42.2.2.2.2.2.1 (((i-1)*width+(j-Znth (i-1) weights_l 0))-0) (by rw [hs.2]; omega)
  have hv := PreH42.1.2.2.2.2.2.2.2 (i-1) ⟨PreH14, PreH15⟩
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> omega

theorem proof_of_zeroOneKnapsack_safety_wit_22_split_goal_2 : zeroOneKnapsack_safety_wit_22_split_goal_2 := by
  unfold zeroOneKnapsack_safety_wit_22_split_goal_2
  intro dp_pre capacity_pre n_pre values_pre weights_pre values_l weights_l dp_l j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42
  have hs := PreH42.2.2.2.2.1
  have hb := PreH42.2.2.2.2.2.1 (((i-1)*width+(j-Znth (i-1) weights_l 0))-0) (by rw [hs.2]; omega)
  have hv := PreH42.1.2.2.2.2.2.2.2 (i-1) ⟨PreH14, PreH15⟩
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> omega

theorem proof_of_zeroOneKnapsack_safety_wit_22 : zeroOneKnapsack_safety_wit_22 := by
  unfold zeroOneKnapsack_safety_wit_22
  right
  intro dp_pre capacity_pre n_pre values_pre weights_pre values_l weights_l dp_l j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42
  have hs := PreH42.2.2.2.2.1
  have hb := PreH42.2.2.2.2.2.1 (((i-1)*width+(j-Znth (i-1) weights_l 0))-0) (by rw [hs.2]; omega)
  have hv := PreH42.1.2.2.2.2.2.2.2 (i-1) ⟨PreH14, PreH15⟩
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> omega

theorem proof_of_zeroOneKnapsack_safety_wit_29_split_goal_1 : zeroOneKnapsack_safety_wit_29_split_goal_1 := by
  unfold zeroOneKnapsack_safety_wit_29_split_goal_1
  intro dp_pre capacity_pre n_pre values_pre weights_pre values_l weights_l dp_l width PreH1 PreH2 PreH3 PreH4
  prop_apply (intArray.full_length_range dp_pre ((n_pre+1)*(capacity_pre+1)) dp_l)
  Intros_p hsize
  change 0 ≤ (n_pre+1)*(capacity_pre+1)*4 ∧ (n_pre+1)*(capacity_pre+1)*4 ≤ 4294967296 at hsize
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> omega

theorem proof_of_zeroOneKnapsack_safety_wit_29_split_goal_2 : zeroOneKnapsack_safety_wit_29_split_goal_2 := by
  unfold zeroOneKnapsack_safety_wit_29_split_goal_2
  intro dp_pre capacity_pre n_pre values_pre weights_pre values_l weights_l dp_l width PreH1 PreH2 PreH3 PreH4
  prop_apply (intArray.full_length_range dp_pre ((n_pre+1)*(capacity_pre+1)) dp_l)
  Intros_p hsize
  change 0 ≤ (n_pre+1)*(capacity_pre+1)*4 ∧ (n_pre+1)*(capacity_pre+1)*4 ≤ 4294967296 at hsize
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> omega

theorem proof_of_zeroOneKnapsack_safety_wit_29 : zeroOneKnapsack_safety_wit_29 := by
  unfold zeroOneKnapsack_safety_wit_29
  right
  intro dp_pre capacity_pre n_pre values_pre weights_pre values_l weights_l dp_l width PreH1 PreH2 PreH3 PreH4
  prop_apply (intArray.full_length_range dp_pre ((n_pre+1)*(capacity_pre+1)) dp_l)
  Intros_p hsize
  change 0 ≤ (n_pre+1)*(capacity_pre+1)*4 ∧ (n_pre+1)*(capacity_pre+1)*4 ≤ 4294967296 at hsize
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> omega

theorem proof_of_zeroOneKnapsack_safety_wit_30_split_goal_1 : zeroOneKnapsack_safety_wit_30_split_goal_1 := by
  unfold zeroOneKnapsack_safety_wit_30_split_goal_1
  intro dp_pre capacity_pre n_pre values_pre weights_pre values_l weights_l dp_l width PreH1 PreH2 PreH3 PreH4
  prop_apply (intArray.full_length_range dp_pre ((n_pre+1)*(capacity_pre+1)) dp_l)
  Intros_p hsize
  change 0 ≤ (n_pre+1)*(capacity_pre+1)*4 ∧ (n_pre+1)*(capacity_pre+1)*4 ≤ 4294967296 at hsize
  have hp := KnapsackMaxValue_parameters_nonnegative__dp_refinement_and_exit _ _ _ _ _ PreH4.1
  have hn := mul_nonneg hp.1 (show 0 ≤ width by omega)
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> nlinarith

theorem proof_of_zeroOneKnapsack_safety_wit_30_split_goal_2 : zeroOneKnapsack_safety_wit_30_split_goal_2 := by
  unfold zeroOneKnapsack_safety_wit_30_split_goal_2
  intro dp_pre capacity_pre n_pre values_pre weights_pre values_l weights_l dp_l width PreH1 PreH2 PreH3 PreH4
  prop_apply (intArray.full_length_range dp_pre ((n_pre+1)*(capacity_pre+1)) dp_l)
  Intros_p hsize
  change 0 ≤ (n_pre+1)*(capacity_pre+1)*4 ∧ (n_pre+1)*(capacity_pre+1)*4 ≤ 4294967296 at hsize
  have hp := KnapsackMaxValue_parameters_nonnegative__dp_refinement_and_exit _ _ _ _ _ PreH4.1
  have hn := mul_nonneg hp.1 (show 0 ≤ width by omega)
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> nlinarith

theorem proof_of_zeroOneKnapsack_safety_wit_30 : zeroOneKnapsack_safety_wit_30 := by
  unfold zeroOneKnapsack_safety_wit_30
  right
  intro dp_pre capacity_pre n_pre values_pre weights_pre values_l weights_l dp_l width PreH1 PreH2 PreH3 PreH4
  prop_apply (intArray.full_length_range dp_pre ((n_pre+1)*(capacity_pre+1)) dp_l)
  Intros_p hsize
  change 0 ≤ (n_pre+1)*(capacity_pre+1)*4 ∧ (n_pre+1)*(capacity_pre+1)*4 ≤ 4294967296 at hsize
  have hp := KnapsackMaxValue_parameters_nonnegative__dp_refinement_and_exit _ _ _ _ _ PreH4.1
  have hn := mul_nonneg hp.1 (show 0 ≤ width by omega)
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> nlinarith

theorem proof_of_zeroOneKnapsack_entail_wit_1 : zeroOneKnapsack_entail_wit_1 := by
  unfold zeroOneKnapsack_entail_wit_1
  right
  intro dp_pre capacity_pre n_pre values_l weights_l PreH1 PreH2 PreH3 PreH4 PreH5
  have hs : KnapsackRowsAnnotationState weights_l values_l n_pre capacity_pre (capacity_pre+1) [] 0 := by
    refine ⟨⟨⟨PreH1, PreH2⟩, ⟨PreH3, PreH4⟩, rfl, ⟨by omega, by omega⟩, PreH5⟩,
      ⟨by omega, by omega⟩, ?_, ?_, ?_, ?_⟩
    · simp only [Int.zero_mul]; exact ⟨by omega, mul_nonneg (by omega) (by omega)⟩
    · simp [KnapsackTablePrefixShape, Zlength]
    · intro k hk; simp [Zlength] at hk; omega
    · intro r c hr hc hi; simp only [Int.zero_mul] at hi; omega
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ([] : List Int) ?_
  simp only [Int.zero_mul]
  sep_apply (intArray.undef_full_to_undef_seg dp_pre ((n_pre+1)*(capacity_pre+1)))
  sep_apply_right (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp
    (intArray.seg_empty dp_pre 0 0)).2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hs | omega

theorem proof_of_zeroOneKnapsack_entail_wit_2 : zeroOneKnapsack_entail_wit_2 := by
  unfold zeroOneKnapsack_entail_wit_2
  right
  intro dp_pre capacity_pre n_pre values_l weights_l dp_l_2 i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have hs : KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l_2 i 0 := by
    rcases PreH9 with ⟨hs, hr, htotal, hshape, hb, hd⟩
    refine ⟨hs, ⟨PreH7, PreH1⟩, ⟨by omega, by omega⟩, ?_, ?_, hb, ?_⟩
    · simpa only [Int.add_zero] using htotal
    · simpa only [Int.add_zero] using hshape
    · exact KnapsackRowsDone_to_RowProgress0 _ _ _ _ _ PreH5 hd
  refine Automation.exp_right_rule (CRules := naive_C_Rules) dp_l_2 ?_
  simp only [Int.add_zero]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hs | omega

theorem proof_of_zeroOneKnapsack_entail_wit_3_split_goal_1 : zeroOneKnapsack_entail_wit_3_split_goal_1 := by
  unfold zeroOneKnapsack_entail_wit_3_split_goal_1
  intro capacity_pre n_pre values_l weights_l dp_l j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have hm := mul_le_mul_of_nonneg_right PreH20 (show 0 ≤ capacity_pre+1 by omega)
  nlinarith

theorem proof_of_zeroOneKnapsack_entail_wit_3 : zeroOneKnapsack_entail_wit_3 := by
  unfold zeroOneKnapsack_entail_wit_3
  right
  intro capacity_pre n_pre values_l weights_l dp_l j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_zeroOneKnapsack_entail_wit_3_split_goal_1 capacity_pre n_pre values_l weights_l dp_l j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23

theorem proof_of_zeroOneKnapsack_entail_wit_5_split_goal_1 : zeroOneKnapsack_entail_wit_5_split_goal_1 := by
  unfold zeroOneKnapsack_entail_wit_5_split_goal_1
  intro capacity_pre n_pre values_l weights_l dp_l j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  nlinarith

theorem proof_of_zeroOneKnapsack_entail_wit_5 : zeroOneKnapsack_entail_wit_5 := by
  unfold zeroOneKnapsack_entail_wit_5
  right
  intro capacity_pre n_pre values_l weights_l dp_l j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_zeroOneKnapsack_entail_wit_5_split_goal_1 capacity_pre n_pre values_l weights_l dp_l j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35

theorem proof_of_zeroOneKnapsack_entail_wit_6_split_goal_1 : zeroOneKnapsack_entail_wit_6_split_goal_1 := by
  unfold zeroOneKnapsack_entail_wit_6_split_goal_1
  intro capacity_pre n_pre values_l weights_l dp_l j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  have hw := PreH40.1.2.2.2.2.2.2.1 (i-1) ⟨PreH12, PreH13⟩
  nlinarith

theorem proof_of_zeroOneKnapsack_entail_wit_6 : zeroOneKnapsack_entail_wit_6 := by
  unfold zeroOneKnapsack_entail_wit_6
  right
  intro capacity_pre n_pre values_l weights_l dp_l j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_zeroOneKnapsack_entail_wit_6_split_goal_1 capacity_pre n_pre values_l weights_l dp_l j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40

theorem proof_of_zeroOneKnapsack_entail_wit_7_1 : zeroOneKnapsack_entail_wit_7_1 := by
  unfold zeroOneKnapsack_entail_wit_7_1
  right
  intro dp_pre capacity_pre n_pre values_l weights_l dp_l_2 j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have hinput := PreH24.1.2.2.2.2
  have hlen : Zlength weights_l = Zlength values_l := by rw [hinput.1, hinput.2.1]
  have hcell : KnapsackCellCorrect weights_l values_l i j 0 := by
    rw [PreH1]; exact KnapsackCellCorrect_row0_zero _ _ _ PreH22 hlen
  have hv : (0 : Int) ≤ 0 ∧ (0 : Int) ≤ 4000000 := ⟨by omega, by omega⟩
  have hs := KnapsackRowAnnotationState_append_cell__row_state_result_refactor _ _ _ _ _ _ _ _ _
    PreH24 ⟨by omega, by omega⟩ hcell hv
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (dp_l_2++[(0 : Int)]) ?_
  rw [show i*width+(j+1) = i*width+j+1 by omega]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hs | omega

theorem proof_of_zeroOneKnapsack_entail_wit_7_2 : zeroOneKnapsack_entail_wit_7_2 := by
  unfold zeroOneKnapsack_entail_wit_7_2
  right
  intro dp_pre capacity_pre n_pre values_l weights_l dp_l_2 j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hinput := PreH25.1.2.2.2.2
  have hlen : Zlength weights_l = Zlength values_l := by rw [hinput.1, hinput.2.1]
  have hcell : KnapsackCellCorrect weights_l values_l i j 0 := by
    rw [PreH1]
    apply KnapsackCellCorrect_col0_zero _ _ _ ⟨PreH21, by rw [hinput.1]; omega⟩ hlen
    intro k hk
    exact (hinput.2.2.1 k ⟨hk.1, by omega⟩).1
  have hv : (0 : Int) ≤ 0 ∧ (0 : Int) ≤ 4000000 := ⟨by omega, by omega⟩
  have hs := KnapsackRowAnnotationState_append_cell__row_state_result_refactor _ _ _ _ _ _ _ _ _
    PreH25 ⟨by omega, by omega⟩ hcell hv
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (dp_l_2++[(0 : Int)]) ?_
  rw [show i*width+(j+1) = i*width+j+1 by omega]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hs | omega

theorem proof_of_zeroOneKnapsack_entail_wit_7_3 : zeroOneKnapsack_entail_wit_7_3 := by
  unfold zeroOneKnapsack_entail_wit_7_3
  right
  intro dp_pre capacity_pre n_pre values_l weights_l dp_l_2 j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43
  have hinput := PreH43.1.2.2.2.2
  have hlen : Zlength weights_l = Zlength values_l := by rw [hinput.1, hinput.2.1]
  have hnonneg : ∀ k, (0 ≤ k ∧ k < Zlength weights_l) → 0 ≤ Znth k weights_l 0 := by
    intro k hk; have hh := hinput.2.2.1 k ⟨hk.1, by rw [← hinput.1]; exact hk.2⟩; omega
  have ho := previous_cell _ _ _ _ _ _ _ _ j PreH43 (by omega) ⟨by omega, by omega⟩ (by omega)
  have hw := hinput.2.2.1 (i-1) ⟨PreH15, PreH16⟩
  have hp := previous_cell _ _ _ _ _ _ _ _ (j-Znth (i-1) weights_l 0) PreH43
    (by omega) ⟨by omega, by omega⟩ (by omega)
  have hc := KnapsackCellCorrect_take_better _ _ (i-1) j (Znth (i-1) weights_l 0)
    (Znth (i-1) values_l 0) _ _ ⟨PreH15, by rw [hinput.1]; omega⟩ hlen rfl rfl (by omega) hnonneg ho hp PreH1
  have hcell := hc
  rw [show i-1+1 = i by omega] at hcell
  have hv := KnapsackCellCorrect_value_bound _ _ _ _ _ n_pre hinput.2.1
    ⟨by omega, by omega⟩ hinput.2.2.2 hcell
  have hs := KnapsackRowAnnotationState_append_cell__row_state_result_refactor _ _ _ _ _ _ _ _ _
    PreH43 ⟨by omega, by omega⟩ hcell hv
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (dp_l_2++[(Znth (((i-1)*width+(j-Znth (i-1) weights_l 0))-0) dp_l_2 0 + Znth (i-1) values_l 0)]) ?_
  rw [show i*width+(j+1) = i*width+j+1 by omega]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hs | omega

theorem proof_of_zeroOneKnapsack_entail_wit_7_4 : zeroOneKnapsack_entail_wit_7_4 := by
  unfold zeroOneKnapsack_entail_wit_7_4
  right
  intro dp_pre capacity_pre n_pre values_l weights_l dp_l_2 j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43
  have hinput := PreH43.1.2.2.2.2
  have hlen : Zlength weights_l = Zlength values_l := by rw [hinput.1, hinput.2.1]
  have hnonneg : ∀ k, (0 ≤ k ∧ k < Zlength weights_l) → 0 ≤ Znth k weights_l 0 := by
    intro k hk; have hh := hinput.2.2.1 k ⟨hk.1, by rw [← hinput.1]; exact hk.2⟩; omega
  have ho := previous_cell _ _ _ _ _ _ _ _ j PreH43 (by omega) ⟨by omega, by omega⟩ (by omega)
  have hw := hinput.2.2.1 (i-1) ⟨PreH15, PreH16⟩
  have hp := previous_cell _ _ _ _ _ _ _ _ (j-Znth (i-1) weights_l 0) PreH43
    (by omega) ⟨by omega, by omega⟩ (by omega)
  have hc := KnapsackCellCorrect_keep_without_when_better_or_equal _ _ (i-1) j (Znth (i-1) weights_l 0)
    (Znth (i-1) values_l 0) _ _ ⟨PreH15, by rw [hinput.1]; omega⟩ hlen rfl rfl (by omega) hnonneg ho hp PreH1
  have hcell := hc
  rw [show i-1+1 = i by omega] at hcell
  have hv := KnapsackCellCorrect_value_bound _ _ _ _ _ n_pre hinput.2.1
    ⟨by omega, by omega⟩ hinput.2.2.2 hcell
  have hs := KnapsackRowAnnotationState_append_cell__row_state_result_refactor _ _ _ _ _ _ _ _ _
    PreH43 ⟨by omega, by omega⟩ hcell hv
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (dp_l_2++[(Znth (((i-1)*width+j)-0) dp_l_2 0)]) ?_
  rw [show i*width+(j+1) = i*width+j+1 by omega]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hs | omega

theorem proof_of_zeroOneKnapsack_entail_wit_7_5 : zeroOneKnapsack_entail_wit_7_5 := by
  unfold zeroOneKnapsack_entail_wit_7_5
  right
  intro dp_pre capacity_pre n_pre values_l weights_l dp_l_2 j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  have hinput := PreH38.1.2.2.2.2
  have hlen : Zlength weights_l = Zlength values_l := by rw [hinput.1, hinput.2.1]
  have hnonneg : ∀ k, (0 ≤ k ∧ k < Zlength weights_l) → 0 ≤ Znth k weights_l 0 := by
    intro k hk; have hh := hinput.2.2.1 k ⟨hk.1, by rw [← hinput.1]; exact hk.2⟩; omega
  have ho := previous_cell _ _ _ _ _ _ _ _ j PreH38 (by omega) ⟨by omega, by omega⟩ (by omega)
  have hc := KnapsackCellCorrect_too_heavy _ _ (i-1) j (Znth (i-1) weights_l 0)
    (Znth (i-1) values_l 0) _ ⟨PreH10, by rw [hinput.1]; omega⟩ hlen rfl rfl PreH1 hnonneg ho
  have hcell := hc
  rw [show i-1+1 = i by omega] at hcell
  have hv := KnapsackCellCorrect_value_bound _ _ _ _ _ n_pre hinput.2.1
    ⟨by omega, by omega⟩ hinput.2.2.2 hcell
  have hs := KnapsackRowAnnotationState_append_cell__row_state_result_refactor _ _ _ _ _ _ _ _ _
    PreH38 ⟨by omega, by omega⟩ hcell hv
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (dp_l_2++[(Znth (((i-1)*width+j)-0) dp_l_2 0)]) ?_
  rw [show i*width+(j+1) = i*width+j+1 by omega]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hs | omega

theorem proof_of_zeroOneKnapsack_entail_wit_8 : zeroOneKnapsack_entail_wit_8 := by
  unfold zeroOneKnapsack_entail_wit_8
  right
  intro dp_pre capacity_pre n_pre values_l weights_l dp_l_2 j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have hj : j = capacity_pre+1 := by omega
  have he : (i+1)*width = i*width+j := by nlinarith
  have hs : KnapsackRowsAnnotationState weights_l values_l n_pre capacity_pre width dp_l_2 (i+1) := by
    rcases PreH11 with ⟨hs, hr, hc, htotal, hshape, hb, hp⟩
    refine ⟨hs, ⟨by omega, by omega⟩, ?_, ?_, hb, ?_⟩
    · rw [he]; exact htotal
    · rw [he]; exact hshape
    · exact KnapsackRowProgress_end_to_RowsDone _ _ _ _ _ _ hj hp
  refine Automation.exp_right_rule (CRules := naive_C_Rules) dp_l_2 ?_
  rw [he]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hs | omega

theorem proof_of_zeroOneKnapsack_entail_wit_9 : zeroOneKnapsack_entail_wit_9 := by
  unfold zeroOneKnapsack_entail_wit_9
  right
  intro dp_pre capacity_pre n_pre values_l weights_l dp_l_2 i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have hi : i = n_pre+1 := by omega
  have hs := KnapsackRowsAnnotationState_to_Result__row_state_result_refactor _ _ _ _ _ _ (by rw [← hi]; exact PreH9)
  have he : i*width = (n_pre+1)*(capacity_pre+1) := by rw [hi, PreH2]
  refine Automation.exp_right_rule (CRules := naive_C_Rules) dp_l_2 ?_
  rw [he]
  split_pure_spatial
  · sep_apply (intArray.seg_to_full dp_pre 0 ((n_pre+1)*(capacity_pre+1)) dp_l_2)
    simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
    sep_apply (intArray.undef_seg_empty dp_pre ((n_pre+1)*(capacity_pre+1)))
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hs | omega

theorem proof_of_zeroOneKnapsack_entail_wit_10_split_goal_1 : zeroOneKnapsack_entail_wit_10_split_goal_1 := by
  unfold zeroOneKnapsack_entail_wit_10_split_goal_1
  intro capacity_pre n_pre values_l weights_l dp_l width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have hp := KnapsackMaxValue_parameters_nonnegative__dp_refinement_and_exit _ _ _ _ _ PreH8.1
  have hm := mul_nonneg hp.1 (show 0 ≤ capacity_pre+1 by omega)
  nlinarith

theorem proof_of_zeroOneKnapsack_entail_wit_10_split_goal_2 : zeroOneKnapsack_entail_wit_10_split_goal_2 := by
  unfold zeroOneKnapsack_entail_wit_10_split_goal_2
  intro capacity_pre n_pre values_l weights_l dp_l width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have hp := KnapsackMaxValue_parameters_nonnegative__dp_refinement_and_exit _ _ _ _ _ PreH8.1
  have hm := mul_nonneg hp.1 (show 0 ≤ capacity_pre+1 by omega)
  nlinarith

theorem proof_of_zeroOneKnapsack_entail_wit_10 : zeroOneKnapsack_entail_wit_10 := by
  unfold zeroOneKnapsack_entail_wit_10
  right
  intro capacity_pre n_pre values_l weights_l dp_l width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_zeroOneKnapsack_entail_wit_10_split_goal_1 capacity_pre n_pre values_l weights_l dp_l width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
      | exact proof_of_zeroOneKnapsack_entail_wit_10_split_goal_2 capacity_pre n_pre values_l weights_l dp_l width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8

end Algorithms.zero_one_knapsack.lean.groundtruth.zero_one_knapsack_proof_manual
