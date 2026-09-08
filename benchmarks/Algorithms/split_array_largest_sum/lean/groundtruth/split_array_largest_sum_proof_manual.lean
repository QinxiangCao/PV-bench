import Algorithms.split_array_largest_sum.lean.groundtruth.split_array_largest_sum_goal
import Algorithms.split_array_largest_sum.lean.groundtruth.split_array_largest_sum_proof_auto
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import ListLib.General.Length

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace Algorithms.split_array_largest_sum.lean.groundtruth.split_array_largest_sum_proof_manual

open Algorithms.split_array_largest_sum.lean
open scoped SimpleC

namespace ProofSupport

open AUXLib


open MaxMinLib

def NotPartitionMaxSegmentSum (l : List Int) (m max_sum : Int) : Prop :=
  ¬ PartitionMaxSegmentSum l m max_sum

private theorem minimum_iff (P : Int → Prop) (v : Int) :
    min_value_of_subset (· ≤ ·) P id v ↔ P v ∧ ∀ x, P x → v ≤ x := by
  constructor
  · rintro ⟨x, ⟨hx, hm⟩, rfl⟩; exact ⟨hx, hm⟩
  · rintro ⟨hx, hm⟩; exact ⟨v, ⟨hx, hm⟩, rfl⟩

private theorem forall_snoc {A : Type} {P : A → Prop} {l : List A} {x : A}
    (hl : Forall P l) (hx : P x) : Forall P (l++[x]) := by
  apply Forall.iff_forall_mem.mpr
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact hl.mem ha
  · simpa using List.mem_singleton.mp ha ▸ hx

theorem minimized_partition_witness (l : List Int) (m answer : Int)
    (h : MinimizedMaxSegmentSum l m answer) : PartitionMaxSegmentSum l m answer :=
  ((minimum_iff _ _).mp h).1

theorem minimized_lower_bound (l : List Int) (m answer max_sum : Int)
    (h : MinimizedMaxSegmentSum l m answer) (hp : PartitionMaxSegmentSum l m max_sum) :
    answer ≤ max_sum := ((minimum_iff _ _).mp h).2 _ hp

theorem minmax_not_partition_below (l : List Int) (m answer cap : Int)
    (h : MinimizedMaxSegmentSum l m answer) (hc : cap < answer) :
    NotPartitionMaxSegmentSum l m cap := by
  intro hp; have := minimized_lower_bound _ _ _ _ h hp; omega

theorem can_split_cannot_contradiction (l : List Int) (m cap : Int)
    (hc : CanSplit l m cap) (hn : CannotSplit l m cap) : False := by
  rcases hc with ⟨cnt, cur, hs, hle⟩
  have := hn cnt cur hs; omega

theorem mid_quot_bounds (left right : Int) (hl : 0 ≤ left) (hlt : left < right)
    (hr : right ≤ 1000000000) :
    0 ≤ left + Z.quot (right-left) 2 ∧ left + Z.quot (right-left) 2 ≤ 1000000000 := by
  have hq := Z.quot_pos (right-left) 2 (by omega) (by omega)
  have hu := Z.quot_le_upper_bound (right-left) 2 (right-left) (by omega) (by omega)
  omega

theorem prefix_split_state_zero (l : List Int) (cap : Int) (h : 0 ≤ cap) :
    PrefixSplitState l cap 0 1 0 := .PrefixSplitState_zero h

theorem prefix_split_state_step_over_cap (l : List Int) (cap n i cnt cur : Int)
    (hl : Zlength l = n)
    (hb : ∀ k, (0 ≤ k ∧ k < n) → 0 ≤ Znth k l 0 ∧ Znth k l 0 < 100000000)
    (hi : 0 ≤ i) (hin : i < n) (hv : Znth i l 0 ≤ cap)
    (hcur : cur+Znth i l 0 > cap) (hs : PrefixSplitState l cap i cnt cur) :
    PrefixSplitState l cap (i+1) (cnt+1) (Znth i l 0) :=
  .PrefixSplitState_new_segment i cnt cur ⟨hi, by omega⟩ ⟨(hb i ⟨hi, hin⟩).1, hv⟩ hcur hs

theorem prefix_split_state_extend_no_split (l : List Int) (cap i cnt cur : Int)
    (hn : ∀ k, (0 ≤ k ∧ k < Zlength l) → 0 ≤ Znth k l 0) (hi : 0 ≤ i)
    (hv : Znth i l 0 ≤ cap) (hcur : cur+Znth i l 0 ≤ cap) (hin : i < Zlength l)
    (hs : PrefixSplitState l cap i cnt cur) :
    PrefixSplitState l cap (i+1) cnt (cur+Znth i l 0) :=
  .PrefixSplitState_extend i cnt cur ⟨hi, hin⟩ ⟨hn i ⟨hi, hin⟩, hv⟩ hcur hs

theorem PrefixSplitState_items_bound (l : List Int) (cap i cnt cur : Int)
    (hs : PrefixSplitState l cap i cnt cur) :
    ∀ k, (0 ≤ k ∧ k < i) → 0 ≤ Znth k l 0 ∧ Znth k l 0 ≤ cap := by
  induction hs with
  | PrefixSplitState_zero => intro k hk; omega
  | PrefixSplitState_new_segment i cnt cur hi hv hc hs ih
  | PrefixSplitState_extend i cnt cur hi hv hc hs ih =>
    intro k hk
    by_cases he : k = i
    · subst k; exact hv
    · exact ih k ⟨hk.1, by omega⟩

private theorem state_unique (l : List Int) (cap i cnt cur : Int)
    (hs : PrefixSplitState l cap i cnt cur) :
    ∀ j cnt' cur', PrefixSplitState l cap j cnt' cur' → i = j → cnt = cnt' ∧ cur = cur' := by
  induction hs with
  | PrefixSplitState_zero hcap =>
    intro j cnt' cur' ht he
    cases ht with
    | PrefixSplitState_zero => exact ⟨rfl, rfl⟩
    | PrefixSplitState_new_segment j cnt' cur' hj => omega
    | PrefixSplitState_extend j cnt' cur' hj => omega
  | PrefixSplitState_new_segment i cnt cur hi hv hc hs ih =>
    intro j cnt' cur' ht he
    cases ht with
    | PrefixSplitState_zero => omega
    | PrefixSplitState_new_segment j cnt' cur' hj hv' hc' ht =>
      have hij : i = j := by omega
      rcases ih j cnt' cur' ht hij with ⟨rfl, rfl⟩
      subst j; exact ⟨rfl, rfl⟩
    | PrefixSplitState_extend j cnt' cur' hj hv' hc' ht =>
      have hij : i = j := by omega
      rcases ih j cnt' cur' ht hij with ⟨hh, hh'⟩
      subst j; omega
  | PrefixSplitState_extend i cnt cur hi hv hc hs ih =>
    intro j cnt' cur' ht he
    cases ht with
    | PrefixSplitState_zero => omega
    | PrefixSplitState_new_segment j cnt' cur' hj hv' hc' ht =>
      have hij : i = j := by omega
      rcases ih j cnt' cur' ht hij with ⟨hh, hh'⟩
      subst j; omega
    | PrefixSplitState_extend j cnt' cur' hj hv' hc' ht =>
      have hij : i = j := by omega
      rcases ih j cnt' cur' ht hij with ⟨rfl, rfl⟩
      subst j; exact ⟨rfl, rfl⟩

theorem PrefixSplitState_unique (l : List Int) (cap i cnt1 cur1 cnt2 cur2 : Int)
    (h1 : PrefixSplitState l cap i cnt1 cur1) (h2 : PrefixSplitState l cap i cnt2 cur2) :
    cnt1 = cnt2 ∧ cur1 = cur2 := state_unique _ _ _ _ _ h1 _ _ _ h2 rfl

theorem sum_snoc (l : List Int) (x : Int) : sum (l++[x]) = sum l+x := by
  rw [sum_app]; simp [sum]

theorem sublist_snoc_Znth {A : Type} (d : A) (l : List A) (i : Int)
    (hi : 0 ≤ i ∧ i < Zlength l) : sublist 0 (i+1) l = sublist 0 i l ++ [Znth i l d] := by
  rw [sublist_split 0 (i+1) i l ⟨by omega, hi.1⟩ ⟨by omega, by omega⟩, sublist_single d i l hi]

private abbrev Good (cap : Int) (seg : List Int) : Prop :=
  seg ≠ [] ∧ sum seg ≤ cap ∧ ∀ x, x ∈ seg → 0 ≤ x

theorem prefix_state_partition (l : List Int) (cap i cnt cur : Int)
    (hs : PrefixSplitState l cap i cnt cur) :
    ∃ (done : List (List Int)) (curseg : List Int),
      sublist 0 i l = (done++[curseg]).flatten ∧ Zlength done+1 = cnt ∧ sum curseg = cur ∧
      Forall (fun seg => seg ≠ [] ∧ sum seg ≤ cap ∧ ∀ x, x ∈ seg → 0 ≤ x) done ∧
      sum curseg ≤ cap ∧ (∀ x, x ∈ curseg → 0 ≤ x) ∧
      ((i = 0 ∧ curseg = []) ∨ (0 < i ∧ curseg ≠ [])) := by
  induction hs with
  | PrefixSplitState_zero hcap =>
    exact ⟨[], [], rfl, rfl, rfl, .nil, hcap, by simp, Or.inl ⟨rfl, rfl⟩⟩
  | PrefixSplitState_new_segment i cnt cur hi hv hc hs ih =>
    rcases ih with ⟨done, seg, hcat, hcnt, hsum, hd, hcap, hn, hshape⟩
    have hne : seg ≠ [] := by
      rcases hshape with ⟨rfl, rfl⟩ | ⟨_, hn⟩
      · change 0 = cur at hsum; omega
      · exact hn
    refine ⟨done++[seg], [Znth i l 0], ?_, ?_, ?_, forall_snoc hd ⟨hne, hcap, hn⟩, ?_, ?_, ?_⟩
    · rw [sublist_snoc_Znth 0 l i hi, hcat]
      simp [List.flatten_append]
    · rw [Zlength_app, Zlength_cons, Zlength_nil]; omega
    · simp [sum]
    · simpa [sum] using hv.2
    · intro x hx; have he := List.mem_singleton.mp hx; rw [he]; exact hv.1
    · exact Or.inr ⟨by omega, by simp⟩
  | PrefixSplitState_extend i cnt cur hi hv hc hs ih =>
    rcases ih with ⟨done, seg, hcat, hcnt, hsum, hd, hcap, hn, hshape⟩
    refine ⟨done, seg++[Znth i l 0], ?_, hcnt, ?_, hd, ?_, ?_, ?_⟩
    · rw [sublist_snoc_Znth 0 l i hi, hcat]
      simp [List.flatten_append, List.append_assoc]
    · rw [sum_snoc, hsum]
    · rw [sum_snoc, hsum]; exact hc
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hn x hx
      · have he := List.mem_singleton.mp hx; rw [he]; exact hv.1
    · exact Or.inr ⟨by omega, by simp⟩

theorem can_split_bounded_partition_at_most (l : List Int) (m cap : Int)
    (hl : 0 < Zlength l) (hc : CanSplit l m cap) :
    ∃ parts : List (List Int), parts.flatten = l ∧ Zlength parts ≤ m ∧
      Forall (fun seg => seg ≠ [] ∧ sum seg ≤ cap ∧ ∀ x, x ∈ seg → 0 ≤ x) parts := by
  rcases hc with ⟨cnt, cur, hs, hcnt⟩
  rcases prefix_state_partition _ _ _ _ _ hs with ⟨done, seg, hcat, hcount, hsum, hd, hcap, hn, hshape⟩
  have hne : seg ≠ [] := by rcases hshape with ⟨h, _⟩ | ⟨_, h⟩; omega; exact h
  refine ⟨done++[seg], ?_, ?_, forall_snoc hd ⟨hne, hcap, hn⟩⟩
  · rw [← hcat, sublist_self l _ rfl]
  · rw [Zlength_app, Zlength_cons, Zlength_nil]; omega

theorem max_segment_sum_exists (parts : List (List Int)) (hn : parts ≠ []) :
    ∃ max_sum, MaxSegmentSum parts max_sum := by
  induction parts with
  | nil => contradiction
  | cons seg rest ih =>
    by_cases hr : rest = []
    · subst rest
      refine ⟨sum seg, seg, ⟨by simp, ?_⟩, rfl⟩
      intro b hb; have he := List.mem_singleton.mp hb; rw [he]
    · rcases ih hr with ⟨v, best, ⟨hbest, hmax⟩, he⟩
      by_cases hh : sum seg ≤ v
      · refine ⟨v, best, ⟨by simp [hbest], ?_⟩, he⟩
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact he ▸ hh
        · exact hmax b hb
      · refine ⟨sum seg, seg, ⟨by simp, ?_⟩, rfl⟩
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact le_refl _
        · have hm := hmax b hb; dsimp at hm he ⊢; omega

theorem sum_nonnegative (seg : List Int) (hn : ∀ x, x ∈ seg → 0 ≤ x) : 0 ≤ sum seg := by
  induction seg with
  | nil => simp [sum]
  | cons a l ih =>
    have ha := hn a (by simp)
    have ht := ih (by intro x hx; exact hn x (by simp [hx]))
    change 0 ≤ a+sum l; omega

theorem sublist_cons_tail {A : Type} (d : A) (l : List A) (i : Int) (x : A) (xs : List A)
    (hi : 0 ≤ i) (hb : i+1+Zlength xs ≤ Zlength l)
    (hs : sublist i (i+1+Zlength xs) l = x::xs) :
    Znth i l d = x ∧ sublist (i+1) (i+1+Zlength xs) l = xs := by
  have hl := Zlength_nonneg xs
  rw [sublist_split i (i+1+Zlength xs) (i+1) l ⟨hi, by omega⟩ ⟨by omega, hb⟩,
    sublist_single d i l ⟨hi, by omega⟩] at hs
  exact List.cons.inj hs

theorem prefix_state_cur_bounds (l : List Int) (cap i cnt cur : Int)
    (hs : PrefixSplitState l cap i cnt cur) : 0 ≤ cur ∧ cur ≤ cap := by
  induction hs with
  | PrefixSplitState_zero hcap => omega
  | PrefixSplitState_new_segment i cnt cur hi hv => exact hv
  | PrefixSplitState_extend i cnt cur hi hv hc hs ih => omega

theorem process_segment_no_new (l : List Int) (cap i cnt cur : Int) (seg : List Int)
    (hs : PrefixSplitState l cap i cnt cur) (hi : 0 ≤ i)
    (hb : i+Zlength seg ≤ Zlength l) (hsub : sublist i (i+Zlength seg) l = seg)
    (hcap : cur+sum seg ≤ cap) (hn : ∀ x, x ∈ seg → 0 ≤ x) :
    ∃ cur', PrefixSplitState l cap (i+Zlength seg) cnt cur' ∧ cur' = cur+sum seg := by
  induction seg generalizing i cnt cur with
  | nil => exact ⟨cur, by simpa [Zlength] using hs, by simp [sum]⟩
  | cons x xs ih =>
    have hxl := Zlength_nonneg xs
    have he : i+Zlength (x::xs) = i+1+Zlength xs := by rw [Zlength_cons]; omega
    rw [he] at hb hsub ⊢
    rcases sublist_cons_tail 0 l i x xs hi hb hsub with ⟨hx, ht⟩
    have htn : ∀ x, x ∈ xs → 0 ≤ x := by intro y hy; exact hn y (by simp [hy])
    have hts := sum_nonnegative xs htn
    have hxn := hn x (by simp)
    have hcur := prefix_state_cur_bounds _ _ _ _ _ hs
    change cur+(x+sum xs) ≤ cap at hcap
    have hstep : PrefixSplitState l cap (i+1) cnt (cur+x) := by
      rw [← hx]
      exact .PrefixSplitState_extend i cnt cur ⟨hi, by omega⟩ ⟨by rw [hx]; omega, by rw [hx]; omega⟩ (by rw [hx]; omega) hs
    rcases ih (i+1) cnt (cur+x) hstep (by omega) hb ht (by omega) htn with ⟨cur', hf, hc⟩
    exact ⟨cur', hf, by change cur' = cur+(x+sum xs); omega⟩

theorem process_segment_one_new (l : List Int) (cap i cnt cur : Int) (seg : List Int)
    (hs : PrefixSplitState l cap i cnt cur) (hi : 0 ≤ i)
    (hb : i+Zlength seg ≤ Zlength l) (hsub : sublist i (i+Zlength seg) l = seg)
    (hcap : sum seg ≤ cap) (hn : ∀ x, x ∈ seg → 0 ≤ x) :
    ∃ cnt' cur', PrefixSplitState l cap (i+Zlength seg) cnt' cur' ∧ cnt' ≤ cnt+1 := by
  induction seg generalizing i cnt cur with
  | nil => exact ⟨cnt, cur, by simpa [Zlength] using hs, by omega⟩
  | cons x xs ih =>
    have hxl := Zlength_nonneg xs
    have he : i+Zlength (x::xs) = i+1+Zlength xs := by rw [Zlength_cons]; omega
    rw [he] at hb hsub ⊢
    rcases sublist_cons_tail 0 l i x xs hi hb hsub with ⟨hx, ht⟩
    have htn : ∀ x, x ∈ xs → 0 ≤ x := by intro y hy; exact hn y (by simp [hy])
    have hts := sum_nonnegative xs htn
    have hxn := hn x (by simp)
    change x+sum xs ≤ cap at hcap
    by_cases hfit : cur+x ≤ cap
    · have hstep : PrefixSplitState l cap (i+1) cnt (cur+x) := by
        rw [← hx]
        exact .PrefixSplitState_extend i cnt cur ⟨hi, by omega⟩ ⟨by rw [hx]; omega, by rw [hx]; omega⟩ (by rw [hx]; omega) hs
      exact ih (i+1) cnt (cur+x) hstep (by omega) hb ht (by omega) htn
    · have hstep : PrefixSplitState l cap (i+1) (cnt+1) x := by
        rw [← hx]
        exact .PrefixSplitState_new_segment i cnt cur ⟨hi, by omega⟩ ⟨by rw [hx]; omega, by rw [hx]; omega⟩ (by rw [hx]; omega) hs
      rcases process_segment_no_new l cap (i+1) (cnt+1) x xs hstep (by omega) hb ht hcap htn with ⟨cur', hf, _⟩
      exact ⟨cnt+1, cur', hf, by omega⟩

theorem app_eq_same_zlength {A : Type} (a b c d : List A) (he : a++b = c++d)
    (hl : Zlength a = Zlength c) : a = c ∧ b = d :=
  List.append_inj he (by exact Int.ofNat.inj hl)

theorem split_sublist_at_prefix {A : Type} (d : A) (l pre rest : List A) (i : Int)
    (hi : 0 ≤ i) (hb : i+Zlength (pre++rest) ≤ Zlength l)
    (hs : sublist i (i+Zlength (pre++rest)) l = pre++rest) :
    sublist i (i+Zlength pre) l = pre ∧
      sublist (i+Zlength pre) (i+Zlength (pre++rest)) l = rest := by
  have hp := Zlength_nonneg pre
  have hr := Zlength_nonneg rest
  have hl : Zlength (pre++rest) = Zlength pre+Zlength rest := Zlength_app _ _
  rw [sublist_split i (i+Zlength (pre++rest)) (i+Zlength pre) l ⟨hi, by omega⟩ ⟨by omega, hb⟩] at hs
  apply app_eq_same_zlength _ _ _ _ hs
  have hh : Zlength (sublist i (i+Zlength pre) l) = i+Zlength pre-i :=
    ListLib.Zlength_sublist i (i+Zlength pre) l ⟨hi, by omega⟩ (by change i+Zlength pre ≤ Zlength l; omega)
  omega

theorem process_parts_one_new_each (l : List Int) (cap i cnt cur : Int) (parts : List (List Int))
    (hs : PrefixSplitState l cap i cnt cur) (hi : 0 ≤ i)
    (hb : i+Zlength parts.flatten ≤ Zlength l)
    (hsub : sublist i (i+Zlength parts.flatten) l = parts.flatten)
    (hg : Forall (fun seg => seg ≠ [] ∧ sum seg ≤ cap ∧ ∀ x, x ∈ seg → 0 ≤ x) parts) :
    ∃ cnt' cur', PrefixSplitState l cap (i+Zlength parts.flatten) cnt' cur' ∧ cnt' ≤ cnt+Zlength parts := by
  induction hg generalizing i cnt cur with
  | nil => exact ⟨cnt, cur, by simpa [Zlength] using hs, by simp [Zlength]⟩
  | @cons seg rest hseg hrest ih =>
    change i+Zlength (seg++rest.flatten) ≤ Zlength l at hb
    change sublist i (i+Zlength (seg++rest.flatten)) l = seg++rest.flatten at hsub
    rcases split_sublist_at_prefix 0 l seg rest.flatten i hi hb hsub with ⟨hsegsub, hrestsub⟩
    have hsl := Zlength_nonneg seg
    have hrl := Zlength_nonneg rest.flatten
    rw [Zlength_app] at hb
    rcases process_segment_one_new l cap i cnt cur seg hs hi (by omega) hsegsub hseg.2.1 hseg.2.2 with ⟨cnt1, cur1, hs1, hc1⟩
    have ht : sublist (i+Zlength seg) (i+Zlength seg+Zlength rest.flatten) l = rest.flatten := by
      convert hrestsub using 2 <;> rw [Zlength_app] <;> omega
    rcases ih (i+Zlength seg) cnt1 cur1 hs1 (by omega) (by omega) ht with ⟨cnt', cur', hs', hc'⟩
    refine ⟨cnt', cur', ?_, ?_⟩
    · simpa only [List.flatten_cons, Zlength_app, Int.add_assoc] using hs'
    · rw [Zlength_cons]; omega

theorem bounded_partition_to_can_split (l : List Int) (m cap : Int) (parts : List (List Int))
    (hc : 0 ≤ cap) (hne : parts ≠ []) (hcat : parts.flatten = l) (hl : Zlength parts = m)
    (hg : Forall (fun seg => seg ≠ [] ∧ sum seg ≤ cap ∧ ∀ x, x ∈ seg → 0 ≤ x) parts) :
    CanSplit l m cap := by
  cases hg with
  | nil => contradiction
  | @cons first rest hf hr =>
    change first++rest.flatten = l at hcat
    have hwhole : sublist 0 (0+Zlength (first++rest.flatten)) l = first++rest.flatten := by
      rw [hcat]; simpa only [Int.zero_add] using sublist_self l (Zlength l) rfl
    rcases split_sublist_at_prefix 0 l first rest.flatten 0 (by omega) (by rw [hcat]; omega) hwhole with ⟨hfs, hrs⟩
    have hfl := Zlength_nonneg first
    have hrl := Zlength_nonneg rest.flatten
    have hlen : Zlength first+Zlength rest.flatten = Zlength l := by rw [← Zlength_app, hcat]
    rcases process_segment_no_new l cap 0 1 0 first (.PrefixSplitState_zero hc) (by omega)
      (by omega) hfs (by simpa using hf.2.1) hf.2.2 with ⟨cur1, hs1, _⟩
    simp only [Int.zero_add] at hs1 hrs
    have hrs' : sublist (Zlength first) (Zlength first+Zlength rest.flatten) l = rest.flatten := by
      simpa only [Zlength_app] using hrs
    rcases process_parts_one_new_each l cap (Zlength first) 1 cur1 rest hs1 hfl (by omega) hrs' hr with ⟨cnt', cur', hs', hc'⟩
    refine ⟨cnt', cur', ?_, ?_⟩
    · rw [← hlen]; exact hs'
    · rw [Zlength_cons] at hl; omega

theorem in_list_nonnegative (l : List Int) (x : Int) (hx : x ∈ l)
    (hn : ∀ i, (0 ≤ i ∧ i < Zlength l) → 0 ≤ Znth i l 0) : 0 ≤ x := by
  induction l with
  | nil => simp at hx
  | cons a rest ih =>
    have hl := Zlength_nonneg rest
    rcases List.mem_cons.mp hx with rfl | hx
    · have hh := hn 0 ⟨by omega, by rw [Zlength_cons]; omega⟩
      simpa only [Znth0_cons] using hh
    · apply ih hx
      intro i hi
      have hh := hn (i+1) ⟨by omega, by rw [Zlength_cons]; omega⟩
      rw [Znth_cons 0 (i+1) a rest (by omega)] at hh
      simpa only [show i+1-1 = i by omega] using hh

theorem partition_max_segments_good (l : List Int) (parts : List (List Int)) (max_sum cap : Int)
    (hcat : parts.flatten = l) (hne : Forall (fun seg => seg ≠ []) parts)
    (hm : MaxSegmentSum parts max_sum) (hc : max_sum ≤ cap)
    (hn : ∀ i, (0 ≤ i ∧ i < Zlength l) → 0 ≤ Znth i l 0) :
    Forall (fun seg => seg ≠ [] ∧ sum seg ≤ cap ∧ ∀ x, x ∈ seg → 0 ≤ x) parts := by
  rcases hm with ⟨best, ⟨hb, hmax⟩, he⟩
  apply Forall.iff_forall_mem.mpr
  intro seg hs
  have hh := hmax seg hs
  refine ⟨hne.mem hs, by dsimp at hh he; omega, ?_⟩
  intro x hx
  apply in_list_nonnegative l x ?_ hn
  rw [← hcat]; exact List.mem_flatten.mpr ⟨seg, hs, hx⟩

theorem partition_max_to_can_split (l : List Int) (m max_sum cap : Int) (hc : 0 ≤ cap)
    (hn : ∀ i, (0 ≤ i ∧ i < Zlength l) → 0 ≤ Znth i l 0)
    (hp : PartitionMaxSegmentSum l m max_sum) (hm : max_sum ≤ cap) : CanSplit l m cap := by
  rcases hp with ⟨parts, ⟨hne, hcat, hparts⟩, hl, hmax⟩
  exact bounded_partition_to_can_split l m cap parts hc hne hcat hl
    (partition_max_segments_good l parts max_sum cap hcat hparts hmax hm hn)

theorem refine_partition_once (cap : Int) (parts : List (List Int))
    (hg : Forall (fun seg => seg ≠ [] ∧ sum seg ≤ cap ∧ ∀ x, x ∈ seg → 0 ≤ x) parts)
    (hl : Zlength parts < Zlength parts.flatten) :
    ∃ parts' : List (List Int), parts'.flatten = parts.flatten ∧ Zlength parts' = Zlength parts+1 ∧
      Forall (fun seg => seg ≠ [] ∧ sum seg ≤ cap ∧ ∀ x, x ∈ seg → 0 ≤ x) parts' := by
  induction hg with
  | nil => simp [Zlength] at hl
  | @cons seg rest hs hr ih =>
    rcases hs with ⟨hne, hsum, hn⟩
    cases seg with
    | nil => contradiction
    | cons x xs =>
      cases xs with
      | nil =>
        have hlen : Zlength rest < Zlength rest.flatten := by
          simp only [List.flatten_cons, List.singleton_append, Zlength_cons] at hl
          omega
        rcases ih hlen with ⟨rest', hcat, hlen, hg⟩
        refine ⟨[x]::rest', ?_, ?_, .cons ⟨by simp, hsum, hn⟩ hg⟩
        · simp only [List.flatten_cons, hcat]
        · rw [Zlength_cons, Zlength_cons, hlen]
      | cons y ys =>
        have hxn := hn x (by simp)
        have htn : ∀ z, z ∈ y::ys → 0 ≤ z := by intro z hz; exact hn z (by simp [hz])
        have hts := sum_nonnegative (y::ys) htn
        change x+sum (y::ys) ≤ cap at hsum
        refine ⟨[x]::(y::ys)::rest, rfl, ?_, .cons ?_ (.cons ?_ hr)⟩
        · simp only [Zlength_cons]
        · refine ⟨by simp, ?_, ?_⟩
          · change x+0 ≤ cap; omega
          · intro z hz; have he := List.mem_singleton.mp hz; rw [he]; exact hxn
        · exact ⟨by simp, by omega, htn⟩

theorem refine_partition_to_target_fuel (fuel : Nat) (cap : Int) (parts : List (List Int)) (target : Int)
    (hg : Forall (fun seg => seg ≠ [] ∧ sum seg ≤ cap ∧ ∀ x, x ∈ seg → 0 ≤ x) parts)
    (hr : Zlength parts ≤ target ∧ target ≤ Zlength parts.flatten)
    (hf : target-Zlength parts ≤ (fuel : Int)) :
    ∃ parts' : List (List Int), parts'.flatten = parts.flatten ∧ Zlength parts' = target ∧
      Forall (fun seg => seg ≠ [] ∧ sum seg ≤ cap ∧ ∀ x, x ∈ seg → 0 ≤ x) parts' := by
  induction fuel generalizing parts with
  | zero => exact ⟨parts, rfl, by omega, hg⟩
  | succ fuel ih =>
    by_cases he : target = Zlength parts
    · exact ⟨parts, rfl, he.symm, hg⟩
    · rcases refine_partition_once cap parts hg (by omega) with ⟨parts1, hcat, hlen, hg1⟩
      rcases ih parts1 hg1 ⟨by omega, by rw [hcat]; exact hr.2⟩ (by omega) with ⟨parts', hcat', hlen', hg'⟩
      exact ⟨parts', hcat'.trans hcat, hlen', hg'⟩

theorem refine_partition_to_target (cap : Int) (parts : List (List Int)) (target : Int)
    (hg : Forall (fun seg => seg ≠ [] ∧ sum seg ≤ cap ∧ ∀ x, x ∈ seg → 0 ≤ x) parts)
    (hr : Zlength parts ≤ target ∧ target ≤ Zlength parts.flatten) :
    ∃ parts' : List (List Int), parts'.flatten = parts.flatten ∧ Zlength parts' = target ∧
      Forall (fun seg => seg ≠ [] ∧ sum seg ≤ cap ∧ ∀ x, x ∈ seg → 0 ≤ x) parts' :=
  refine_partition_to_target_fuel (target-Zlength parts).toNat cap parts target hg hr (by omega)

theorem max_segment_sum_bound (cap : Int) (parts : List (List Int)) (max_sum : Int)
    (hg : Forall (fun seg => seg ≠ [] ∧ sum seg ≤ cap ∧ ∀ x, x ∈ seg → 0 ≤ x) parts)
    (hm : MaxSegmentSum parts max_sum) : max_sum ≤ cap := by
  rcases hm with ⟨seg, ⟨hs, _⟩, he⟩
  have hh := (hg.mem hs).2.1
  dsimp at he; omega

theorem good_segments_nonnil (cap : Int) (parts : List (List Int))
    (hg : Forall (fun seg => seg ≠ [] ∧ sum seg ≤ cap ∧ ∀ x, x ∈ seg → 0 ≤ x) parts) :
    Forall (fun seg => seg ≠ []) parts := by
  apply Forall.iff_forall_mem.mpr
  intro seg hs; exact (hg.mem hs).1

theorem can_split_to_partition_max (l : List Int) (m cap : Int) (hm : 1 ≤ m)
    (hml : m ≤ Zlength l) (hl : 0 < Zlength l) (hc : CanSplit l m cap) :
    ∃ max_sum, PartitionMaxSegmentSum l m max_sum ∧ max_sum ≤ cap := by
  rcases can_split_bounded_partition_at_most l m cap hl hc with ⟨parts, hcat, hlen, hg⟩
  rcases refine_partition_to_target cap parts m hg ⟨hlen, by rw [hcat]; exact hml⟩ with ⟨parts', hcat', hlen', hg'⟩
  have hne : parts' ≠ [] := by intro he; rw [he, Zlength_nil] at hlen'; omega
  rcases max_segment_sum_exists parts' hne with ⟨max_sum, hmax⟩
  exact ⟨max_sum, ⟨parts', ⟨hne, hcat'.trans hcat, good_segments_nonnil cap parts' hg'⟩, hlen', hmax⟩,
    max_segment_sum_bound cap parts' max_sum hg' hmax⟩

theorem minmax_can_lower_bound (l : List Int) (m answer cap : Int)
    (hm : 1 ≤ m ∧ m ≤ Zlength l)
    (_ : ∀ i, (0 ≤ i ∧ i < Zlength l) → 0 ≤ Znth i l 0)
    (hmin : MinimizedMaxSegmentSum l m answer) (hc : CanSplit l m cap) : answer ≤ cap := by
  rcases can_split_to_partition_max l m cap hm.1 hm.2 (by omega) hc with ⟨v, hp, hv⟩
  have := minimized_lower_bound _ _ _ _ hmin hp; omega

theorem minmax_cannot_upper_bound (l : List Int) (m answer cap : Int) (hc : 0 ≤ cap)
    (hn : ∀ i, (0 ≤ i ∧ i < Zlength l) → 0 ≤ Znth i l 0)
    (hmin : MinimizedMaxSegmentSum l m answer) (hcannot : CannotSplit l m cap) : cap < answer := by
  by_contra hh
  have hpart := minimized_partition_witness _ _ _ hmin
  exact can_split_cannot_contradiction _ _ _
    (partition_max_to_can_split _ _ _ _ hc hn hpart (by omega)) hcannot

end ProofSupport

open ProofSupport
open Algorithms.split_array_largest_sum.lean.groundtruth.split_array_largest_sum_goal

open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open Algorithms.split_array_largest_sum.lean.groundtruth.split_array_largest_sum_goal
open ProofSupport
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

private theorem quot_half_lt (a : Int) (ha : 0 < a) : Z.quot a 2 < a := by
  by_cases he : a = 1
  · subst a; decide
  · have h := Z.quot_le_upper_bound a 2 (a-1) (by omega) (by omega)
    omega

theorem proof_of_check_entail_wit_1 : check_entail_wit_1 := by
  unfold check_entail_wit_1
  right
  intro cap_pre m_pre n_pre l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact PreH8 | exact prefix_split_state_zero l cap_pre PreH5

theorem proof_of_check_entail_wit_2_1 : check_entail_wit_2_1 := by
  unfold check_entail_wit_2_1
  right
  intro cap_pre m_pre n_pre l cur cnt i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    exact prefix_split_state_step_over_cap _ _ _ _ _ _ PreH10 PreH11 PreH12 PreH3 PreH2 PreH1 PreH18

theorem proof_of_check_entail_wit_2_2 : check_entail_wit_2_2 := by
  unfold check_entail_wit_2_2
  right
  intro cap_pre m_pre n_pre l cur cnt i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    exact PrefixSplitState_extend i cnt cur ⟨PreH12, by omega⟩ ⟨(PreH11 i ⟨PreH12, PreH3⟩).1, PreH2⟩ PreH1 PreH18

theorem proof_of_check_return_wit_1 : check_return_wit_1 := by
  unfold check_return_wit_1
  right
  intro cap_pre m_pre n_pre l cur cnt i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    intro _ cnt' cur' hs
    have hpre : PrefixSplitState l cap_pre (Zlength l) cnt cur := by
      rw [show Zlength l = i by omega]; exact PreH17
    have hh := PrefixSplitState_unique _ _ _ _ _ _ _ hpre hs
    omega

theorem proof_of_check_return_wit_2 : check_return_wit_2 := by
  unfold check_return_wit_2
  right
  intro cap_pre m_pre n_pre l cur cnt i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    intro _
    exact ⟨cnt, cur, by rw [show Zlength l = i by omega]; exact PreH17, PreH1⟩

theorem proof_of_check_return_wit_3 : check_return_wit_3 := by
  unfold check_return_wit_3
  right
  intro cap_pre m_pre n_pre l cur cnt i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    intro _ cnt' cur' hs
    have hh := PrefixSplitState_items_bound _ _ _ _ _ hs i ⟨PreH11, by omega⟩
    omega

theorem proof_of_splitArrayLargestSum_safety_wit_3 : splitArrayLargestSum_safety_wit_3 := by
  unfold splitArrayLargestSum_safety_wit_3
  right
  intro m_pre n_pre arr_pre l res right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hm := mid_quot_bounds left right PreH8 PreH1 PreH9
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> omega

theorem proof_of_splitArrayLargestSum_safety_wit_7 : splitArrayLargestSum_safety_wit_7 := by
  unfold splitArrayLargestSum_safety_wit_7
  right
  intro m_pre n_pre arr_pre l res right left retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hm := mid_quot_bounds left right PreH12 PreH5 PreH13
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> omega

theorem proof_of_splitArrayLargestSum_entail_wit_1 : splitArrayLargestSum_entail_wit_1 := by
  unfold splitArrayLargestSum_entail_wit_1
  right
  intro m_pre n_pre l ans PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ans ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact PreH7 | omega

theorem proof_of_splitArrayLargestSum_entail_wit_2_1 : splitArrayLargestSum_entail_wit_2_1 := by
  unfold splitArrayLargestSum_entail_wit_2_1
  right
  intro m_pre n_pre l res_2 right left retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hm := mid_quot_bounds left right PreH12 PreH5 PreH13
  have hq := Z.quot_pos (right-left) 2 (by omega) (by omega)
  have hb := minmax_can_lower_bound l m_pre res_2 (left+Z.quot (right-left) 2)
    ⟨PreH8, by omega⟩ (by intro k hk; exact (PreH11 k ⟨hk.1, by omega⟩).1) PreH17 (PreH3 (by omega))
  refine Automation.exp_right_rule (CRules := naive_C_Rules) res_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact PreH17 | omega

theorem proof_of_splitArrayLargestSum_entail_wit_2_2 : splitArrayLargestSum_entail_wit_2_2 := by
  unfold splitArrayLargestSum_entail_wit_2_2
  right
  intro m_pre n_pre l res_2 right left retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hm := mid_quot_bounds left right PreH12 PreH5 PreH13
  have hq := quot_half_lt (right-left) (by omega)
  have hb := minmax_cannot_upper_bound l m_pre res_2 (left+Z.quot (right-left) 2) hm.1
    (by intro k hk; exact (PreH11 k ⟨hk.1, by omega⟩).1) PreH17 (PreH4 PreH18)
  refine Automation.exp_right_rule (CRules := naive_C_Rules) res_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact PreH17 | omega

theorem proof_of_splitArrayLargestSum_partial_solve_wit_1_pure : splitArrayLargestSum_partial_solve_wit_1_pure := by
  unfold splitArrayLargestSum_partial_solve_wit_1_pure
  right
  intro m_pre n_pre arr_pre l res right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have hm := mid_quot_bounds left right PreH18 PreH11 PreH19
  split_pures <;> dump_pre_spatial
  all_goals first | exact PreH17 | omega

theorem proof_of_splitArrayLargestSum_return_wit_1 : splitArrayLargestSum_return_wit_1 := by
  unfold splitArrayLargestSum_return_wit_1
  right
  intro m_pre n_pre l res right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    rw [show left = res by omega]; exact PreH13

end Algorithms.split_array_largest_sum.lean.groundtruth.split_array_largest_sum_proof_manual
