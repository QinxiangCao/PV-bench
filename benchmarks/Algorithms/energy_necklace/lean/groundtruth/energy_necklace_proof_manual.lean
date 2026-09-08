import Algorithms.energy_necklace.lean.groundtruth.energy_necklace_goal
import Algorithms.energy_necklace.lean.groundtruth.energy_necklace_proof_auto
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import ListLib.General.Length

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace Algorithms.energy_necklace.lean.groundtruth.energy_necklace_proof_manual

open Algorithms.energy_necklace.lean

open AUXLib

private theorem maximum_iff (P : Int → Prop) (v : Int) :
    MaxMinLib.max_value_of_subset (· ≤ ·) P id v ↔ P v ∧ ∀ x, P x → x ≤ v := by
  constructor
  · rintro ⟨x, ⟨hx, hl⟩, rfl⟩; exact ⟨hx, hl⟩
  · rintro ⟨hx, hl⟩; exact ⟨v, ⟨hx, hl⟩, rfl⟩

private theorem max_scan_step (P : Int → Int → Prop) (lo cut best candidate : Int)
    (hlo : lo ≤ cut) (hc : P cut candidate) (hcn : 0 ≤ candidate)
    (huniq : ∀ k a b, P k a → P k b → a = b)
    (hscan : (cut = lo ∧ best = 0) ∨ (lo < cut ∧
      MaxMinLib.max_value_of_subset (· ≤ ·) (fun v => ∃ k, (lo ≤ k ∧ k < cut) ∧ P k v) id best)) :
    MaxMinLib.max_value_of_subset (· ≤ ·)
      (fun v => ∃ k, (lo ≤ k ∧ k < cut+1) ∧ P k v) id (max best candidate) := by
  apply (maximum_iff _ _).mpr
  constructor
  · rcases hscan with ⟨he, hb⟩ | ⟨hlt, hm⟩
    · rw [hb, max_eq_right hcn]
      exact ⟨cut, ⟨hlo, by omega⟩, hc⟩
    · by_cases hb : best ≤ candidate
      · rw [max_eq_right hb]; exact ⟨cut, ⟨hlo, by omega⟩, hc⟩
      · rw [max_eq_left (by omega : candidate ≤ best)]
        obtain ⟨k, hk, hp⟩ := ((maximum_iff _ best).mp hm).1
        exact ⟨k, ⟨hk.1, by omega⟩, hp⟩
  · rintro v ⟨k, hk, hp⟩
    by_cases hlt : k < cut
    · have hs := hscan.resolve_left (by intro h; omega)
      exact le_trans (((maximum_iff _ best).mp hs.2).2 v ⟨k, ⟨hk.1, hlt⟩, hp⟩) (le_max_left _ _)
    · have he : k = cut := by omega
      subst k
      rw [huniq cut v candidate hp hc]
      exact le_max_right _ _

private theorem index_bounds (width l r : Int) (hw : 0 < width)
    (hl : 0 ≤ l ∧ l < width) (hr : 0 ≤ r ∧ r < width) :
    0 ≤ EnergyCellIndex width l r ∧ EnergyCellIndex width l r < width*width := by
  unfold EnergyCellIndex
  constructor
  · exact add_nonneg (mul_nonneg hl.1 (by omega)) hr.1
  · nlinarith

theorem EnergyValsDuplicated_label_bound__arithmetic_safety_bounds (beads vals : List Int) (n i : Int)
    (hd : EnergyValsDuplicated beads vals n) (hb : EnergyLabelsBounded beads n) (hi : 0 ≤ i ∧ i < 2*n) :
    1 ≤ Znth i vals 0 ∧ Znth i vals 0 ≤ 1000 := by
  by_cases hl : i < n
  · rw [hd.2.2.2.1 i ⟨hi.1, hl⟩]; exact hb.2 i ⟨hi.1, hl⟩
  · have he : i = n+(i-n) := by omega
    rw [he, hd.2.2.2.2 (i-n) ⟨by omega, by omega⟩]
    exact hb.2 (i-n) ⟨by omega, by omega⟩

theorem EnergySplitArithmeticBounded_from_progress__arithmetic_safety_bounds
    (beads vals dp : List Int) (n total width len left right split best bound : Int)
    (hb : EnergyComputationBounded beads n bound) (hd : EnergyValsDuplicated beads vals n)
    (ht : total = 2*n) (hw : width = total) (hl : 2 ≤ len ∧ len ≤ n)
    (hlf : 0 ≤ left ∧ left < total-len) (hr : right = left+len-1)
    (hk : left ≤ split ∧ split < right) (hsize : Zlength dp = total*width)
    (hp : EnergySplitProgress vals dp total width len left split best) :
    EnergySplitArithmeticBounded vals dp width left right split bound :=
  hb.2.1 vals dp total width len left right split hd ht hw hl hlf hr hk hsize hp.1.1

theorem EnergyIntervalBest_single_zero__prefix_table_bootstrap (vals : List Int) (left : Int)
    (hl : 0 ≤ left) (hr : left+1 < Zlength vals) : EnergyIntervalBest vals left left 0 := by
  apply (maximum_iff _ _).mpr
  refine ⟨EnergyIntervalPlan_single left hl hr, ?_⟩
  intro cost hp
  cases hp with
  | EnergyIntervalPlan_single => omega
  | EnergyIntervalPlan_merge l k r lc rc hl hb => omega

theorem EnergyZeroTable_len_done_2__prefix_table_bootstrap (vals dp : List Int) (total width : Int)
    (hv : Zlength vals = total) (hz : EnergyZeroTable dp total width) :
    EnergyLenDone vals dp total width 2 := by
  refine ⟨hz.1, hz.2.1, hv, hz.2.2.1, by omega, ?_⟩
  intro l left right idx hl hr hi hleft hfit
  have he : l = 1 := by omega
  have her : right = left := by omega
  subst l
  rw [her, hi, her]
  have hb := index_bounds width left left (by have := hz.2.1; omega)
    ⟨hleft, by have := hz.2.1; omega⟩ ⟨hleft, by have := hz.2.1; omega⟩
  rw [hz.2.2.2 _ (by rw [←hz.2.1]; exact hb)]
  exact EnergyIntervalBest_single_zero__prefix_table_bootstrap vals left hleft hfit

theorem EnergyZeroTable_from_prefix__prefix_table_bootstrap (dp : List Int) (total width i : Int)
    (ht : 0 ≤ total) (hw : width = total) (hge : i ≥ total*width) (hle : i ≤ total*width)
    (hlen : Zlength dp = i) (hz : ∀ k, (0 ≤ k ∧ k < i) → Znth k dp 0 = 0) :
    EnergyZeroTable dp total width := ⟨ht, hw, by omega, fun k hk => hz k ⟨hk.1, by omega⟩⟩

theorem EnergySplitCandidate_ext_eq__dp_interval_progress (vals dp : List Int)
    (width left right split a b : Int) (ha : EnergySplitCandidate vals dp width left right split a)
    (hb : EnergySplitCandidate vals dp width left right split b) : a = b := ha.2.2.trans hb.2.2.symm

theorem EnergySplitProgress_step_keep__dp_interval_progress (vals dp : List Int)
    (total width len left right split best candidate : Int) (hr : right = left+len-1)
    (hk : left ≤ split ∧ split < right) (hp : EnergySplitProgress vals dp total width len left split best)
    (hc : EnergySplitCandidate vals dp width left right split candidate) (hc0 : 0 ≤ candidate) (hb : candidate ≤ best) :
    EnergySplitProgress vals dp total width len left (split+1) best := by
  rcases hp with ⟨hlp, hlen, hleft, hfit, hre, hsplit, hbest, hscan⟩
  refine ⟨hlp, hlen, hleft, hfit, rfl, ⟨by omega, by omega⟩, hbest, Or.inr ⟨by omega, ?_⟩⟩
  rw [hr] at hc
  simpa only [max_eq_left hb] using max_scan_step (EnergySplitCandidate vals dp width left (left+len-1))
    left split best candidate hk.1 hc hc0 (EnergySplitCandidate_ext_eq__dp_interval_progress vals dp width left (left+len-1)) hscan

theorem EnergySplitProgress_step_take__dp_interval_progress (vals dp : List Int)
    (total width len left right split best candidate : Int) (hr : right = left+len-1)
    (hk : left ≤ split ∧ split < right) (hp : EnergySplitProgress vals dp total width len left split best)
    (hc : EnergySplitCandidate vals dp width left right split candidate) (hcb : 0 ≤ candidate ∧ candidate ≤ 2100000000)
    (hb : best < candidate) : EnergySplitProgress vals dp total width len left (split+1) candidate := by
  rcases hp with ⟨hlp, hlen, hleft, hfit, hre, hsplit, hbest, hscan⟩
  refine ⟨hlp, hlen, hleft, hfit, rfl, ⟨by omega, by omega⟩, hcb, Or.inr ⟨by omega, ?_⟩⟩
  rw [hr] at hc
  simpa only [max_eq_right (le_of_lt hb)] using max_scan_step (EnergySplitCandidate vals dp width left (left+len-1))
    left split best candidate hk.1 hc hcb.1 (EnergySplitCandidate_ext_eq__dp_interval_progress vals dp width left (left+len-1)) hscan

private theorem child_best (vals dp : List Int) (total width len left right k : Int)
    (hd : EnergyLenDone vals dp total width len) (hr : right = left+len-1) (hl : 0 ≤ left)
    (hk : left ≤ k ∧ k < right) (hrb : right+1 < Zlength vals) :
    EnergyIntervalBest vals left k (Znth (EnergyCellIndex width left k) dp 0) ∧
    EnergyIntervalBest vals (k+1) right (Znth (EnergyCellIndex width (k+1) right) dp 0) :=
  ⟨hd.2.2.2.2.2 (k-left+1) left k _ ⟨by omega, by omega⟩ (by omega) rfl hl (by omega),
   hd.2.2.2.2.2 (right-k) (k+1) right _ ⟨by omega, by omega⟩ (by omega) rfl (by omega) (by omega)⟩

theorem EnergySplitCandidate_plan__dp_interval_progress (vals dp : List Int)
    (total width len left right split candidate : Int) (hd : EnergyLenDone vals dp total width len)
    (hr : right = left+len-1) (hl : 0 ≤ left) (hk : left ≤ split ∧ split < right)
    (hrb : right+1 < Zlength vals) (hc : EnergySplitCandidate vals dp width left right split candidate) :
    EnergyIntervalPlan vals left right candidate := by
  have hb := child_best vals dp total width len left right split hd hr hl hk hrb
  rw [hc.2.2]
  exact EnergyIntervalPlan_merge left split right _ _ hl hk hrb
    ((maximum_iff _ _).mp hb.1).1 ((maximum_iff _ _).mp hb.2).1

theorem EnergySplitProgress_finish_interval_best__dp_interval_progress (vals dp : List Int)
    (total width len left right split best : Int) (hr : right = left+len-1) (hs : split ≥ right)
    (hrb : right+1 < Zlength vals) (hp : EnergySplitProgress vals dp total width len left split best) :
    EnergyIntervalBest vals left right best := by
  rcases hp with ⟨hlp, hlen, hleft, hfit, hre, hsplit, hbest, hscan⟩
  have he : split = right := by omega
  subst split
  have hm := hscan.resolve_left (by intro h; omega)
  rw [←hr] at hm
  have hm' := (maximum_iff _ best).mp hm.2
  apply (maximum_iff _ best).mpr
  constructor
  · obtain ⟨k, hk, hc⟩ := hm'.1
    exact EnergySplitCandidate_plan__dp_interval_progress vals dp total width len left right k best hlp.1 hr hleft hk hrb hc
  · intro cost hplan
    cases hplan with
    | EnergyIntervalPlan_single => omega
    | EnergyIntervalPlan_merge l k r lc rc hl hk hd hpl hpr =>
      have hch := child_best vals dp total width len left right k hlp.1 hr hleft hk hrb
      have hbl := ((maximum_iff _ _).mp hch.1).2 lc hpl
      have hbr := ((maximum_iff _ _).mp hch.2).2 rc hpr
      have hcan := hm'.2 _ ⟨k, hk, hk, hd, rfl⟩
      omega

theorem EnergyCellIndex_inj__dp_interval_progress (width l r l' r' : Int)
    (hw : 0 < width) (hr : 0 ≤ r ∧ r < width) (hr' : 0 ≤ r' ∧ r' < width)
    (he : EnergyCellIndex width l r = EnergyCellIndex width l' r') : l = l' ∧ r = r' := by
  unfold EnergyCellIndex at he
  have hl : l = l' := by
    rcases lt_trichotomy l l' with h | h | h
    · have hp := mul_le_mul_of_nonneg_right (show l+1 ≤ l' by omega) (show 0 ≤ width by omega); nlinarith
    · exact h
    · have hp := mul_le_mul_of_nonneg_right (show l'+1 ≤ l by omega) (show 0 ≤ width by omega); nlinarith
  exact ⟨hl, by rw [hl] at he; omega⟩

theorem EnergyLenDone_replace_current__dp_interval_progress (vals dp : List Int)
    (total width len left right best : Int) (hr : right = left+len-1) (hl : 0 ≤ left)
    (hfit : left < total-len) (hd : EnergyLenDone vals dp total width len) :
    EnergyLenDone vals (replace_Znth (EnergyCellIndex width left right) best dp) total width len := by
  have hw : 0 < width := by have := hd.2.1; have := hd.2.2.2.2.1; omega
  have hrr : 0 ≤ right ∧ right < width := by have := hd.2.1; have := hd.2.2.2.2.1; omega
  have hcur := index_bounds width left right hw ⟨hl, by have := hd.2.1; have := hd.2.2.2.2.1; omega⟩ hrr
  have hsize : Zlength dp = width*width := by rw [hd.2.2.2.1, hd.2.1]
  rw [←hsize] at hcur
  refine ⟨hd.1, hd.2.1, hd.2.2.1, by rw [Zlength_replace_Znth]; exact hd.2.2.2.1, hd.2.2.2.2.1, ?_⟩
  intro l i j idx hb hj hi h0 hf
  have hidx : 0 ≤ idx ∧ idx < Zlength dp := by
    rw [hi, hsize]
    exact index_bounds width i j hw ⟨h0, by have := hd.2.1; have := hd.2.2.1; omega⟩
      ⟨by omega, by have := hd.2.1; have := hd.2.2.1; omega⟩
  have hneq : EnergyCellIndex width left right ≠ idx := by
    intro he
    rw [hi] at he
    have hh := EnergyCellIndex_inj__dp_interval_progress width left right i j hw hrr
      ⟨by omega, by have := hd.2.1; have := hd.2.2.1; omega⟩ he
    omega
  rw [Znth_replace_Znth_Diff 0 dp _ idx best hcur hidx hneq]
  exact hd.2.2.2.2.2 l i j idx hb hj hi h0 hf

theorem EnergyLeftProgress_step_update__dp_interval_progress (vals dp : List Int)
    (total width len left right best : Int) (hr : right = left+len-1) (hl : 0 ≤ left)
    (hfit : left < total-len) (hp : EnergySplitProgress vals dp total width len left right best)
    (hm : EnergyIntervalBest vals left right best) :
    EnergyLeftProgress vals (replace_Znth (EnergyCellIndex width left right) best dp) total width len (left+1) := by
  have hd := hp.1.1
  have hw : 0 < width := by have := hd.2.1; have := hp.2.1; omega
  have hrr : 0 ≤ right ∧ right < width := by have := hd.2.1; have := hp.2.1; omega
  have hcur := index_bounds width left right hw ⟨hl, by have := hd.2.1; have := hp.2.1; omega⟩ hrr
  have hsize : Zlength dp = width*width := by rw [hd.2.2.2.1, hd.2.1]
  rw [←hsize] at hcur
  refine ⟨EnergyLenDone_replace_current__dp_interval_progress _ _ _ _ _ _ _ _ hr hl hfit hd,
    hp.2.1, by omega, ?_⟩
  intro i j idx hi hj hidx hf
  by_cases he : i = left
  · subst i
    have hej : j = right := by omega
    rw [hidx, hej, Znth_replace_Znth_Same 0 dp _ best hcur]
    exact hm
  · have hiold : 0 ≤ i ∧ i < left := ⟨hi.1, by omega⟩
    have hir : 0 ≤ i ∧ i < width := by have := hd.2.1; have := hp.2.1; omega
    have hjr : 0 ≤ j ∧ j < width := by have := hd.2.1; have := hd.2.2.1; have := hp.2.1; omega
    have hb : 0 ≤ idx ∧ idx < Zlength dp := by rw [hidx, hsize]; exact index_bounds width i j hw hir hjr
    have hn : EnergyCellIndex width left right ≠ idx := by
      intro hh
      rw [hidx] at hh
      have hx := EnergyCellIndex_inj__dp_interval_progress width left right i j hw hrr hjr hh
      omega
    rw [Znth_replace_Znth_Diff 0 dp _ idx best hcur hb hn]
    exact hp.1.2.2.2 i j idx hiold hj hidx hf

theorem EnergyLeftProgress_finish_len__dp_interval_progress (vals dp : List Int)
    (total width len left : Int) (hge : left ≥ total-len) (hle : left ≤ total-len)
    (hp : EnergyLeftProgress vals dp total width len left) : EnergyLenDone vals dp total width (len+1) := by
  have hd := hp.1
  refine ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1, by have := hp.2.1; omega, ?_⟩
  intro l i j idx hl hj hi h0 hf
  by_cases hlt : l < len
  · exact hd.2.2.2.2.2 l i j idx ⟨hl.1, hlt⟩ hj hi h0 hf
  · have he : l = len := by omega
    subst l
    exact hp.2.2.2 i j idx ⟨h0, by have := hd.2.2.1; omega⟩ hj hi hf

theorem EnergyAnswerProgress_answer_bounds__answer_loop (beads vals dp : List Int)
    (n total width start answer : Int) (hp : EnergyAnswerProgress beads vals dp n total width start answer) :
    0 ≤ answer ∧ answer ≤ 2100000000 := hp.2.2.2.2.1

theorem EnergyLenDone_to_answer_len__answer_loop (vals dp : List Int) (total width len n : Int)
    (hlo : len > n) (hhi : len ≤ n+1) (hp : EnergyLenDone vals dp total width len) :
    EnergyLenDone vals dp total width (n+1) := by
  convert hp using 1 <;> omega

theorem EnergyLenDone_rotation_cell_best__answer_loop (vals dp : List Int) (total width n start : Int)
    (hn : 4 ≤ n) (ht : total = 2*n) (hw : width = total) (hs : 0 ≤ start ∧ start < n)
    (hp : EnergyLenDone vals dp total width (n+1)) :
    EnergyIntervalBest vals start (start+n-1) (Znth (EnergyCellIndex width start (start+n-1)) dp 0) :=
  hp.2.2.2.2.2 n start (start+n-1) _ ⟨by omega, by omega⟩ rfl rfl hs.1 (by have := hp.2.2.1; omega)

theorem EnergyAnswerCellBounded__answer_loop (beads vals dp : List Int) (n total width start : Int)
    (hb : EnergyComputationBounded beads n 2100000000) (hd : EnergyValsDuplicated beads vals n)
    (ht : total = 2*n) (hw : width = total) (hs : 0 ≤ start ∧ start < n)
    (hz : Zlength dp = total*width) (hp : EnergyLenDone vals dp total width (n+1)) :
    0 ≤ Znth (EnergyCellIndex width start (start+n-1)) dp 0 ∧ Znth (EnergyCellIndex width start (start+n-1)) dp 0 ≤ 2100000000 :=
  hb.2.2.2 vals dp total width start hd ht hw hs hz hp

theorem EnergyIntervalBest_unique__answer_loop (vals : List Int) (left right a b : Int)
    (ha : EnergyIntervalBest vals left right a) (hb : EnergyIntervalBest vals left right b) : a = b := by
  have hma := (maximum_iff _ a).mp ha
  have hmb := (maximum_iff _ b).mp hb
  exact le_antisymm (hmb.2 a hma.1) (hma.2 b hmb.1)

theorem EnergyValsDuplicated_unique__answer_loop (beads vals1 vals2 : List Int) (n : Int)
    (h1 : EnergyValsDuplicated beads vals1 n) (h2 : EnergyValsDuplicated beads vals2 n) : vals1 = vals2 := by
  apply (ListLib.list_eq_ext vals1 vals2 0).mpr
  refine ⟨by change Zlength vals1 = Zlength vals2; have := h1.2.2.1; have := h2.2.2.1; omega, ?_⟩
  intro i hi
  change Znth i vals1 0 = Znth i vals2 0
  have hib : i < 2*n := by change 0 ≤ i ∧ i < Zlength vals1 at hi; rw [h1.2.2.1] at hi; exact hi.2
  by_cases hl : i < n
  · rw [h1.2.2.2.1 i ⟨hi.1, hl⟩, h2.2.2.2.1 i ⟨hi.1, hl⟩]
  · have he : i = n+(i-n) := by omega
    rw [he, h1.2.2.2.2 (i-n) ⟨by omega, by omega⟩, h2.2.2.2.2 (i-n) ⟨by omega, by omega⟩]

theorem EnergyAnswerProgress_step_keep__answer_loop (beads vals dp : List Int)
    (n total width start answer value : Int) (hp : EnergyAnswerProgress beads vals dp n total width start answer)
    (hs : 0 ≤ start ∧ start < n) (hv : EnergyIntervalBest vals start (start+n-1) value)
    (hv0 : 0 ≤ value) (hb : value ≤ answer) : EnergyAnswerProgress beads vals dp n total width (start+1) answer := by
  refine ⟨hp.1, hp.2.1, hp.2.2.1, ⟨by omega, by omega⟩, hp.2.2.2.2.1, Or.inr ⟨by omega, ?_⟩⟩
  simpa only [max_eq_left hb] using max_scan_step (fun k v => EnergyIntervalBest vals k (k+n-1) v)
    0 start answer value hs.1 hv hv0 (fun k a b => EnergyIntervalBest_unique__answer_loop vals k (k+n-1) a b) hp.2.2.2.2.2

theorem EnergyAnswerProgress_step_update__answer_loop (beads vals dp : List Int)
    (n total width start answer value : Int) (hp : EnergyAnswerProgress beads vals dp n total width start answer)
    (hs : 0 ≤ start ∧ start < n) (hv : EnergyIntervalBest vals start (start+n-1) value)
    (hvb : 0 ≤ value ∧ value ≤ 2100000000) (hb : answer < value) :
    EnergyAnswerProgress beads vals dp n total width (start+1) value := by
  refine ⟨hp.1, hp.2.1, hp.2.2.1, ⟨by omega, by omega⟩, hvb, Or.inr ⟨by omega, ?_⟩⟩
  simpa only [max_eq_right (le_of_lt hb)] using max_scan_step (fun k v => EnergyIntervalBest vals k (k+n-1) v)
    0 start answer value hs.1 hv hvb.1 (fun k a b => EnergyIntervalBest_unique__answer_loop vals k (k+n-1) a b) hp.2.2.2.2.2

theorem EnergyAnswerProgress_finish__answer_loop (beads vals dp : List Int)
    (n total width start answer : Int) (hn : 4 ≤ n) (hp : EnergyAnswerProgress beads vals dp n total width start answer)
    (hslo : start ≥ n) (hshi : start ≤ n) : EnergyNecklaceAnswer beads n answer := by
  have he : start = n := by omega
  subst start
  have hm := hp.2.2.2.2.2.resolve_left (by intro h; omega)
  have hb := (maximum_iff _ answer).mp hm.2
  apply (maximum_iff _ answer).mpr
  constructor
  · obtain ⟨s, hs, hbest⟩ := hb.1
    exact ⟨s, hs, vals, hp.1, hs, hbest⟩
  · rintro v ⟨s, hs, vals', hdup, hs', hbest⟩
    have he := EnergyValsDuplicated_unique__answer_loop beads vals' vals n hdup hp.1
    subst vals'
    exact hb.2 v ⟨s, hs, hbest⟩


set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open Algorithms.energy_necklace.lean.groundtruth.energy_necklace_goal
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

private theorem app_nth (l : List Int) (x i : Int) (hi : 0 ≤ i ∧ i < Zlength l) :
    Znth i (l++[x]) 0 = Znth i l 0 := ListLib.app_Znth1 0 l [x] i hi

theorem proof_of_energyNecklace_safety_wit_25 : energyNecklace_safety_wit_25 := by
  unfold energyNecklace_safety_wit_25
  right
  intro dp_pre vals_pre n_pre beads_pre beads_l vals_l dp_l total width len left right split best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  have hb := EnergySplitArithmeticBounded_from_progress__arithmetic_safety_bounds
    beads_l vals_l dp_l n_pre total width len left right split best 2100000000
    PreH32 PreH29 PreH1 PreH2 ⟨PreH7, PreH8⟩ ⟨PreH9, PreH10⟩ PreH11 ⟨PreH12, PreH13⟩ PreH28 PreH30
  have h := hb.2.2.1
  try dsimp [EnergyCellIndex] at h
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> omega

theorem proof_of_energyNecklace_safety_wit_27 : energyNecklace_safety_wit_27 := by
  unfold energyNecklace_safety_wit_27
  right
  intro dp_pre vals_pre n_pre beads_pre beads_l vals_l dp_l total width len left right split best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  have hl := EnergyValsDuplicated_label_bound__arithmetic_safety_bounds _ _ _ left PreH29 PreH31 ⟨by omega, by omega⟩
  have hk := EnergyValsDuplicated_label_bound__arithmetic_safety_bounds _ _ _ (split+1) PreH29 PreH31 ⟨by omega, by omega⟩
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> nlinarith

theorem proof_of_energyNecklace_safety_wit_31 : energyNecklace_safety_wit_31 := by
  unfold energyNecklace_safety_wit_31
  right
  intro dp_pre vals_pre n_pre beads_pre beads_l vals_l dp_l total width len left right split best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  have hb := EnergySplitArithmeticBounded_from_progress__arithmetic_safety_bounds
    beads_l vals_l dp_l n_pre total width len left right split best 2100000000
    PreH32 PreH29 PreH1 PreH2 ⟨PreH7, PreH8⟩ ⟨PreH9, PreH10⟩ PreH11 ⟨PreH12, PreH13⟩ PreH28 PreH30
  have h := hb.2.2.2.2
  try dsimp [EnergyCellIndex] at h
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> omega

theorem proof_of_energyNecklace_safety_wit_32 : energyNecklace_safety_wit_32 := by
  unfold energyNecklace_safety_wit_32
  right
  intro dp_pre vals_pre n_pre beads_pre beads_l vals_l dp_l total width len left right split best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  have hb := EnergySplitArithmeticBounded_from_progress__arithmetic_safety_bounds
    beads_l vals_l dp_l n_pre total width len left right split best 2100000000
    PreH32 PreH29 PreH1 PreH2 ⟨PreH7, PreH8⟩ ⟨PreH9, PreH10⟩ PreH11 ⟨PreH12, PreH13⟩ PreH28 PreH30
  have h := hb.2.2.2.1
  try dsimp [EnergyCellIndex] at h
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> omega

theorem proof_of_energyNecklace_entail_wit_2 : energyNecklace_entail_wit_2 := by
  unfold energyNecklace_entail_wit_2
  right
  intro n_pre beads_l total width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | rfl | intro k hk; omega

theorem proof_of_energyNecklace_entail_wit_3 : energyNecklace_entail_wit_3 := by
  unfold energyNecklace_entail_wit_3
  right
  intro n_pre beads_l i vals_l_2 width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    rw [Zlength_app, Zlength_cons, Zlength_nil, PreH9]
    omega

theorem proof_of_energyNecklace_entail_wit_4 : energyNecklace_entail_wit_4 := by
  unfold energyNecklace_entail_wit_4
  right
  intro vals_pre n_pre beads_l i vals_l_2 width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have he : i = n_pre := by omega
  simp only [he] at *
  refine Automation.exp_right_rule (CRules := naive_C_Rules) vals_l_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption

theorem proof_of_energyNecklace_entail_wit_5 : energyNecklace_entail_wit_5 := by
  unfold energyNecklace_entail_wit_5
  right
  intro vals_pre n_pre beads_l vals_l_2 total width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  refine Automation.exp_right_rule (CRules := naive_C_Rules) vals_l_2 ?_
  simp only [Int.add_zero]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | intro k hk; omega

theorem proof_of_energyNecklace_entail_wit_6 : energyNecklace_entail_wit_6 := by
  unfold energyNecklace_entail_wit_6
  right
  intro vals_pre n_pre beads_l i vals_l_2 width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hlen : Zlength (vals_l_2 ++ [Znth i beads_l 0]) = n_pre+(i+1) := by
    rw [Zlength_app, Zlength_cons, Zlength_nil, PreH9]; omega
  have hfirst : ∀ k, (0 ≤ k ∧ k < n_pre) → Znth k (vals_l_2++[Znth i beads_l 0]) 0 = Znth k beads_l 0 := by
    intro k hk
    rw [app_nth _ _ k (by rw [PreH9]; omega)]
    exact PreH12 k hk
  have hsecond : ∀ k, (0 ≤ k ∧ k < i+1) → Znth (n_pre+k) (vals_l_2++[Znth i beads_l 0]) 0 = Znth k beads_l 0 := by
    intro k hk
    by_cases he : k = i
    · subst k
      rw [app_Znth2 0 vals_l_2 _ (n_pre+i) (by rw [PreH9]), PreH9, Int.sub_self]
      rfl
    · rw [app_nth _ _ (n_pre+k) (by rw [PreH9]; omega)]
      exact PreH13 k ⟨hk.1, by omega⟩
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (vals_l_2++[Znth i beads_l 0]) ?_
  rw [show n_pre+(i+1) = (n_pre+i)+1 by omega]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_energyNecklace_entail_wit_7 : energyNecklace_entail_wit_7 := by
  unfold energyNecklace_entail_wit_7
  right
  intro vals_pre n_pre beads_l i vals_l_2 width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have he : i = n_pre := by omega
  have hend : n_pre+i = total := by omega
  have hdup : EnergyValsDuplicated beads_l vals_l_2 n_pre :=
    ⟨by omega, PreH8, by omega, PreH12, fun k hk => PreH13 k ⟨hk.1, by omega⟩⟩
  rw [hend]
  refine Automation.exp_right_rule (CRules := naive_C_Rules) vals_l_2 ?_
  split_pure_spatial
  · simpa only [Int.zero_mul, Int.add_zero, Int.sub_zero] using intArray.seg_to_full vals_pre 0 total vals_l_2
  · split_pures <;> dump_pre_spatial
    all_goals assumption

theorem proof_of_energyNecklace_entail_wit_8 : energyNecklace_entail_wit_8 := by
  unfold energyNecklace_entail_wit_8
  right
  intro n_pre beads_l vals_l_2 total width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | rfl | intro k hk; omega

theorem proof_of_energyNecklace_entail_wit_9 : energyNecklace_entail_wit_9 := by
  unfold energyNecklace_entail_wit_9
  right
  intro n_pre beads_l vals_l_2 i dp_l_2 width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    rw [Zlength_app, Zlength_cons, Zlength_nil, PreH9]
    omega

theorem proof_of_energyNecklace_entail_wit_10 : energyNecklace_entail_wit_10 := by
  unfold energyNecklace_entail_wit_10
  right
  intro dp_pre n_pre beads_l vals_l_2 i dp_l_2 width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have he : i = total*width := by omega
  have hz := EnergyZeroTable_from_prefix__prefix_table_bootstrap dp_l_2 total width i (by omega) PreH3 PreH1 PreH11 PreH9 PreH12
  have hd := EnergyZeroTable_len_done_2__prefix_table_bootstrap vals_l_2 dp_l_2 total width
    (by have := PreH13.2.2.1; omega) hz
  rw [he]
  refine Automation.exp_right_rule (CRules := naive_C_Rules) dp_l_2 ?_
  split_pure_spatial
  · simpa only [Int.zero_mul, Int.add_zero, Int.sub_zero] using intArray.seg_to_full dp_pre 0 (total*width) dp_l_2
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_energyNecklace_entail_wit_12 : energyNecklace_entail_wit_12 := by
  unfold energyNecklace_entail_wit_12
  right
  intro n_pre beads_l vals_l_2 dp_l_2 len width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    rw [←PreH2]
    exact ⟨PreH13, PreH8, by omega, fun l r idx hl _ _ _ => False.elim (by omega)⟩

theorem proof_of_energyNecklace_entail_wit_13 : energyNecklace_entail_wit_13 := by
  unfold energyNecklace_entail_wit_13
  right
  intro n_pre beads_l vals_l_2 dp_l_2 left len width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    rw [←PreH2]
    exact ⟨PreH15, PreH8, PreH10, by omega, rfl, ⟨by omega, by omega⟩,
      ⟨by omega, by omega⟩, Or.inl ⟨rfl, rfl⟩⟩

theorem proof_of_energyNecklace_entail_wit_14 : energyNecklace_entail_wit_14 := by
  unfold energyNecklace_entail_wit_14
  right
  intro n_pre beads_l vals_l_2 dp_l_2 total width len left right best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have hb := PreH19.2.2.2.2.2.2.1
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals omega

theorem proof_of_energyNecklace_entail_wit_15 : energyNecklace_entail_wit_15 := by
  unfold energyNecklace_entail_wit_15
  right
  intro n_pre beads_l vals_l_2 dp_l_2 best split right left len width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals rw [←PreH2]
    all_goals nlinarith

theorem proof_of_energyNecklace_entail_wit_16 : energyNecklace_entail_wit_16 := by
  unfold energyNecklace_entail_wit_16
  right
  intro n_pre beads_l vals_l dp_l total width len left right split best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  have hb := EnergySplitArithmeticBounded_from_progress__arithmetic_safety_bounds
    beads_l vals_l dp_l n_pre total width len left right split best 2100000000
    PreH32 PreH29 PreH1 PreH2 ⟨PreH7, PreH8⟩ ⟨PreH9, PreH10⟩ PreH11 ⟨PreH12, PreH13⟩ PreH28 PreH30
  have hc := hb.2.2.2.2
  dsimp [EnergyCellIndex] at hc
  rw [PreH2, PreH11] at hc
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals omega

theorem proof_of_energyNecklace_entail_wit_17_2 : energyNecklace_entail_wit_17_2 := by
  unfold energyNecklace_entail_wit_17_2
  right
  intro n_pre beads_l vals_l_2 dp_l_2 total width len left right split left_value right_value gain candidate best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  have hv := PreH27.1.1.2.2.1
  have hc : EnergySplitCandidate vals_l_2 dp_l_2 width left right split candidate :=
    ⟨⟨PreH13, PreH14⟩, by omega, by dsimp [EnergyCellIndex]; omega⟩
  have hp := EnergySplitProgress_step_keep__dp_interval_progress _ _ _ _ _ _ _ _ _ _
    PreH12 ⟨PreH13, PreH14⟩ PreH27 hc PreH22 PreH1
  have hb := PreH27.2.2.2.2.2.2.1
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | omega
      | simpa only [PreH3, PreH2, PreH21] using hp

theorem proof_of_energyNecklace_entail_wit_17_1 : energyNecklace_entail_wit_17_1 := by
  unfold energyNecklace_entail_wit_17_1
  right
  intro n_pre beads_l vals_l_2 dp_l_2 total width len left right split left_value right_value gain candidate best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  have hv := PreH27.1.1.2.2.1
  have hc : EnergySplitCandidate vals_l_2 dp_l_2 width left right split candidate :=
    ⟨⟨PreH13, PreH14⟩, by omega, by dsimp [EnergyCellIndex]; omega⟩
  have hp := EnergySplitProgress_step_take__dp_interval_progress _ _ _ _ _ _ _ _ _ _
    PreH12 ⟨PreH13, PreH14⟩ PreH27 hc ⟨PreH22, PreH23⟩ PreH1
  have hb := PreH27.2.2.2.2.2.2.1
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | omega
      | simpa only [PreH3, PreH2, PreH21] using hp

theorem proof_of_energyNecklace_entail_wit_19 : energyNecklace_entail_wit_19 := by
  unfold energyNecklace_entail_wit_19
  right
  intro n_pre beads_l vals_l_2 dp_l_2 best split right left len width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have hv := PreH24.1.1.2.2.1
  have hm := EnergySplitProgress_finish_interval_best__dp_interval_progress _ _ _ _ _ _ _ _ _
    PreH12 PreH1 (by omega) PreH24
  have he : split = right := by omega
  rw [he] at PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | simpa only [PreH12] using hm
      | simpa only [PreH2, PreH12] using PreH24
      | rw [←PreH2]; nlinarith

theorem proof_of_energyNecklace_entail_wit_20 : energyNecklace_entail_wit_20 := by
  unfold energyNecklace_entail_wit_20
  right
  intro n_pre beads_l vals_l_2 dp_l total width len left right best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have hup : EnergyUpdatedCell vals_l_2 dp_l (replace_Znth (EnergyCellIndex width left right) best dp_l) width left right best :=
    ⟨⟨PreH13, by change left*width+right < Zlength dp_l; rw [PreH18]; exact PreH14⟩, rfl, PreH21⟩
  have hp := EnergyLeftProgress_step_update__dp_interval_progress _ _ _ _ _ _ _ _
    PreH11 PreH9 PreH10 PreH20 PreH21
  refine Automation.exp_right_rule (CRules := naive_C_Rules) dp_l ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | simpa only [EnergyCellIndex, PreH2, PreH1, PreH11, PreH17] using hup
      | simpa only [EnergyCellIndex, PreH2, PreH1, PreH11, PreH17] using hp
      | simpa only [PreH17, PreH18, PreH1, PreH2, Zlength_replace_Znth]

theorem proof_of_energyNecklace_entail_wit_22 : energyNecklace_entail_wit_22 := by
  unfold energyNecklace_entail_wit_22
  right
  intro n_pre beads_l vals_l_2 dp_l_2 left len width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hp := EnergyLeftProgress_finish_len__dp_interval_progress _ _ _ _ _ _ PreH1 PreH11 PreH15
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    simpa only [PreH2] using hp

theorem proof_of_energyNecklace_entail_wit_24 : energyNecklace_entail_wit_24 := by
  unfold energyNecklace_entail_wit_24
  right
  intro n_pre beads_l vals_l_2 dp_l_2 len width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hl := EnergyLenDone_to_answer_len__answer_loop _ _ _ _ _ _ PreH1 PreH9 PreH13
  have hp : EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width 0 0 :=
    ⟨PreH12, PreH11, PreH3, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, Or.inl ⟨rfl, rfl⟩⟩
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | simpa only [PreH2] using hp | simpa only [PreH2] using hl

theorem proof_of_energyNecklace_entail_wit_25 : energyNecklace_entail_wit_25 := by
  unfold energyNecklace_entail_wit_25
  right
  intro n_pre beads_l vals_l_2 dp_l_2 total width answer PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hb := EnergyAnswerProgress_answer_bounds__answer_loop _ _ _ _ _ _ _ _ PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals omega

theorem proof_of_energyNecklace_entail_wit_26_split_goal_1 : energyNecklace_entail_wit_26_split_goal_1 := by
  unfold energyNecklace_entail_wit_26_split_goal_1
  intro n_pre beads_l vals_l_2 dp_l_2 answer start width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hb := EnergyLenDone_rotation_cell_best__answer_loop _ _ _ _ _ _ PreH4 PreH2 PreH3 ⟨PreH8, PreH1⟩ PreH15
  convert hb using 1 <;> dsimp [EnergyCellIndex] <;> congr 1 <;> omega

theorem proof_of_energyNecklace_entail_wit_26_split_goal_2 : energyNecklace_entail_wit_26_split_goal_2 := by
  unfold energyNecklace_entail_wit_26_split_goal_2
  intro n_pre beads_l vals_l_2 dp_l_2 answer start width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  rw [←PreH2]
  nlinarith

theorem proof_of_energyNecklace_entail_wit_26 : energyNecklace_entail_wit_26 := by
  unfold energyNecklace_entail_wit_26
  right
  intro n_pre beads_l vals_l_2 dp_l_2 answer start width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_energyNecklace_entail_wit_26_split_goal_1 n_pre beads_l vals_l_2 dp_l_2 answer start width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
      | exact proof_of_energyNecklace_entail_wit_26_split_goal_2 n_pre beads_l vals_l_2 dp_l_2 answer start width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18

theorem proof_of_energyNecklace_entail_wit_27 : energyNecklace_entail_wit_27 := by
  unfold energyNecklace_entail_wit_27
  right
  intro n_pre beads_l vals_l_2 dp_l total width start answer PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hb := EnergyAnswerCellBounded__answer_loop _ _ _ _ _ _ _ PreH18 PreH13 PreH1 PreH2 ⟨PreH7, PreH8⟩ PreH12 PreH14
  dsimp [EnergyCellIndex] at hb
  rw [PreH2] at hb
  have he : start*total+(start+n_pre-1) = start*total+start+n_pre-1 := by omega
  rw [he] at hb
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals omega

theorem proof_of_energyNecklace_entail_wit_28_2 : energyNecklace_entail_wit_28_2 := by
  unfold energyNecklace_entail_wit_28_2
  right
  intro n_pre beads_l vals_l_2 dp_l_2 total width start value answer PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have hp := EnergyAnswerProgress_step_keep__answer_loop _ _ _ _ _ _ _ _ _
    PreH17 ⟨PreH8, PreH9⟩ PreH18 PreH11 PreH1
  have hb := EnergyAnswerProgress_answer_bounds__answer_loop _ _ _ _ _ _ _ _ PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | simpa only [PreH3, PreH2] using hp | omega

theorem proof_of_energyNecklace_entail_wit_28_1 : energyNecklace_entail_wit_28_1 := by
  unfold energyNecklace_entail_wit_28_1
  right
  intro n_pre beads_l vals_l_2 dp_l_2 total width start value answer PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have hp := EnergyAnswerProgress_step_update__answer_loop _ _ _ _ _ _ _ _ _
    PreH17 ⟨PreH8, PreH9⟩ PreH18 ⟨PreH11, PreH12⟩ PreH1
  have hb := EnergyAnswerProgress_answer_bounds__answer_loop _ _ _ _ _ _ _ _ PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | simpa only [PreH3, PreH2] using hp | omega

theorem proof_of_energyNecklace_entail_wit_30 : energyNecklace_entail_wit_30 := by
  unfold energyNecklace_entail_wit_30
  right
  intro n_pre beads_l vals_l_2 dp_l_2 answer start width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    exact EnergyAnswerProgress_finish__answer_loop _ _ _ _ _ _ _ _ PreH4 PreH16 PreH1 PreH9

theorem proof_of_energyNecklace_return_wit_1 : energyNecklace_return_wit_1 := by
  unfold energyNecklace_return_wit_1
  right
  intro dp_pre vals_pre n_pre beads_l vals_l_2 dp_l_2 total width answer PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hp : EnergyLenDone vals_l_2 dp_l_2 (2*n_pre) (2*n_pre) (n_pre+1) := by
    simpa only [PreH2, PreH1] using PreH12
  rw [PreH2, PreH1]
  refine Automation.exp_right_rule (CRules := naive_C_Rules) dp_l_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) vals_l_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption

end Algorithms.energy_necklace.lean.groundtruth.energy_necklace_proof_manual
