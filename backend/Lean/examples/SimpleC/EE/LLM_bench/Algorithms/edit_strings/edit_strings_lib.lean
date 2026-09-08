import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import ListLib.General.Length
import Init.Data.List.Nat.Range

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.edit_strings.edit_strings_lib
open AUXLib

def edit_zrange (n : Int) : List Int := (List.range n.toNat).map Int.ofNat

def edit_zrange_between (lo hi : Int) : List Int :=
  (List.range (hi-lo).toNat).map (fun off => lo+Int.ofNat off)

def EditBinaryList (xs : List Int) (n : Int) : Prop :=
  Zlength xs=n ∧ ∀ idx, (0 ≤ idx ∧ idx<n) → Znth idx xs 0=0 ∨ Znth idx xs 0=1

def edit_edge_open (t : List Int) (idx : Int) : Prop :=
  Znth (idx-1) t 0=1 ∧ Znth idx t 0=1

def edit_edge_openb (t : List Int) (idx : Int) : Bool :=
  decide (Znth (idx-1) t 0=1) && decide (Znth idx t 0=1)

def edit_all_edges_openb (t : List Int) (lo hi : Int) : Bool :=
  (edit_zrange_between lo hi).all (edit_edge_openb t)

def EditBlockStart (t : List Int) (idx start : Int) : Prop :=
  (0 ≤ start ∧ start ≤ idx) ∧ (∀ k, (start<k ∧ k≤idx) → edit_edge_open t k) ∧
    (start=0 ∨ ¬edit_edge_open t start)

def edit_block_startb (t : List Int) (idx start : Int) : Bool :=
  decide (0 ≤ start) && decide (start ≤ idx) && edit_all_edges_openb t (start+1) (idx+1) &&
    (decide (start=0) || !(edit_edge_openb t start))

def edit_bit_atb (xs : List Int) (idx bit : Int) : Bool := decide (Znth idx xs 0=bit)

def edit_count_bit_in_block_prefix (s t : List Int) (limit block bit : Int) : Int :=
  Int.ofNat ((edit_zrange (Zlength s)).filter (fun idx =>
    decide (idx<limit) && edit_block_startb t idx block && edit_bit_atb s idx bit)).length

def EditZeroPrefix (xs : List Int) (written : Int) : Prop :=
  Zlength xs=written ∧ ∀ idx, (0 ≤ idx ∧ idx<written) → Znth idx xs 0=0

def EditZeroFull (n : Int) (xs : List Int) : Prop :=
  Zlength xs=n ∧ ∀ idx, (0 ≤ idx ∧ idx<n) → Znth idx xs 0=0

def EditSegmentPrefix (t : List Int) (upto : Int) (seg : List Int) : Prop :=
  Zlength seg=upto ∧ ∀ idx, (0 ≤ idx ∧ idx<upto) → EditBlockStart t idx (Znth idx seg 0)

def EditCountsForPrefix (s t : List Int) (n upto : Int) (cnt0 cnt1 : List Int) : Prop :=
  Zlength cnt0=n ∧ Zlength cnt1=n ∧
  (∀ block, (0 ≤ block ∧ block<n) → Znth block cnt0 0=edit_count_bit_in_block_prefix s t upto block 0) ∧
  ∀ block, (0 ≤ block ∧ block<n) → Znth block cnt1 0=edit_count_bit_in_block_prefix s t upto block 1

def EditBuildState (s t : List Int) (n upto : Int) (seg cnt0 cnt1 : List Int) : Prop :=
  (0 ≤ upto ∧ upto ≤ n) ∧ EditBinaryList s n ∧ EditBinaryList t n ∧
    EditSegmentPrefix t upto seg ∧ EditCountsForPrefix s t n upto cnt0 cnt1

def EditCountBounds (n : Int) (cnt : List Int) : Prop :=
  Zlength cnt=n ∧ ∀ idx, (0 ≤ idx ∧ idx<n) → 0 ≤ Znth idx cnt 0 ∧ Znth idx cnt 0 ≤ n

def EditScratchCountsBound (n : Int) (cnt10 cnt11 cnt20 cnt21 : List Int) : Prop :=
  EditCountBounds n cnt10 ∧ EditCountBounds n cnt11 ∧ EditCountBounds n cnt20 ∧ EditCountBounds n cnt21

def edit_count_positions_in_seg_prefix (seg : List Int) (limit block : Int) : Int :=
  Int.ofNat ((edit_zrange (Zlength seg)).filter (fun idx => decide (idx<limit) && decide (Znth idx seg 0=block))).length

def EditGreedyRemainingTotals (seg1 seg2 : List Int) (i : Int)
    (full10 full11 full20 full21 cnt10 cnt11 cnt20 cnt21 : List Int) : Prop :=
  (∀ block, (0 ≤ block ∧ block<Zlength seg1) →
    Znth block cnt10 0+Znth block cnt11 0=Znth block full10 0+Znth block full11 0-edit_count_positions_in_seg_prefix seg1 i block) ∧
  ∀ block, (0 ≤ block ∧ block<Zlength seg2) →
    Znth block cnt20 0+Znth block cnt21 0=Znth block full20 0+Znth block full21 0-edit_count_positions_in_seg_prefix seg2 i block

def EditReachableString (s t out : List Int) (n : Int) : Prop :=
  EditBinaryList s n ∧ EditBinaryList t n ∧ EditBinaryList out n ∧
  ∀ block bit, (0 ≤ block ∧ block<n) → (bit=0 ∨ bit=1) →
    edit_count_bit_in_block_prefix out t n block bit=edit_count_bit_in_block_prefix s t n block bit

def edit_match_count (s1 s2 : List Int) (n : Int) : Int :=
  Int.ofNat ((edit_zrange n).filter (fun idx => decide (Znth idx s1 0=Znth idx s2 0))).length

def EditStringsFeasibleMatchCount (s1 s2 t1 t2 : List Int) (n answer : Int) : Prop :=
  ∃ out1 out2, EditReachableString s1 t1 out1 n ∧ EditReachableString s2 t2 out2 n ∧ answer=edit_match_count out1 out2 n

def EditStringsMatchUpperBound (s1 s2 t1 t2 : List Int) (n answer : Int) : Prop :=
  ∀ cand1 cand2 cand, EditReachableString s1 t1 cand1 n → EditReachableString s2 t2 cand2 n →
    cand=edit_match_count cand1 cand2 n → cand≤answer

def EditStringsMaximum (s1 s2 t1 t2 : List Int) (n answer : Int) : Prop :=
  EditBinaryList s1 n ∧ EditBinaryList s2 n ∧ EditBinaryList t1 n ∧ EditBinaryList t2 n ∧
    EditStringsFeasibleMatchCount s1 s2 t1 t2 n answer ∧ EditStringsMatchUpperBound s1 s2 t1 t2 n answer

inductive EditGreedyConsumedPrefix (seg1 seg2 full10 full11 full20 full21 : List Int) :
    Int → Int → List Int → List Int → List Int → List Int → Prop where
  | EditGreedyConsumedPrefix_start : EditGreedyConsumedPrefix seg1 seg2 full10 full11 full20 full21
      0 0 full10 full11 full20 full21
  | EditGreedyConsumedPrefix_common_zero (i ans : Int) (cnt10 cnt11 cnt20 cnt21 : List Int) (a b : Int) :
      (0 ≤ i ∧ i<Zlength seg1) → Zlength seg2=Zlength seg1 → a=Znth i seg1 0 → b=Znth i seg2 0 →
      0<Znth a cnt10 0 → 0<Znth b cnt20 0 →
      EditGreedyConsumedPrefix seg1 seg2 full10 full11 full20 full21 i ans cnt10 cnt11 cnt20 cnt21 →
      EditGreedyConsumedPrefix seg1 seg2 full10 full11 full20 full21 (i+1) (ans+1)
        (replace_Znth a (Znth a cnt10 0-1) cnt10) cnt11 (replace_Znth b (Znth b cnt20 0-1) cnt20) cnt21
  | EditGreedyConsumedPrefix_common_one (i ans : Int) (cnt10 cnt11 cnt20 cnt21 : List Int) (a b : Int) :
      (0 ≤ i ∧ i<Zlength seg1) → Zlength seg2=Zlength seg1 → a=Znth i seg1 0 → b=Znth i seg2 0 →
      ¬(0<Znth a cnt10 0 ∧ 0<Znth b cnt20 0) → 0<Znth a cnt11 0 → 0<Znth b cnt21 0 →
      EditGreedyConsumedPrefix seg1 seg2 full10 full11 full20 full21 i ans cnt10 cnt11 cnt20 cnt21 →
      EditGreedyConsumedPrefix seg1 seg2 full10 full11 full20 full21 (i+1) (ans+1)
        cnt10 (replace_Znth a (Znth a cnt11 0-1) cnt11) cnt20 (replace_Znth b (Znth b cnt21 0-1) cnt21)
  | EditGreedyConsumedPrefix_s1_zero_s2_one (i ans : Int) (cnt10 cnt11 cnt20 cnt21 : List Int) (a b : Int) :
      (0 ≤ i ∧ i<Zlength seg1) → Zlength seg2=Zlength seg1 → a=Znth i seg1 0 → b=Znth i seg2 0 →
      ¬(0<Znth a cnt10 0 ∧ 0<Znth b cnt20 0) → ¬(0<Znth a cnt11 0 ∧ 0<Znth b cnt21 0) →
      0<Znth a cnt10 0 → 0<Znth b cnt21 0 →
      EditGreedyConsumedPrefix seg1 seg2 full10 full11 full20 full21 i ans cnt10 cnt11 cnt20 cnt21 →
      EditGreedyConsumedPrefix seg1 seg2 full10 full11 full20 full21 (i+1) ans
        (replace_Znth a (Znth a cnt10 0-1) cnt10) cnt11 cnt20 (replace_Znth b (Znth b cnt21 0-1) cnt21)
  | EditGreedyConsumedPrefix_s1_one_s2_zero (i ans : Int) (cnt10 cnt11 cnt20 cnt21 : List Int) (a b : Int) :
      (0 ≤ i ∧ i<Zlength seg1) → Zlength seg2=Zlength seg1 → a=Znth i seg1 0 → b=Znth i seg2 0 →
      ¬(0<Znth a cnt10 0 ∧ 0<Znth b cnt20 0) → ¬(0<Znth a cnt11 0 ∧ 0<Znth b cnt21 0) →
      ¬(0<Znth a cnt10 0) → 0<Znth a cnt11 0 → 0<Znth b cnt20 0 →
      EditGreedyConsumedPrefix seg1 seg2 full10 full11 full20 full21 i ans cnt10 cnt11 cnt20 cnt21 →
      EditGreedyConsumedPrefix seg1 seg2 full10 full11 full20 full21 (i+1) ans
        cnt10 (replace_Znth a (Znth a cnt11 0-1) cnt11) (replace_Znth b (Znth b cnt20 0-1) cnt20) cnt21

@[match_pattern] abbrev EditGreedyConsumedPrefix_start (seg1 seg2 full10 full11 full20 full21 : List Int) :=
  @EditGreedyConsumedPrefix.EditGreedyConsumedPrefix_start seg1 seg2 full10 full11 full20 full21
@[match_pattern] abbrev EditGreedyConsumedPrefix_common_zero (seg1 seg2 full10 full11 full20 full21 : List Int) :=
  @EditGreedyConsumedPrefix.EditGreedyConsumedPrefix_common_zero seg1 seg2 full10 full11 full20 full21
@[match_pattern] abbrev EditGreedyConsumedPrefix_common_one (seg1 seg2 full10 full11 full20 full21 : List Int) :=
  @EditGreedyConsumedPrefix.EditGreedyConsumedPrefix_common_one seg1 seg2 full10 full11 full20 full21
@[match_pattern] abbrev EditGreedyConsumedPrefix_s1_zero_s2_one (seg1 seg2 full10 full11 full20 full21 : List Int) :=
  @EditGreedyConsumedPrefix.EditGreedyConsumedPrefix_s1_zero_s2_one seg1 seg2 full10 full11 full20 full21
@[match_pattern] abbrev EditGreedyConsumedPrefix_s1_one_s2_zero (seg1 seg2 full10 full11 full20 full21 : List Int) :=
  @EditGreedyConsumedPrefix.EditGreedyConsumedPrefix_s1_one_s2_zero seg1 seg2 full10 full11 full20 full21

def EditGreedyFinalOptimality (s1 s2 t1 t2 : List Int) (n answer : Int) : Prop :=
  EditStringsFeasibleMatchCount s1 s2 t1 t2 n answer ∧ EditStringsMatchUpperBound s1 s2 t1 t2 n answer

def EditGreedyPrefixState (s1 s2 t1 t2 : List Int) (n i answer : Int) (seg1 seg2 cnt10 cnt11 cnt20 cnt21 : List Int) : Prop :=
  (0 ≤ i ∧ i≤n) ∧ (0 ≤ answer ∧ answer≤i) ∧ ∃ full10 full11 full20 full21,
    EditBuildState s1 t1 n n seg1 full10 full11 ∧ EditBuildState s2 t2 n n seg2 full20 full21 ∧
    EditScratchCountsBound n cnt10 cnt11 cnt20 cnt21 ∧
    EditGreedyRemainingTotals seg1 seg2 i full10 full11 full20 full21 cnt10 cnt11 cnt20 cnt21 ∧
    EditGreedyConsumedPrefix seg1 seg2 full10 full11 full20 full21 i answer cnt10 cnt11 cnt20 cnt21

def EditGreedyCurrentAvailability (n i : Int) (seg1 seg2 cnt10 cnt11 cnt20 cnt21 : List Int) : Prop :=
  (0 ≤ i ∧ i<n) → (0 ≤ Znth i seg1 0 ∧ Znth i seg1 0<n) ∧ (0 ≤ Znth i seg2 0 ∧ Znth i seg2 0<n) ∧
    0<Znth (Znth i seg1 0) cnt10 0+Znth (Znth i seg1 0) cnt11 0 ∧
    0<Znth (Znth i seg2 0) cnt20 0+Znth (Znth i seg2 0) cnt21 0

def EditGreedyCompletedMaximumFacts (s1 s2 t1 t2 : List Int) (n : Int) : Prop :=
  ∀ answer seg1 seg2 cnt10 cnt11 cnt20 cnt21, EditGreedyPrefixState s1 s2 t1 t2 n n answer seg1 seg2 cnt10 cnt11 cnt20 cnt21 →
    EditGreedyFinalOptimality s1 s2 t1 t2 n answer

def EditGreedyCompletedStateFacts (s1 s2 t1 t2 : List Int) (n answer : Int) (seg1 seg2 cnt10 cnt11 cnt20 cnt21 : List Int) : Prop :=
  EditGreedyPrefixState s1 s2 t1 t2 n n answer seg1 seg2 cnt10 cnt11 cnt20 cnt21 ∧ EditGreedyFinalOptimality s1 s2 t1 t2 n answer

theorem EditStringsMaximum_intro (s1 s2 t1 t2 : List Int) (n answer : Int)
    (hs1 : EditBinaryList s1 n) (hs2 : EditBinaryList s2 n) (ht1 : EditBinaryList t1 n) (ht2 : EditBinaryList t2 n)
    (hf : EditStringsFeasibleMatchCount s1 s2 t1 t2 n answer) (hu : EditStringsMatchUpperBound s1 s2 t1 t2 n answer) :
    EditStringsMaximum s1 s2 t1 t2 n answer := ⟨hs1, hs2, ht1, ht2, hf, hu⟩

theorem EditStringsMaximum_feasible (s1 s2 t1 t2 : List Int) (n answer : Int)
    (h : EditStringsMaximum s1 s2 t1 t2 n answer) : EditStringsFeasibleMatchCount s1 s2 t1 t2 n answer := h.2.2.2.2.1

theorem EditStringsMaximum_upper_bound (s1 s2 t1 t2 : List Int) (n answer : Int)
    (h : EditStringsMaximum s1 s2 t1 t2 n answer) : EditStringsMatchUpperBound s1 s2 t1 t2 n answer := h.2.2.2.2.2

theorem EditGreedyPrefixState_final_optimality (s1 s2 t1 t2 : List Int) (n answer : Int)
    (seg1 seg2 cnt10 cnt11 cnt20 cnt21 : List Int) (hf : EditGreedyCompletedMaximumFacts s1 s2 t1 t2 n)
    (hs : EditGreedyPrefixState s1 s2 t1 t2 n n answer seg1 seg2 cnt10 cnt11 cnt20 cnt21) :
    EditGreedyFinalOptimality s1 s2 t1 t2 n answer := hf answer seg1 seg2 cnt10 cnt11 cnt20 cnt21 hs

theorem EditGreedyPrefixState_completed_maximum (s1 s2 t1 t2 : List Int) (n answer : Int)
    (seg1 seg2 cnt10 cnt11 cnt20 cnt21 : List Int)
    (hs : EditGreedyPrefixState s1 s2 t1 t2 n n answer seg1 seg2 cnt10 cnt11 cnt20 cnt21)
    (hf : EditGreedyCompletedMaximumFacts s1 s2 t1 t2 n) : EditGreedyCompletedMaximumFacts s1 s2 t1 t2 n := hf

theorem EditGreedyPrefixState_completed_state_facts (s1 s2 t1 t2 : List Int) (n answer : Int)
    (seg1 seg2 cnt10 cnt11 cnt20 cnt21 : List Int) (hf : EditGreedyCompletedMaximumFacts s1 s2 t1 t2 n)
    (hs : EditGreedyPrefixState s1 s2 t1 t2 n n answer seg1 seg2 cnt10 cnt11 cnt20 cnt21) :
    EditGreedyCompletedStateFacts s1 s2 t1 t2 n answer seg1 seg2 cnt10 cnt11 cnt20 cnt21 :=
  ⟨hs, hf answer seg1 seg2 cnt10 cnt11 cnt20 cnt21 hs⟩

theorem EditGreedyCompletedStateFacts_to_Maximum (s1 s2 t1 t2 : List Int) (n answer : Int)
    (seg1 seg2 cnt10 cnt11 cnt20 cnt21 : List Int)
    (hf : EditGreedyCompletedStateFacts s1 s2 t1 t2 n answer seg1 seg2 cnt10 cnt11 cnt20 cnt21) :
    EditStringsMaximum s1 s2 t1 t2 n answer := by
  obtain ⟨_, _, _, _, hb1, hb2, _⟩ := hf.1.2.2
  exact ⟨hb1.2.1, hb2.2.1, hb1.2.2.1, hb2.2.2.1, hf.2.1, hf.2.2⟩

theorem EditGreedyCompletedMaximumFacts_to_Maximum (s1 s2 t1 t2 : List Int) (n answer : Int)
    (seg1 seg2 cnt10 cnt11 cnt20 cnt21 : List Int) (hf : EditGreedyCompletedMaximumFacts s1 s2 t1 t2 n)
    (hs : EditGreedyPrefixState s1 s2 t1 t2 n n answer seg1 seg2 cnt10 cnt11 cnt20 cnt21) :
    EditStringsMaximum s1 s2 t1 t2 n answer :=
  EditGreedyCompletedStateFacts_to_Maximum s1 s2 t1 t2 n answer seg1 seg2 cnt10 cnt11 cnt20 cnt21
    ⟨hs, hf answer seg1 seg2 cnt10 cnt11 cnt20 cnt21 hs⟩

theorem edit_zrange_between_in__build_s1_segments_counts (lo hi k : Int) (hh : lo ≤ hi) :
    k ∈ edit_zrange_between lo hi ↔ lo ≤ k ∧ k<hi := by
  simp only [edit_zrange_between, List.mem_map]
  constructor
  · rintro ⟨off, hoff, he⟩
    have ho := List.mem_range.mp hoff
    simp only [Int.ofNat_eq_coe] at he
    omega
  · intro hk
    refine ⟨(k-lo).toNat, List.mem_range.mpr (by omega), ?_⟩
    simp only [Int.ofNat_eq_coe]
    omega

theorem edit_edge_openb_true_iff__build_s1_segments_counts (t : List Int) (idx : Int) :
    edit_edge_openb t idx=true ↔ edit_edge_open t idx := by simp [edit_edge_openb, edit_edge_open]

theorem edit_all_edges_openb_true_iff__build_s1_segments_counts (t : List Int) (lo hi : Int) (hh : lo ≤ hi) :
    edit_all_edges_openb t lo hi=true ↔ ∀ k, (lo ≤ k ∧ k<hi) → edit_edge_open t k := by
  simp only [edit_all_edges_openb, List.all_eq_true]
  constructor
  · intro h k hk
    exact (edit_edge_openb_true_iff__build_s1_segments_counts t k).mp (h k ((edit_zrange_between_in__build_s1_segments_counts lo hi k hh).mpr hk))
  · intro h k hk
    exact (edit_edge_openb_true_iff__build_s1_segments_counts t k).mpr (h k ((edit_zrange_between_in__build_s1_segments_counts lo hi k hh).mp hk))

theorem edit_block_startb_true_iff__build_s1_segments_counts (t : List Int) (idx start : Int) :
    edit_block_startb t idx start=true ↔ EditBlockStart t idx start := by
  simp only [edit_block_startb, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨⟨⟨hs0, hsi⟩, hall⟩, hend⟩
    refine ⟨⟨hs0,hsi⟩, ?_, ?_⟩
    · intro k hk
      exact (edit_all_edges_openb_true_iff__build_s1_segments_counts t (start+1) (idx+1) (by omega)).mp hall k (by omega)
    · rcases hend with hz|hn
      · exact Or.inl hz
      · right; intro ho
        have := (edit_edge_openb_true_iff__build_s1_segments_counts t start).mpr ho
        simp_all
  · rintro ⟨hs, hall, hend⟩
    refine ⟨⟨⟨hs.1, hs.2⟩, ?_⟩, ?_⟩
    · apply (edit_all_edges_openb_true_iff__build_s1_segments_counts t (start+1) (idx+1) (by omega)).mpr
      intro k hk; exact hall k (by omega)
    · rcases hend with hz|hn
      · exact Or.inl hz
      · right
        cases he : edit_edge_openb t start with
        | false => rfl
        | true => exact False.elim (hn ((edit_edge_openb_true_iff__build_s1_segments_counts t start).mp he))

theorem EditBlockStart_unique__build_s1_segments_counts (t : List Int) (idx a b : Int)
    (ha : EditBlockStart t idx a) (hb : EditBlockStart t idx b) : a=b := by
  obtain ⟨ha0, haedge, haend⟩ := ha
  obtain ⟨hb0, hbedge, hbend⟩ := hb
  by_cases hab : a<b
  · have he := haedge b (by omega)
    rcases hbend with hz|hn <;> first | omega | exact False.elim (hn he)
  · by_cases hba : b<a
    · have he := hbedge a (by omega)
      rcases haend with hz|hn <;> first | omega | exact False.elim (hn he)
    · omega

theorem edit_zrange_in__build_s1_segments_counts (n k : Int) (hn : 0 ≤ n) :
    k ∈ edit_zrange n ↔ 0 ≤ k ∧ k<n := by
  simp only [edit_zrange, List.mem_map]
  constructor
  · rintro ⟨off, hoff, he⟩
    have ho := List.mem_range.mp hoff
    simp only [Int.ofNat_eq_coe] at he
    omega
  · intro hk
    exact ⟨k.toNat, List.mem_range.mpr (by omega), by simp only [Int.ofNat_eq_coe]; omega⟩

theorem edit_NoDup_map_inj__greedy_common_and_mismatch_steps {A B : Type} (f : A → B) (l : List A)
    (hinj : ∀ x y, x ∈ l → y ∈ l → f x=f y → x=y) (hn : NoDup l) : NoDup (l.map f) := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x l ih =>
    have hnc := List.nodup_cons.mp hn
    apply List.nodup_cons.mpr
    refine ⟨?_, ih (fun a b ha hb he => hinj a b (by simp [ha]) (by simp [hb]) he) hnc.2⟩
    intro hm
    obtain ⟨y, hy, he⟩ := List.mem_map.mp hm
    have hxy := hinj y x (by simp [hy]) (by simp) he
    exact hnc.1 (hxy ▸ hy)

theorem edit_zrange_NoDup__build_s1_segments_counts (n : Int) : NoDup (edit_zrange n) :=
  edit_NoDup_map_inj__greedy_common_and_mismatch_steps Int.ofNat (List.range n.toNat)
    (by intro x y hx hy he; exact Int.ofNat.inj he) (List.nodup_range)

theorem NoDup_filter_bool__build_s1_segments_counts (A : Type) (p : A → Bool) (xs : List A)
    (hn : NoDup xs) : NoDup (xs.filter p) := List.filter_sublist.nodup hn

private theorem nodup_subset_length (xs ys : List Int) (hn : xs.Nodup)
    (hsub : ∀ x, x∈xs → x∈ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    have hnc := List.nodup_cons.mp hn
    have hxm := hsub x (by simp)
    have h := ih (ys.erase x) hnc.2 (by
      intro y hy
      exact (List.mem_erase_of_ne (by intro he; subst y; exact hnc.1 hy)).mpr (hsub y (by simp [hy])))
    rw [List.length_erase_of_mem hxm] at h
    simp only [List.length_cons]
    have hyn : 0<ys.length := List.length_pos_of_mem hxm
    omega

theorem NoDup_zlist_range_length__build_s1_segments_counts (limit : Int) (picks : List Int)
    (hl : 0 ≤ limit) (hn : NoDup picks) (hf : Forall (fun i => 0 ≤ i ∧ i<limit) picks) :
    Int.ofNat picks.length ≤ limit := by
  have h := nodup_subset_length picks (edit_zrange limit) hn (by
    intro x hx
    exact (edit_zrange_in__build_s1_segments_counts limit x hl).mpr (hf.mem hx))
  simp only [edit_zrange, List.length_map, List.length_range] at h
  simp only [Int.ofNat_eq_coe]
  omega

theorem edit_count_bit_in_block_prefix_bound__build_s1_segments_counts (s t : List Int) (limit block bit : Int)
    (hl : 0 ≤ limit ∧ limit ≤ Zlength s) :
    0 ≤ edit_count_bit_in_block_prefix s t limit block bit ∧ edit_count_bit_in_block_prefix s t limit block bit ≤ limit := by
  unfold edit_count_bit_in_block_prefix
  refine ⟨by simp only [Int.ofNat_eq_coe]; omega, NoDup_zlist_range_length__build_s1_segments_counts limit _ hl.1
    (NoDup_filter_bool__build_s1_segments_counts Int _ _ (edit_zrange_NoDup__build_s1_segments_counts _)) ?_⟩
  apply Forall.iff_forall_mem.mpr
  intro idx hi
  obtain ⟨hmem, hpred⟩ := List.mem_filter.mp hi
  have hr := (edit_zrange_in__build_s1_segments_counts (Zlength s) idx (Zlength_nonneg s)).mp hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpred
  exact ⟨hr.1, hpred.1.1⟩

theorem filter_limit_succ_once__build_s1_segments_counts (xs : List Int) (i : Int) (Q : Int → Bool)
    (hn : NoDup xs) (him : i∈xs) (htr : ∀ x, x∈xs → x<i ∨ x=i ∨ i<x) :
    (xs.filter (fun idx => decide (idx<i+1) && Q idx)).length =
      (xs.filter (fun idx => decide (idx<i) && Q idx)).length + (if Q i then 1 else 0) := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    have hnc := List.nodup_cons.mp hn
    by_cases hxi : x=i
    · subst x
      have hf : xs.filter (fun idx => decide (idx<i+1) && Q idx)=xs.filter (fun idx => decide (idx<i) && Q idx) := by
        apply List.filter_congr
        intro j hj
        have hji : j≠i := by intro he; subst j; exact hnc.1 hj
        have he : decide (j<i+1)=decide (j<i) := by
          by_cases hjlt : j<i
          · simp only [decide_eq_true (show j<i+1 by omega), decide_eq_true hjlt]
          · simp only [decide_eq_false (show ¬j<i+1 by omega), decide_eq_false hjlt]
        rw [he]
      simp only [List.filter_cons, decide_eq_true (show i<i+1 by omega), Bool.true_and,
        decide_eq_false (show ¬i<i by omega), Bool.false_and, Bool.false_eq_true, if_false, hf]
      cases hq : Q i <;> simp [hq, List.length_cons, Nat.add_comm]
    · have hit : i∈xs := by simpa only [List.mem_cons, show i≠x from Ne.symm hxi, false_or] using him
      have h := ih hnc.2 hit (fun a ha => htr a (by simp [ha]))
      have he : decide (x<i+1)=decide (x<i) := by
        by_cases hxlt : x<i
        · simp only [decide_eq_true (show x<i+1 by omega), decide_eq_true hxlt]
        · simp only [decide_eq_false (show ¬x<i+1 by omega), decide_eq_false hxlt]
      simp only [List.filter_cons, he]
      cases hb : (decide (x<i) && Q x) <;> simp only [hb, Bool.false_eq_true, Bool.true_eq, if_false, if_true, List.length_cons] <;> omega

theorem edit_count_bit_in_block_prefix_succ__build_s1_segments_counts (s t : List Int) (i block bit : Int)
    (hi : 0 ≤ i ∧ i<Zlength s) :
    edit_count_bit_in_block_prefix s t (i+1) block bit=edit_count_bit_in_block_prefix s t i block bit+
      (if edit_block_startb t i block && edit_bit_atb s i bit then 1 else 0) := by
  have h := filter_limit_succ_once__build_s1_segments_counts (edit_zrange (Zlength s)) i
    (fun idx => edit_block_startb t idx block && edit_bit_atb s idx bit)
    (edit_zrange_NoDup__build_s1_segments_counts _) ((edit_zrange_in__build_s1_segments_counts _ i (Zlength_nonneg s)).mpr hi)
    (by intros; omega)
  unfold edit_count_bit_in_block_prefix
  simp only [Bool.and_assoc] at h ⊢
  rw [h]
  simp only [Int.ofNat_eq_coe, Int.natCast_add]
  split <;> rfl

private theorem edit_count_zero (s t : List Int) (block bit : Int) :
    edit_count_bit_in_block_prefix s t 0 block bit=0 := by
  unfold edit_count_bit_in_block_prefix
  have he : (edit_zrange (Zlength s)).filter (fun idx => decide (idx<0) && edit_block_startb t idx block && edit_bit_atb s idx bit)=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro idx hi
    have hr := (edit_zrange_in__build_s1_segments_counts _ idx (Zlength_nonneg s)).mp hi
    simp [show ¬idx<0 by omega]
  rw [he]
  rfl

theorem EditZeroPrefix_snoc_zero__zeroing_and_base_build (xs : List Int) (i : Int)
    (hp : EditZeroPrefix xs i) : EditZeroPrefix (xs++[0]) (i+1) := by
  refine ⟨by simp only [Zlength_app, Zlength_cons, Zlength_nil, hp.1]; omega, ?_⟩
  intro idx hi
  by_cases hlt : idx<i
  · have he : Znth idx (xs++[0]) 0=Znth idx xs 0 := ListLib.app_Znth1 0 xs [0] idx (by
      change 0 ≤ idx ∧ idx<Zlength xs
      have := hp.1
      omega)
    rw [he]
    exact hp.2 idx (by omega)
  · have he : idx=Zlength xs := by have := hp.1; omega
    rw [he, app_Znth2 0 xs [0] (Zlength xs) (Int.le_refl _), Int.sub_self]
    rfl

theorem EditZeroPrefix_to_full_at_bound__zeroing_and_base_build (n : Int) (xs : List Int) (i : Int)
    (hi : i≥n) (hin : i≤n) (hp : EditZeroPrefix xs i) : EditZeroFull n xs := by
  have : i=n := by omega
  subst i
  exact hp

theorem EditZeroFull_count_bound__zeroing_and_base_build (n : Int) (xs : List Int)
    (hn : 0 ≤ n) (hz : EditZeroFull n xs) : EditCountBounds n xs := by
  refine ⟨hz.1, ?_⟩
  intro idx hi
  rw [hz.2 idx hi]
  exact ⟨Int.le_refl _, hn⟩

theorem EditZeroFull_scratch_bound__zeroing_and_base_build (n : Int) (cnt10 cnt11 cnt20 cnt21 : List Int)
    (hn : 0 ≤ n) (h10 : EditZeroFull n cnt10) (h11 : EditZeroFull n cnt11)
    (h20 : EditZeroFull n cnt20) (h21 : EditZeroFull n cnt21) : EditScratchCountsBound n cnt10 cnt11 cnt20 cnt21 :=
  ⟨EditZeroFull_count_bound__zeroing_and_base_build n cnt10 hn h10, EditZeroFull_count_bound__zeroing_and_base_build n cnt11 hn h11,
    EditZeroFull_count_bound__zeroing_and_base_build n cnt20 hn h20, EditZeroFull_count_bound__zeroing_and_base_build n cnt21 hn h21⟩

theorem edit_filter_ltb_one_seq_from__zeroing_and_base_build (start len : Nat) (pred1 pred2 : Int → Bool)
    (hs : 1 ≤ Int.ofNat start) :
    ((List.range' start len).map Int.ofNat).filter (fun idx => (decide (idx<1) && pred1 idx) && pred2 idx)=[] := by
  apply List.filter_eq_nil_iff.mpr
  intro idx hi
  obtain ⟨off, hoff, he⟩ := List.mem_map.mp hi
  have ho := List.mem_range'.mp hoff
  simp only [Int.ofNat_eq_coe] at hs he
  simp [show ¬idx<1 by omega]

theorem edit_count_bit_in_block_prefix_one__zeroing_and_base_build (s t : List Int) (n block bit : Int)
    (hn : 1 ≤ n) (hlen : Zlength s=n) (hb : 0 ≤ block ∧ block<n) :
    edit_count_bit_in_block_prefix s t 1 block bit =
      if block=0 then if Znth 0 s 0=bit then 1 else 0 else 0 := by
  have h := edit_count_bit_in_block_prefix_succ__build_s1_segments_counts s t 0 block bit (by omega)
  simp only [edit_count_zero, Int.zero_add] at h
  rw [h]
  by_cases hz : block=0
  · subst block
    simp only [edit_block_startb, edit_all_edges_openb, edit_zrange_between, edit_bit_atb]
    simp
  · have hbpos : ¬block≤0 := by omega
    simp only [edit_block_startb, decide_eq_false hbpos, Bool.and_false, Bool.false_and, if_neg hz]
    rfl

private theorem replace_read (xs : List Int) (i j v : Int)
    (hi : 0 ≤ i ∧ i<Zlength xs) (hj : 0 ≤ j ∧ j<Zlength xs) :
    Znth j (replace_Znth i v xs) 0=if j=i then v else Znth j xs 0 := by
  by_cases h : j=i
  · subst j; simp [Znth_replace_Znth_Same 0 xs i v hi]
  · rw [if_neg h, Znth_replace_Znth_Diff 0 xs i j v hi hj (Ne.symm h)]

private theorem bounds_update (n : Int) (xs : List Int) (idx v : Int)
    (hb : EditCountBounds n xs) (hi : 0 ≤ idx ∧ idx<n) (hv : 0 ≤ v ∧ v≤n) :
    EditCountBounds n (replace_Znth idx v xs) := by
  refine ⟨by simpa only [Zlength_replace_Znth] using hb.1, ?_⟩
  intro j hj
  rw [replace_read xs idx j v (by simpa only [hb.1] using hi) (by simpa only [hb.1] using hj)]
  split
  · exact hv
  · exact hb.2 j hj

theorem EditCountBounds_replace_zero_inc__zeroing_and_base_build (n : Int) (xs : List Int)
    (hn : 1 ≤ n) (hz : EditZeroFull n xs) : EditCountBounds n (replace_Znth 0 (Znth 0 xs 0+1) xs) := by
  apply bounds_update n xs 0 _ (EditZeroFull_count_bound__zeroing_and_base_build n xs (by omega) hz) (by omega)
  rw [hz.2 0 (by omega)]
  omega

theorem EditScratchCountsBound_replace_c11_zero_inc__zeroing_and_base_build (n : Int) (c10 c11 c20 c21 : List Int)
    (hn : 1 ≤ n) (hs : EditScratchCountsBound n c10 c11 c20 c21) (hz : EditZeroFull n c11) :
    EditScratchCountsBound n c10 (replace_Znth 0 (Znth 0 c11 0+1) c11) c20 c21 :=
  ⟨hs.1, EditCountBounds_replace_zero_inc__zeroing_and_base_build n c11 hn hz, hs.2.2⟩

theorem EditScratchCountsBound_replace_c10_zero_inc__zeroing_and_base_build (n : Int) (c10 c11 c20 c21 : List Int)
    (hn : 1 ≤ n) (hs : EditScratchCountsBound n c10 c11 c20 c21) (hz : EditZeroFull n c10) :
    EditScratchCountsBound n (replace_Znth 0 (Znth 0 c10 0+1) c10) c11 c20 c21 :=
  ⟨EditCountBounds_replace_zero_inc__zeroing_and_base_build n c10 hn hz, hs.2⟩

theorem EditBinaryList_from_bounds__zeroing_and_base_build (xs : List Int) (n : Int)
    (hlen : Zlength xs=n) (hb : ∀ idx, (0 ≤ idx ∧ idx<n) → 0 ≤ Znth idx xs 0 ∧ Znth idx xs 0≤1) : EditBinaryList xs n := by
  refine ⟨hlen, ?_⟩
  intro idx hi
  have := hb idx hi
  omega

theorem EditSegmentPrefix_one_zero__zeroing_and_base_build (t sg : List Int)
    (hlen : Zlength sg=1) (hz : Znth 0 sg 0=0) : EditSegmentPrefix t 1 sg := by
  refine ⟨hlen, ?_⟩
  intro idx hi
  have : idx=0 := by omega
  subst idx
  rw [hz]
  exact ⟨⟨Int.le_refl _,Int.le_refl _⟩, (by intros; omega), Or.inl rfl⟩

private theorem count_initial (s t : List Int) (n : Int) (cnt0 cnt1 : List Int) (bit : Int)
    (hn : 1 ≤ n) (hlen : Zlength s=n) (hbit : bit=0 ∨ bit=1) (hv : Znth 0 s 0=bit)
    (h0 : EditZeroFull n cnt0) (h1 : EditZeroFull n cnt1) :
    EditCountsForPrefix s t n 1
      (if bit=0 then replace_Znth 0 (Znth 0 cnt0 0+1) cnt0 else cnt0)
      (if bit=1 then replace_Znth 0 (Znth 0 cnt1 0+1) cnt1 else cnt1) := by
  have hn0 : 0 ≤ (0:Int) ∧ 0<n := by omega
  rcases hbit with rfl|rfl <;>
    (try simp only [ite_true, ite_false]) <;>
    refine ⟨by simpa only [Zlength_replace_Znth] using h0.1, by simpa only [Zlength_replace_Znth] using h1.1, ?_, ?_⟩
  all_goals
    intro block hblock
    rw [edit_count_bit_in_block_prefix_one__zeroing_and_base_build s t n block _ hn hlen hblock]
  all_goals
    first
    | rw [replace_read _ 0 block _ (by simpa only [h0.1] using hn0) (by simpa only [h0.1] using hblock)]
    | rw [replace_read _ 0 block _ (by simpa only [h1.1] using hn0) (by simpa only [h1.1] using hblock)]
    | skip
  all_goals simp only [h0.2 _ hblock, h1.2 _ hblock, h0.2 0 hn0, h1.2 0 hn0, hv]; split <;> simp_all
  all_goals first | exact h0.2 block hblock | exact h1.2 block hblock

theorem EditCountsForPrefix_initial_one__zeroing_and_base_build (s t : List Int) (n : Int) (cnt0 cnt1 : List Int)
    (hn : 1 ≤ n) (hlen : Zlength s=n) (hb : ∀ idx, (0 ≤ idx ∧ idx<n) → 0 ≤ Znth idx s 0 ∧ Znth idx s 0≤1)
    (hv : Znth 0 s 0≠0) (h0 : EditZeroFull n cnt0) (h1 : EditZeroFull n cnt1) :
    EditCountsForPrefix s t n 1 cnt0 (replace_Znth 0 (Znth 0 cnt1 0+1) cnt1) := by
  have hz : Znth 0 s 0=1 := by have := hb 0 (by omega); omega
  simpa using count_initial s t n cnt0 cnt1 1 hn hlen (Or.inr rfl) hz h0 h1

theorem EditCountsForPrefix_initial_zero__zeroing_and_base_build (s t : List Int) (n : Int) (cnt0 cnt1 : List Int)
    (hn : 1 ≤ n) (hlen : Zlength s=n) (hv : Znth 0 s 0=0) (h0 : EditZeroFull n cnt0) (h1 : EditZeroFull n cnt1) :
    EditCountsForPrefix s t n 1 (replace_Znth 0 (Znth 0 cnt0 0+1) cnt0) cnt1 := by
  simpa using count_initial s t n cnt0 cnt1 0 hn hlen (Or.inl rfl) hv h0 h1

theorem EditBuildState_initial_s1_one__zeroing_and_base_build (s t : List Int) (n : Int) (sg cnt0 cnt1 : List Int)
    (hn : 1 ≤ n) (hs : Zlength s=n) (ht : Zlength t=n)
    (hbs : ∀ idx, (0 ≤ idx ∧ idx<n) → 0 ≤ Znth idx s 0 ∧ Znth idx s 0≤1)
    (hbt : ∀ idx, (0 ≤ idx ∧ idx<n) → 0 ≤ Znth idx t 0 ∧ Znth idx t 0≤1)
    (hv : Znth 0 s 0≠0) (hg : Zlength sg=1) (hgz : Znth 0 sg 0=0)
    (h0 : EditZeroFull n cnt0) (h1 : EditZeroFull n cnt1) :
    EditBuildState s t n 1 sg cnt0 (replace_Znth 0 (Znth 0 cnt1 0+1) cnt1) :=
  ⟨by omega, EditBinaryList_from_bounds__zeroing_and_base_build s n hs hbs,
    EditBinaryList_from_bounds__zeroing_and_base_build t n ht hbt,
    EditSegmentPrefix_one_zero__zeroing_and_base_build t sg hg hgz,
    EditCountsForPrefix_initial_one__zeroing_and_base_build s t n cnt0 cnt1 hn hs hbs hv h0 h1⟩

theorem EditBuildState_initial_s1_zero__zeroing_and_base_build (s t : List Int) (n : Int) (sg cnt0 cnt1 : List Int)
    (hn : 1 ≤ n) (hs : Zlength s=n) (ht : Zlength t=n)
    (hbs : ∀ idx, (0 ≤ idx ∧ idx<n) → 0 ≤ Znth idx s 0 ∧ Znth idx s 0≤1)
    (hbt : ∀ idx, (0 ≤ idx ∧ idx<n) → 0 ≤ Znth idx t 0 ∧ Znth idx t 0≤1)
    (hv : Znth 0 s 0=0) (hg : Zlength sg=1) (hgz : Znth 0 sg 0=0)
    (h0 : EditZeroFull n cnt0) (h1 : EditZeroFull n cnt1) :
    EditBuildState s t n 1 sg (replace_Znth 0 (Znth 0 cnt0 0+1) cnt0) cnt1 :=
  ⟨by omega, EditBinaryList_from_bounds__zeroing_and_base_build s n hs hbs,
    EditBinaryList_from_bounds__zeroing_and_base_build t n ht hbt,
    EditSegmentPrefix_one_zero__zeroing_and_base_build t sg hg hgz,
    EditCountsForPrefix_initial_zero__zeroing_and_base_build s t n cnt0 cnt1 hn hs hv h0 h1⟩

private theorem snoc_last {A : Type} (xs : List A) (v d : A) (i : Int) (hi : Zlength xs=i) :
    Znth i (xs++[v]) d=v := by
  subst i
  rw [app_Znth2 d xs [v] (Zlength xs) (Int.le_refl _), Int.sub_self]
  rfl

theorem edit_snoc_Znth_last__build_s1_segments_counts (xs : List Int) (i x d : Int)
    (hi : Zlength xs=i) (hn : 0 ≤ i) : Znth i (xs++[x]) d=x := snoc_last xs x d i hi

private theorem segment_snoc (t : List Int) (i : Int) (sg : List Int) (v : Int)
    (hg : EditSegmentPrefix t i sg) (hi : 0 ≤ i) (hv : EditBlockStart t i v) :
    EditSegmentPrefix t (i+1) (sg++[v]) := by
  refine ⟨by simp only [Zlength_app,Zlength_cons,Zlength_nil,hg.1]; omega, ?_⟩
  intro idx hidx
  by_cases hlt : idx<i
  · have he : Znth idx (sg++[v]) 0=Znth idx sg 0 := ListLib.app_Znth1 0 sg [v] idx (by change 0≤idx∧idx<Zlength sg; rw[hg.1]; omega)
    rw [he]
    exact hg.2 idx (by omega)
  · have : idx=i := by omega
    subst idx
    rw [snoc_last sg v 0 i hg.1]
    exact hv

theorem EditSegmentPrefix_extend_new__build_s1_segments_counts (t : List Int) (i : Int) (sg : List Int)
    (hg : EditSegmentPrefix t i sg) (hi : 0 ≤ i) (he : ¬edit_edge_open t i) :
    EditSegmentPrefix t (i+1) (sg++[i]) :=
  segment_snoc t i sg i hg hi ⟨⟨hi,Int.le_refl _⟩,(by intros; omega),Or.inr he⟩

theorem EditSegmentPrefix_extend_open__build_s1_segments_counts (t : List Int) (i : Int) (sg : List Int)
    (hg : EditSegmentPrefix t i sg) (hi : 1 ≤ i) (he : edit_edge_open t i) :
    EditSegmentPrefix t (i+1) (sg++[Znth (i-1) sg 0]) := by
  have hb := hg.2 (i-1) (by omega)
  apply segment_snoc t i sg _ hg (by omega)
  refine ⟨⟨hb.1.1,by have := hb.1.2; omega⟩,?_,hb.2.2⟩
  intro k hk
  by_cases hki : k=i
  · simpa only [hki] using he
  · exact hb.2.1 k (by omega)

theorem EditSegmentPrefix_last_block_bounds__build_s1_segments_counts (t : List Int) (i : Int) (sg : List Int)
    (hg : EditSegmentPrefix t i sg) (hi : 1 ≤ i) : 0 ≤ Znth (i-1) sg 0 ∧ Znth (i-1) sg 0<i := by
  have hb := (hg.2 (i-1) (by omega)).1
  omega

private theorem block_bool_at (t : List Int) (i block k : Int) (hb : EditBlockStart t i block) :
    edit_block_startb t i k=decide (k=block) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, edit_block_startb_true_iff__build_s1_segments_counts]
  constructor
  · intro hk; exact EditBlockStart_unique__build_s1_segments_counts t i k block hk hb
  · intro hk; simpa only [hk] using hb

private theorem count_extend_single (s t : List Int) (n i block bit : Int) (cnt : List Int)
    (hs : Zlength s=n) (hi : 0 ≤ i ∧ i<n) (hb : EditBlockStart t i block)
    (hc : Zlength cnt=n) (hv : ∀ k, (0 ≤ k ∧ k<n) → Znth k cnt 0=edit_count_bit_in_block_prefix s t i k bit) :
    ∀ k, (0 ≤ k ∧ k<n) →
      Znth k (if Znth i s 0=bit then replace_Znth block (Znth block cnt 0+1) cnt else cnt) 0=
        edit_count_bit_in_block_prefix s t (i+1) k bit := by
  intro k hk
  have hblock : 0 ≤ block ∧ block<n := by have := hb.1; omega
  rw [edit_count_bit_in_block_prefix_succ__build_s1_segments_counts s t i k bit (by simpa only [hs] using hi),
    block_bool_at t i block k hb]
  unfold edit_bit_atb
  by_cases hbit : Znth i s 0=bit
  · rw [if_pos hbit, replace_read cnt block k _ (by simpa only [hc] using hblock) (by simpa only [hc] using hk)]
    by_cases he : k=block
    · subst k; simp [hv block hblock,hbit]
    · simp [he,hbit,hv k hk]
  · simp [hbit,hv k hk]

private theorem counts_extend (s t : List Int) (n i : Int) (sg cnt0 cnt1 : List Int) (block bit : Int)
    (hs : Zlength s=n) (hi : 0 ≤ i ∧ i<n) (hg : EditSegmentPrefix t (i+1) sg)
    (hc : EditCountsForPrefix s t n i cnt0 cnt1) (hblock : block=Znth i sg 0)
    (hbit : bit=0 ∨ bit=1) (hv : Znth i s 0=bit) :
    EditCountsForPrefix s t n (i+1)
      (if bit=0 then replace_Znth block (Znth block cnt0 0+1) cnt0 else cnt0)
      (if bit=1 then replace_Znth block (Znth block cnt1 0+1) cnt1 else cnt1) := by
  have hb : EditBlockStart t i block := by rw [hblock]; exact hg.2 i (by omega)
  have h0 := count_extend_single s t n i block 0 cnt0 hs hi hb hc.1 hc.2.2.1
  have h1 := count_extend_single s t n i block 1 cnt1 hs hi hb hc.2.1 hc.2.2.2
  rcases hbit with rfl|rfl <;> simp only [hv,ite_true,ite_false] at h0 h1 ⊢ <;>
    exact ⟨by simpa only [Zlength_replace_Znth] using hc.1, by simpa only [Zlength_replace_Znth] using hc.2.1,h0,h1⟩

theorem EditCountsForPrefix_extend_one__build_s1_segments_counts (s t : List Int) (n i : Int) (sg cnt0 cnt1 : List Int) (block : Int)
    (hs : Zlength s=n) (hi : 0 ≤ i ∧ i<n) (hg : EditSegmentPrefix t (i+1) sg)
    (hc : EditCountsForPrefix s t n i cnt0 cnt1) (hb : block=Znth i sg 0) (hv : Znth i s 0≠0)
    (hbs : ∀ idx, (0 ≤ idx ∧ idx<n) → 0 ≤ Znth idx s 0 ∧ Znth idx s 0≤1) :
    EditCountsForPrefix s t n (i+1) cnt0 (replace_Znth block (Znth block cnt1 0+1) cnt1) := by
  have hbit : Znth i s 0=1 := by have := hbs i hi; omega
  simpa using counts_extend s t n i sg cnt0 cnt1 block 1 hs hi hg hc hb (Or.inr rfl) hbit

theorem EditCountsForPrefix_extend_zero__build_s1_segments_counts (s t : List Int) (n i : Int) (sg cnt0 cnt1 : List Int) (block : Int)
    (hs : Zlength s=n) (hi : 0 ≤ i ∧ i<n) (hg : EditSegmentPrefix t (i+1) sg)
    (hc : EditCountsForPrefix s t n i cnt0 cnt1) (hb : block=Znth i sg 0) (hv : Znth i s 0=0) :
    EditCountsForPrefix s t n (i+1) (replace_Znth block (Znth block cnt0 0+1) cnt0) cnt1 := by
  simpa using counts_extend s t n i sg cnt0 cnt1 block 0 hs hi hg hc hb (Or.inl rfl) hv

private theorem bound_inc (s t : List Int) (n i : Int) (cnt : List Int) (block bit : Int)
    (hs : Zlength s=n) (hi : 0 ≤ i ∧ i<n) (hb : 0 ≤ block ∧ block<n)
    (hc : Znth block cnt 0=edit_count_bit_in_block_prefix s t i block bit) (hbound : EditCountBounds n cnt) :
    EditCountBounds n (replace_Znth block (Znth block cnt 0+1) cnt) := by
  apply bounds_update n cnt block _ hbound hb
  have h := edit_count_bit_in_block_prefix_bound__build_s1_segments_counts s t i block bit (by omega)
  omega

theorem EditScratchCountsBound_inc_second__build_s1_segments_counts (s t : List Int) (n i : Int) (cnt0 cnt1 cnt20 cnt21 : List Int) (block : Int)
    (hs : Zlength s=n) (hi : 0 ≤ i ∧ i<n) (hc : EditCountsForPrefix s t n i cnt0 cnt1)
    (hb : 0 ≤ block ∧ block<n) (hbound : EditScratchCountsBound n cnt0 cnt1 cnt20 cnt21) :
    EditScratchCountsBound n cnt0 (replace_Znth block (Znth block cnt1 0+1) cnt1) cnt20 cnt21 :=
  ⟨hbound.1,bound_inc s t n i cnt1 block 1 hs hi hb (hc.2.2.2 block hb) hbound.2.1,hbound.2.2⟩

theorem EditScratchCountsBound_inc_first__build_s1_segments_counts (s t : List Int) (n i : Int) (cnt0 cnt1 cnt20 cnt21 : List Int) (block : Int)
    (hs : Zlength s=n) (hi : 0 ≤ i ∧ i<n) (hc : EditCountsForPrefix s t n i cnt0 cnt1)
    (hb : 0 ≤ block ∧ block<n) (hbound : EditScratchCountsBound n cnt0 cnt1 cnt20 cnt21) :
    EditScratchCountsBound n (replace_Znth block (Znth block cnt0 0+1) cnt0) cnt1 cnt20 cnt21 :=
  ⟨bound_inc s t n i cnt0 block 0 hs hi hb (hc.2.2.1 block hb) hbound.1,hbound.2⟩

theorem EditBuildState_extend_one__build_s1_segments_counts (s t : List Int) (n i : Int) (sg cnt0 cnt1 : List Int) (block : Int)
    (hs : Zlength s=n) (ht : Zlength t=n)
    (hbs : ∀ idx, (0 ≤ idx ∧ idx<n) → 0 ≤ Znth idx s 0 ∧ Znth idx s 0≤1)
    (hbt : ∀ idx, (0 ≤ idx ∧ idx<n) → 0 ≤ Znth idx t 0 ∧ Znth idx t 0≤1)
    (hi : 0 ≤ i ∧ i<n) (hg : EditSegmentPrefix t (i+1) sg) (hc : EditCountsForPrefix s t n i cnt0 cnt1)
    (hb : block=Znth i sg 0) (hv : Znth i s 0≠0) :
    EditBuildState s t n (i+1) sg cnt0 (replace_Znth block (Znth block cnt1 0+1) cnt1) :=
  ⟨by omega, EditBinaryList_from_bounds__zeroing_and_base_build s n hs hbs,
    EditBinaryList_from_bounds__zeroing_and_base_build t n ht hbt,hg,
    EditCountsForPrefix_extend_one__build_s1_segments_counts s t n i sg cnt0 cnt1 block hs hi hg hc hb hv hbs⟩

theorem EditBuildState_extend_zero__build_s1_segments_counts (s t : List Int) (n i : Int) (sg cnt0 cnt1 : List Int) (block : Int)
    (hs : Zlength s=n) (ht : Zlength t=n)
    (hbs : ∀ idx, (0 ≤ idx ∧ idx<n) → 0 ≤ Znth idx s 0 ∧ Znth idx s 0≤1)
    (hbt : ∀ idx, (0 ≤ idx ∧ idx<n) → 0 ≤ Znth idx t 0 ∧ Znth idx t 0≤1)
    (hi : 0 ≤ i ∧ i<n) (hg : EditSegmentPrefix t (i+1) sg) (hc : EditCountsForPrefix s t n i cnt0 cnt1)
    (hb : block=Znth i sg 0) (hv : Znth i s 0=0) :
    EditBuildState s t n (i+1) sg (replace_Znth block (Znth block cnt0 0+1) cnt0) cnt1 :=
  ⟨by omega, EditBinaryList_from_bounds__zeroing_and_base_build s n hs hbs,
    EditBinaryList_from_bounds__zeroing_and_base_build t n ht hbt,hg,
    EditCountsForPrefix_extend_zero__build_s1_segments_counts s t n i sg cnt0 cnt1 block hs hi hg hc hb hv⟩

theorem edit_seq_add__build_s2_segments_counts (start len : Nat) :
    List.range' start len=(List.range' 0 len).map (fun off => start+off) := by
  simpa only [←List.range_eq_range'] using (List.range'_eq_map_range (s:=start) (n:=len))

theorem edit_zrange_between_cons__build_s2_segments_counts (lo hi : Int) (hh : lo<hi) :
    edit_zrange_between lo hi=lo::edit_zrange_between (lo+1) hi := by
  have hlen : (hi-lo).toNat=(hi-(lo+1)).toNat+1 := by omega
  unfold edit_zrange_between
  rw [hlen,List.range_succ_eq_map,List.map_cons,List.map_map]
  congr 1
  · simp
  · apply List.map_congr_left
    intro off _
    simp only [Function.comp_apply,Int.ofNat_eq_coe,Int.natCast_add,Int.natCast_one]
    omega

private theorem between_split (lo mid hi : Int) (hm : lo≤mid) (hh : mid≤hi) :
    edit_zrange_between lo hi=edit_zrange_between lo mid++edit_zrange_between mid hi := by
  have hlen : (hi-lo).toNat=(mid-lo).toNat+(hi-mid).toNat := by omega
  unfold edit_zrange_between
  rw [hlen,List.range_add,List.map_append,List.map_map]
  congr 1
  apply List.map_congr_left
  intro off _
  simp only [Function.comp_apply,Int.ofNat_eq_coe,Int.natCast_add]
  omega

theorem edit_zrange_split__build_s2_segments_counts (n i : Int) (hi : 0≤i ∧ i<n) :
    edit_zrange n=edit_zrange i++i::edit_zrange_between (i+1) n := by
  have hn : edit_zrange n=edit_zrange_between 0 n := by simp [edit_zrange,edit_zrange_between]
  have he : edit_zrange_between 0 i=edit_zrange i := by simp [edit_zrange,edit_zrange_between]
  rw [hn,between_split 0 i n hi.1 (by omega),he,edit_zrange_between_cons__build_s2_segments_counts i n hi.2]

theorem edit_zrange_In__build_s2_segments_counts (n idx : Int) (hi : idx∈edit_zrange n) : 0≤idx ∧ idx<n := by
  obtain ⟨k,hk,he⟩ := List.mem_map.mp hi
  have hh := List.mem_range.mp hk
  simp only [Int.ofNat_eq_coe] at he
  omega

theorem edit_zrange_between_In__build_s2_segments_counts (lo hi idx : Int) (hm : idx∈edit_zrange_between lo hi) : lo≤idx ∧ idx<hi := by
  obtain ⟨k,hk,he⟩ := List.mem_map.mp hm
  have hh := List.mem_range.mp hk
  simp only [Int.ofNat_eq_coe] at he
  omega

theorem edit_filter_all_false__build_s2_segments_counts {A : Type} (f : A→Bool) (xs : List A)
    (h : ∀ x, x∈xs → f x=false) : xs.filter f=[] := by
  apply List.filter_eq_nil_iff.mpr
  intro x hx
  simp only [h x hx,Bool.false_eq_true,not_false_eq_true]

theorem edit_count_bit_in_block_prefix_succ__build_s2_segments_counts (s t : List Int) (n i block bit : Int)
    (hs : Zlength s=n) (hi : 0≤i ∧ i<n) :
    edit_count_bit_in_block_prefix s t (i+1) block bit=edit_count_bit_in_block_prefix s t i block bit+
      (if edit_block_startb t i block && edit_bit_atb s i bit then 1 else 0) :=
  edit_count_bit_in_block_prefix_succ__build_s1_segments_counts s t i block bit (by omega)

theorem edit_block_startb_zero__build_s2_segments_counts (t : List Int) (block : Int) :
    edit_block_startb t 0 block=decide (block=0) :=
  block_bool_at t 0 0 block ⟨⟨by omega,by omega⟩,(by intros;omega),Or.inl rfl⟩

private theorem count_one_all (s t : List Int) (n block bit : Int) (hs : Zlength s=n) (hn : 1≤n) :
    edit_count_bit_in_block_prefix s t 1 block bit=if block=0 then if Znth 0 s 0=bit then 1 else 0 else 0 := by
  have h := edit_count_bit_in_block_prefix_succ__build_s1_segments_counts s t 0 block bit (by omega)
  simp only [Int.zero_add,edit_count_zero,edit_block_startb_zero__build_s2_segments_counts,edit_bit_atb] at h
  rw [h]
  by_cases hb : block=0 <;> by_cases hv : Znth 0 s 0=bit <;> simp [hb,hv]

theorem edit_count_prefix_one_nonzero_zero_bit__build_s2_segments_counts (s t : List Int) (n block : Int)
    (hs : Zlength s=n) (hn : 1≤n) (hz : Znth 0 s 0≠0)
    (hb : ∀ idx, (0≤idx ∧ idx<n) → 0≤Znth idx s 0 ∧ Znth idx s 0≤1) :
    edit_count_bit_in_block_prefix s t 1 block 0=0 := by
  rw [count_one_all s t n block 0 hs hn]
  simp [hz]

theorem edit_count_prefix_one_nonzero_one_bit__build_s2_segments_counts (s t : List Int) (n block : Int)
    (hs : Zlength s=n) (hn : 1≤n) (hz : Znth 0 s 0≠0)
    (hb : ∀ idx, (0≤idx ∧ idx<n) → 0≤Znth idx s 0 ∧ Znth idx s 0≤1) :
    edit_count_bit_in_block_prefix s t 1 block 1=(if decide (block=0) then 1 else 0) := by
  have hv : Znth 0 s 0=1 := by have := hb 0 (by omega); omega
  rw [count_one_all s t n block 1 hs hn]
  simp [hv]

theorem edit_count_prefix_one_zero_zero_bit__build_s2_segments_counts (s t : List Int) (n block : Int)
    (hs : Zlength s=n) (hn : 1≤n) (hz : Znth 0 s 0=0) :
    edit_count_bit_in_block_prefix s t 1 block 0=(if decide (block=0) then 1 else 0) := by
  rw [count_one_all s t n block 0 hs hn]
  simp [hz]

theorem edit_count_prefix_one_zero_one_bit__build_s2_segments_counts (s t : List Int) (n block : Int)
    (hs : Zlength s=n) (hn : 1≤n) (hz : Znth 0 s 0=0) :
    edit_count_bit_in_block_prefix s t 1 block 1=0 := by
  rw [count_one_all s t n block 1 hs hn]
  simp [hz]

theorem edit_zrange_between_In_iff__build_s2_segments_counts (lo hi idx : Int) :
    idx∈edit_zrange_between lo hi ↔ lo≤idx ∧ idx<hi := by
  constructor
  · exact edit_zrange_between_In__build_s2_segments_counts lo hi idx
  · intro h
    exact (edit_zrange_between_in__build_s1_segments_counts lo hi idx (by omega)).mpr h

theorem edit_edge_openb_true_iff__build_s2_segments_counts (t : List Int) (idx : Int) :
    edit_edge_openb t idx=true ↔ edit_edge_open t idx := edit_edge_openb_true_iff__build_s1_segments_counts t idx

theorem edit_all_edges_openb_true_iff__build_s2_segments_counts (t : List Int) (lo hi : Int) :
    edit_all_edges_openb t lo hi=true ↔ ∀ k, (lo≤k ∧ k<hi) → edit_edge_open t k := by
  simp only [edit_all_edges_openb,List.all_eq_true,edit_edge_openb_true_iff__build_s1_segments_counts,
    edit_zrange_between_In_iff__build_s2_segments_counts]

theorem edit_block_startb_true_iff__build_s2_segments_counts (t : List Int) (idx start : Int) :
    edit_block_startb t idx start=true ↔ EditBlockStart t idx start := edit_block_startb_true_iff__build_s1_segments_counts t idx start

theorem edit_block_start_unique__build_s2_segments_counts (t : List Int) (idx start1 start2 : Int)
    (h1 : EditBlockStart t idx start1) (h2 : EditBlockStart t idx start2) : start1=start2 :=
  EditBlockStart_unique__build_s1_segments_counts t idx start1 start2 h1 h2

theorem edit_block_startb_unique__build_s2_segments_counts (t : List Int) (idx start block : Int)
    (hs : EditBlockStart t idx start) (hb : edit_block_startb t idx block=true) : block=start :=
  EditBlockStart_unique__build_s1_segments_counts t idx block start ((edit_block_startb_true_iff__build_s1_segments_counts t idx block).mp hb) hs

theorem edit_Znth_app_last__build_s2_segments_counts {A : Type} (xs : List A) (v d : A) (i : Int)
    (hi : Zlength xs=i) : Znth i (xs++[v]) d=v := snoc_last xs v d i hi

theorem edit_segment_prefix_append_new__build_s2_segments_counts (t : List Int) (i : Int) (sg : List Int)
    (hg : EditSegmentPrefix t i sg) (hi : 0≤i) (he : ¬edit_edge_open t i) :
    EditSegmentPrefix t (i+1) (sg++[i]) := EditSegmentPrefix_extend_new__build_s1_segments_counts t i sg hg hi he

theorem edit_segment_prefix_append_same__build_s2_segments_counts (t : List Int) (i : Int) (sg : List Int)
    (hg : EditSegmentPrefix t i sg) (hi : 1≤i) (he : edit_edge_open t i) :
    EditSegmentPrefix t (i+1) (sg++[Znth (i-1) sg 0]) := EditSegmentPrefix_extend_open__build_s1_segments_counts t i sg hg hi he

theorem edit_count_bit_in_block_prefix_bound_n__build_s2_segments_counts (s t : List Int) (n upto block bit : Int)
    (hs : Zlength s=n) (hn : 0≤n) : 0≤edit_count_bit_in_block_prefix s t upto block bit ∧ edit_count_bit_in_block_prefix s t upto block bit≤n := by
  have hl := List.length_filter_le (fun idx => decide (idx<upto) && edit_block_startb t idx block && edit_bit_atb s idx bit) (edit_zrange (Zlength s))
  have he : Int.ofNat (edit_zrange (Zlength s)).length=n := by
    simp only [edit_zrange,List.length_map,List.length_range,Int.ofNat_eq_coe]
    omega
  unfold edit_count_bit_in_block_prefix
  simp only [Int.ofNat_eq_coe] at he ⊢
  omega

theorem edit_counts_prefix_extend_one__build_s2_segments_counts (s t : List Int) (n i : Int) (seg cnt0 cnt1 : List Int) (block : Int)
    (hs : Zlength s=n) (hi : 0≤i ∧ i<n) (hg : EditSegmentPrefix t (i+1) seg)
    (hc : EditCountsForPrefix s t n i cnt0 cnt1) (hb : block=Znth i seg 0) (hv : Znth i s 0=1) :
    EditCountsForPrefix s t n (i+1) cnt0 (replace_Znth block (Znth block cnt1 0+1) cnt1) := by
  simpa using counts_extend s t n i seg cnt0 cnt1 block 1 hs hi hg hc hb (Or.inr rfl) hv

theorem edit_counts_prefix_extend_zero__build_s2_segments_counts (s t : List Int) (n i : Int) (seg cnt0 cnt1 : List Int) (block : Int)
    (hs : Zlength s=n) (hi : 0≤i ∧ i<n) (hg : EditSegmentPrefix t (i+1) seg)
    (hc : EditCountsForPrefix s t n i cnt0 cnt1) (hb : block=Znth i seg 0) (hv : Znth i s 0=0) :
    EditCountsForPrefix s t n (i+1) (replace_Znth block (Znth block cnt0 0+1) cnt0) cnt1 :=
  EditCountsForPrefix_extend_zero__build_s1_segments_counts s t n i seg cnt0 cnt1 block hs hi hg hc hb hv

theorem edit_scratch_bound_update_one__build_s2_segments_counts (s t : List Int) (n i : Int) (seg cnt10 cnt11 cnt20 cnt21 : List Int) (block : Int)
    (hs : Zlength s=n) (hi : 0≤i ∧ i<n) (hg : EditSegmentPrefix t (i+1) seg)
    (hc : EditCountsForPrefix s t n i cnt20 cnt21) (hbound : EditScratchCountsBound n cnt10 cnt11 cnt20 cnt21)
    (hb : block=Znth i seg 0) (hv : Znth i s 0=1) :
    EditScratchCountsBound n cnt10 cnt11 cnt20 (replace_Znth block (Znth block cnt21 0+1) cnt21) := by
  have hbnd : 0≤block ∧ block<n := by have := (hg.2 i (by omega)).1; omega
  exact ⟨hbound.1,hbound.2.1,hbound.2.2.1,bound_inc s t n i cnt21 block 1 hs hi hbnd (hc.2.2.2 block hbnd) hbound.2.2.2⟩

theorem edit_scratch_bound_update_zero__build_s2_segments_counts (s t : List Int) (n i : Int) (seg cnt10 cnt11 cnt20 cnt21 : List Int) (block : Int)
    (hs : Zlength s=n) (hi : 0≤i ∧ i<n) (hg : EditSegmentPrefix t (i+1) seg)
    (hc : EditCountsForPrefix s t n i cnt20 cnt21) (hbound : EditScratchCountsBound n cnt10 cnt11 cnt20 cnt21)
    (hb : block=Znth i seg 0) (hv : Znth i s 0=0) :
    EditScratchCountsBound n cnt10 cnt11 (replace_Znth block (Znth block cnt20 0+1) cnt20) cnt21 := by
  have hbnd : 0≤block ∧ block<n := by have := (hg.2 i (by omega)).1; omega
  exact ⟨hbound.1,hbound.2.1,bound_inc s t n i cnt20 block 0 hs hi hbnd (hc.2.2.1 block hbnd) hbound.2.2.1,hbound.2.2.2⟩

theorem edit_zrange_nodup__greedy_common_and_mismatch_steps (n : Int) : (edit_zrange n).Nodup :=
  edit_zrange_NoDup__build_s1_segments_counts n

theorem edit_zrange_in__greedy_common_and_mismatch_steps (n idx : Int) (hi : 0≤idx ∧ idx<n) : idx∈edit_zrange n :=
  (edit_zrange_in__build_s1_segments_counts n idx (by omega)).mpr hi

theorem edit_zrange_in_bounds__greedy_common_and_mismatch_steps (n idx : Int) (hi : idx∈edit_zrange n) : 0≤idx ∧ idx<n :=
  edit_zrange_In__build_s2_segments_counts n idx hi

theorem edit_edge_openb_true_iff__greedy_common_and_mismatch_steps (t : List Int) (idx : Int) :
    edit_edge_openb t idx=true ↔ edit_edge_open t idx := edit_edge_openb_true_iff__build_s1_segments_counts t idx

theorem edit_all_edges_openb_true__greedy_common_and_mismatch_steps (t : List Int) (lo hi : Int)
    (h : ∀ k, (lo≤k ∧ k<hi) → edit_edge_open t k) : edit_all_edges_openb t lo hi=true :=
  (edit_all_edges_openb_true_iff__build_s2_segments_counts t lo hi).mpr h

theorem edit_block_startb_true__greedy_common_and_mismatch_steps (t : List Int) (idx start : Int)
    (h : EditBlockStart t idx start) : edit_block_startb t idx start=true :=
  (edit_block_startb_true_iff__build_s1_segments_counts t idx start).mpr h

theorem edit_count_positions_prefix_lt_full_counts_current__greedy_common_and_mismatch_steps
    (s t : List Int) (n : Int) (seg full0 full1 : List Int) (i : Int)
    (hb : EditBuildState s t n n seg full0 full1) (hi : 0≤i ∧ i<n) :
    edit_count_positions_in_seg_prefix seg i (Znth i seg 0)<Znth (Znth i seg 0) full0 0+Znth (Znth i seg 0) full1 0 := by
  let block := Znth i seg 0
  have hg := hb.2.2.2.1
  have hs := hb.2.1
  have hc := hb.2.2.2.2
  have hblock : 0≤block ∧ block<n := by have := (hg.2 i hi).1; dsimp [block]; omega
  rw [hc.2.2.1 block hblock,hc.2.2.2 block hblock]
  unfold edit_count_positions_in_seg_prefix edit_count_bit_in_block_prefix
  rw [hg.1,hs.1]
  let xs := edit_zrange n
  let P := fun idx => decide (idx<i) && decide (Znth idx seg 0=block)
  let Q0 := fun idx => decide (idx<n) && edit_block_startb t idx block && edit_bit_atb s idx 0
  let Q1 := fun idx => decide (idx<n) && edit_block_startb t idx block && edit_bit_atb s idx 1
  change Int.ofNat (xs.filter P).length<Int.ofNat (xs.filter Q0).length+Int.ofNat (xs.filter Q1).length
  have hin : i∈xs := edit_zrange_in__greedy_common_and_mismatch_steps n i hi
  have hnot : i∉xs.filter P := by
    intro h
    have := (List.mem_filter.mp h).2
    simp [P] at this
  have hnodup : (i::xs.filter P).Nodup := List.nodup_cons.mpr
    ⟨hnot,List.filter_sublist.nodup (edit_zrange_NoDup__build_s1_segments_counts n)⟩
  have hsub : ∀ x, x∈i::xs.filter P → x∈xs.filter Q0++xs.filter Q1 := by
    intro x hx
    have hxdata : x∈xs ∧ Znth x seg 0=block := by
      rcases List.mem_cons.mp hx with he|hm
      · subst x; exact ⟨hin,rfl⟩
      · have hm := List.mem_filter.mp hm
        refine ⟨hm.1,?_⟩
        have ht := hm.2
        simp only [P,Bool.and_eq_true,decide_eq_true_eq] at ht
        exact ht.2
    have hxr := edit_zrange_In__build_s2_segments_counts n x hxdata.1
    have hstart := hg.2 x hxr
    rw [hxdata.2] at hstart
    have hopen := edit_block_startb_true__greedy_common_and_mismatch_steps t x block hstart
    rcases hs.2 x hxr with hz|ho
    · apply List.mem_append.mpr; left
      apply List.mem_filter.mpr
      exact ⟨hxdata.1,by simp [Q0,hxr.2,hopen,edit_bit_atb,hz]⟩
    · apply List.mem_append.mpr; right
      apply List.mem_filter.mpr
      exact ⟨hxdata.1,by simp [Q1,hxr.2,hopen,edit_bit_atb,ho]⟩
  have hlen := nodup_subset_length (i::xs.filter P) (xs.filter Q0++xs.filter Q1) hnodup hsub
  simp only [List.length_cons,List.length_append,Int.ofNat_eq_coe] at hlen ⊢
  omega

theorem edit_greedy_prefix_state_current_availability__greedy_common_and_mismatch_steps
    (s1 s2 t1 t2 : List Int) (n i ans : Int) (seg1 seg2 cnt10 cnt11 cnt20 cnt21 : List Int)
    (hs : EditGreedyPrefixState s1 s2 t1 t2 n i ans seg1 seg2 cnt10 cnt11 cnt20 cnt21) :
    EditGreedyCurrentAvailability n i seg1 seg2 cnt10 cnt11 cnt20 cnt21 := by
  intro hi
  obtain ⟨full10,full11,full20,full21,hb1,hb2,hsc,hr,hcon⟩ := hs.2.2
  have hg1 := hb1.2.2.2.1
  have hg2 := hb2.2.2.2.1
  have ha : 0≤Znth i seg1 0 ∧ Znth i seg1 0<n := by have := (hg1.2 i hi).1; omega
  have hb : 0≤Znth i seg2 0 ∧ Znth i seg2 0<n := by have := (hg2.2 i hi).1; omega
  have hlt1 := edit_count_positions_prefix_lt_full_counts_current__greedy_common_and_mismatch_steps s1 t1 n seg1 full10 full11 i hb1 hi
  have hlt2 := edit_count_positions_prefix_lt_full_counts_current__greedy_common_and_mismatch_steps s2 t2 n seg2 full20 full21 i hb2 hi
  have hr1 := hr.1 (Znth i seg1 0) (by simpa only [hg1.1] using ha)
  have hr2 := hr.2 (Znth i seg2 0) (by simpa only [hg2.1] using hb)
  exact ⟨ha,hb,by omega,by omega⟩

theorem edit_count_positions_in_seg_prefix_zero__greedy_common_and_mismatch_steps (seg : List Int) (block : Int) :
    edit_count_positions_in_seg_prefix seg 0 block=0 := by
  unfold edit_count_positions_in_seg_prefix
  have he : (edit_zrange (Zlength seg)).filter (fun idx => decide (idx<0) && decide (Znth idx seg 0=block))=[] := by
    apply edit_filter_all_false__build_s2_segments_counts
    intro idx hi
    have hr := edit_zrange_In__build_s2_segments_counts _ idx hi
    simp [show ¬idx<0 by omega]
  rw [he]
  rfl

private theorem positions_step (seg : List Int) (i block : Int) (hi : 0≤i ∧ i<Zlength seg) :
    edit_count_positions_in_seg_prefix seg (i+1) block=edit_count_positions_in_seg_prefix seg i block+
      (if Znth i seg 0=block then 1 else 0) := by
  have h := filter_limit_succ_once__build_s1_segments_counts (edit_zrange (Zlength seg)) i
    (fun idx => decide (Znth idx seg 0=block)) (edit_zrange_NoDup__build_s1_segments_counts _)
    (edit_zrange_in__greedy_common_and_mismatch_steps _ i hi) (by intros;omega)
  unfold edit_count_positions_in_seg_prefix
  rw [h]
  simp only [Int.ofNat_eq_coe,Int.natCast_add]
  by_cases he : Znth i seg 0=block <;> simp [he]

theorem edit_count_positions_step_same__greedy_common_and_mismatch_steps (seg : List Int) (i block : Int)
    (hi : 0≤i ∧ i<Zlength seg) (hb : block=Znth i seg 0) :
    edit_count_positions_in_seg_prefix seg (i+1) block=edit_count_positions_in_seg_prefix seg i block+1 := by
  rw [positions_step seg i block hi,if_pos hb.symm]

theorem edit_count_positions_step_diff__greedy_common_and_mismatch_steps (seg : List Int) (i block : Int)
    (hi : 0≤i ∧ i<Zlength seg) (hb : Znth i seg 0≠block) :
    edit_count_positions_in_seg_prefix seg (i+1) block=edit_count_positions_in_seg_prefix seg i block := by
  rw [positions_step seg i block hi,if_neg hb,Int.add_zero]

theorem edit_remaining_totals_decr_left__greedy_common_and_mismatch_steps
    (seg : List Int) (i : Int) (full0 full1 cnt0 cnt1 : List Int) (idx : Int)
    (hi : 0≤i ∧ i<Zlength seg) (he : idx=Znth i seg 0) (hidx : 0≤idx ∧ idx<Zlength seg)
    (hlen : Zlength cnt0=Zlength seg)
    (hr : ∀ block, (0≤block ∧ block<Zlength seg) → Znth block cnt0 0+Znth block cnt1 0=
      Znth block full0 0+Znth block full1 0-edit_count_positions_in_seg_prefix seg i block) :
    ∀ block, (0≤block ∧ block<Zlength seg) →
      Znth block (replace_Znth idx (Znth idx cnt0 0-1) cnt0) 0+Znth block cnt1 0=
        Znth block full0 0+Znth block full1 0-edit_count_positions_in_seg_prefix seg (i+1) block := by
  intro block hb
  rw [replace_read cnt0 idx block _ (by simpa only [hlen] using hidx) (by simpa only [hlen] using hb),positions_step seg i block hi]
  have h := hr block hb
  by_cases hx : block=idx
  · rcases hx with rfl; simp only [ite_true,if_pos he.symm]; omega
  · rw [if_neg hx,if_neg (by omega)]
    omega

theorem edit_remaining_totals_decr_right__greedy_common_and_mismatch_steps
    (seg : List Int) (i : Int) (full0 full1 cnt0 cnt1 : List Int) (idx : Int)
    (hi : 0≤i ∧ i<Zlength seg) (he : idx=Znth i seg 0) (hidx : 0≤idx ∧ idx<Zlength seg)
    (hlen : Zlength cnt1=Zlength seg)
    (hr : ∀ block, (0≤block ∧ block<Zlength seg) → Znth block cnt0 0+Znth block cnt1 0=
      Znth block full0 0+Znth block full1 0-edit_count_positions_in_seg_prefix seg i block) :
    ∀ block, (0≤block ∧ block<Zlength seg) →
      Znth block cnt0 0+Znth block (replace_Znth idx (Znth idx cnt1 0-1) cnt1) 0=
        Znth block full0 0+Znth block full1 0-edit_count_positions_in_seg_prefix seg (i+1) block := by
  intro block hb
  rw [replace_read cnt1 idx block _ (by simpa only [hlen] using hidx) (by simpa only [hlen] using hb),positions_step seg i block hi]
  have h := hr block hb
  by_cases hx : block=idx
  · rcases hx with rfl; simp only [ite_true,if_pos he.symm]; omega
  · rw [if_neg hx,if_neg (by omega)]
    omega

theorem edit_count_bounds_replace_decr__greedy_common_and_mismatch_steps (n : Int) (cnt : List Int) (idx : Int)
    (hb : EditCountBounds n cnt) (hi : 0≤idx ∧ idx<n) (hp : 0<Znth idx cnt 0) :
    EditCountBounds n (replace_Znth idx (Znth idx cnt 0-1) cnt) := by
  apply bounds_update n cnt idx _ hb hi
  have := hb.2 idx hi
  omega

theorem edit_greedy_prefix_state_start__greedy_common_and_mismatch_steps
    (s1 s2 t1 t2 : List Int) (n : Int) (seg1 seg2 cnt10 cnt11 cnt20 cnt21 : List Int)
    (hb1 : EditBuildState s1 t1 n n seg1 cnt10 cnt11) (hb2 : EditBuildState s2 t2 n n seg2 cnt20 cnt21)
    (hsc : EditScratchCountsBound n cnt10 cnt11 cnt20 cnt21) :
    EditGreedyPrefixState s1 s2 t1 t2 n 0 0 seg1 seg2 cnt10 cnt11 cnt20 cnt21 := by
  refine ⟨by have := hb1.1;omega,by omega,cnt10,cnt11,cnt20,cnt21,hb1,hb2,hsc,?_,?_⟩
  · constructor <;> intros <;> simp only [edit_count_positions_in_seg_prefix_zero__greedy_common_and_mismatch_steps,Int.sub_zero]
  · exact EditGreedyConsumedPrefix_start seg1 seg2 cnt10 cnt11 cnt20 cnt21

theorem edit_greedy_prefix_state_read_bounds__greedy_common_and_mismatch_steps
    (s1 s2 t1 t2 : List Int) (n i ans : Int) (seg1 seg2 cnt10 cnt11 cnt20 cnt21 : List Int)
    (hs : EditGreedyPrefixState s1 s2 t1 t2 n i ans seg1 seg2 cnt10 cnt11 cnt20 cnt21) (hi : 0≤i ∧ i<n) :
    (0≤Znth i seg1 0 ∧ Znth i seg1 0<n) ∧ (0≤Znth i seg2 0 ∧ Znth i seg2 0<n) ∧
    (0≤Znth (Znth i seg1 0) cnt10 0 ∧ Znth (Znth i seg1 0) cnt10 0≤n) ∧
    (0≤Znth (Znth i seg1 0) cnt11 0 ∧ Znth (Znth i seg1 0) cnt11 0≤n) ∧
    (0≤Znth (Znth i seg2 0) cnt20 0 ∧ Znth (Znth i seg2 0) cnt20 0≤n) ∧
    (0≤Znth (Znth i seg2 0) cnt21 0 ∧ Znth (Znth i seg2 0) cnt21 0≤n) := by
  have hav := edit_greedy_prefix_state_current_availability__greedy_common_and_mismatch_steps s1 s2 t1 t2 n i ans seg1 seg2 cnt10 cnt11 cnt20 cnt21 hs hi
  obtain ⟨_,_,_,_,_,_,hsc,_⟩ := hs.2.2
  exact ⟨hav.1,hav.2.1,hsc.1.2 _ hav.1,hsc.2.1.2 _ hav.1,hsc.2.2.1.2 _ hav.2.1,hsc.2.2.2.2 _ hav.2.1⟩

theorem edit_greedy_common_zero_step__greedy_common_and_mismatch_steps
    (s1 s2 t1 t2 : List Int) (n i ans : Int) (seg1 seg2 cnt10 cnt11 cnt20 cnt21 : List Int) (a b : Int)
    (hs : EditGreedyPrefixState s1 s2 t1 t2 n i ans seg1 seg2 cnt10 cnt11 cnt20 cnt21)
    (hi : 0≤i ∧ i<n) (ha : a=Znth i seg1 0) (hb : b=Znth i seg2 0)
    (hpa : 0<Znth a cnt10 0) (hpb : 0<Znth b cnt20 0) :
    EditGreedyPrefixState s1 s2 t1 t2 n (i+1) (ans+1) seg1 seg2 (replace_Znth a (Znth a cnt10 0-1) cnt10) cnt11 (replace_Znth b (Znth b cnt20 0-1) cnt20) cnt21 := by
  have hrange := edit_greedy_prefix_state_read_bounds__greedy_common_and_mismatch_steps s1 s2 t1 t2 n i ans seg1 seg2 cnt10 cnt11 cnt20 cnt21 hs hi
  have haRange : 0≤a ∧ a<n := by simpa only [ha] using hrange.1
  have hbRange : 0≤b ∧ b<n := by simpa only [hb] using hrange.2.1
  obtain ⟨hib,hans,full10,full11,full20,full21,hb1,hb2,hsc,hr,hcon⟩ := hs
  have hlen1 := hb1.2.2.2.1.1
  have hlen2 := hb2.2.2.2.1.1
  have hi1 : 0≤i ∧ i<Zlength seg1 := by simpa only [hlen1] using hi
  have hi2 : 0≤i ∧ i<Zlength seg2 := by simpa only [hlen2] using hi
  have hlen : Zlength seg2=Zlength seg1 := by omega
  refine ⟨by omega,by omega,full10,full11,full20,full21,hb1,hb2,?_,?_,?_⟩
  · exact ⟨edit_count_bounds_replace_decr__greedy_common_and_mismatch_steps n cnt10 a hsc.1 haRange hpa, hsc.2.1, edit_count_bounds_replace_decr__greedy_common_and_mismatch_steps n cnt20 b hsc.2.2.1 hbRange hpb, hsc.2.2.2⟩
  · constructor
    · exact edit_remaining_totals_decr_left__greedy_common_and_mismatch_steps seg1 i full10 full11 cnt10 cnt11 a
        hi1 ha (by simpa only [hlen1] using haRange) (by rw [hsc.1.1,hlen1]) hr.1
    · exact edit_remaining_totals_decr_left__greedy_common_and_mismatch_steps seg2 i full20 full21 cnt20 cnt21 b
        hi2 hb (by simpa only [hlen2] using hbRange) (by rw [hsc.2.2.1.1,hlen2]) hr.2
  · exact EditGreedyConsumedPrefix_common_zero seg1 seg2 full10 full11 full20 full21 i ans cnt10 cnt11 cnt20 cnt21 a b
      hi1 hlen ha hb  hpa hpb hcon

theorem edit_greedy_common_one_step__greedy_common_and_mismatch_steps
    (s1 s2 t1 t2 : List Int) (n i ans : Int) (seg1 seg2 cnt10 cnt11 cnt20 cnt21 : List Int) (a b : Int)
    (hs : EditGreedyPrefixState s1 s2 t1 t2 n i ans seg1 seg2 cnt10 cnt11 cnt20 cnt21)
    (hi : 0≤i ∧ i<n) (ha : a=Znth i seg1 0) (hb : b=Znth i seg2 0)
    (hn0 : ¬(0<Znth a cnt10 0 ∧ 0<Znth b cnt20 0))
    (hpa : 0<Znth a cnt11 0) (hpb : 0<Znth b cnt21 0) :
    EditGreedyPrefixState s1 s2 t1 t2 n (i+1) (ans+1) seg1 seg2 cnt10 (replace_Znth a (Znth a cnt11 0-1) cnt11) cnt20 (replace_Znth b (Znth b cnt21 0-1) cnt21) := by
  have hrange := edit_greedy_prefix_state_read_bounds__greedy_common_and_mismatch_steps s1 s2 t1 t2 n i ans seg1 seg2 cnt10 cnt11 cnt20 cnt21 hs hi
  have haRange : 0≤a ∧ a<n := by simpa only [ha] using hrange.1
  have hbRange : 0≤b ∧ b<n := by simpa only [hb] using hrange.2.1
  obtain ⟨hib,hans,full10,full11,full20,full21,hb1,hb2,hsc,hr,hcon⟩ := hs
  have hlen1 := hb1.2.2.2.1.1
  have hlen2 := hb2.2.2.2.1.1
  have hi1 : 0≤i ∧ i<Zlength seg1 := by simpa only [hlen1] using hi
  have hi2 : 0≤i ∧ i<Zlength seg2 := by simpa only [hlen2] using hi
  have hlen : Zlength seg2=Zlength seg1 := by omega
  refine ⟨by omega,by omega,full10,full11,full20,full21,hb1,hb2,?_,?_,?_⟩
  · exact ⟨hsc.1, edit_count_bounds_replace_decr__greedy_common_and_mismatch_steps n cnt11 a hsc.2.1 haRange hpa, hsc.2.2.1, edit_count_bounds_replace_decr__greedy_common_and_mismatch_steps n cnt21 b hsc.2.2.2 hbRange hpb⟩
  · constructor
    · exact edit_remaining_totals_decr_right__greedy_common_and_mismatch_steps seg1 i full10 full11 cnt10 cnt11 a
        hi1 ha (by simpa only [hlen1] using haRange) (by rw [hsc.2.1.1,hlen1]) hr.1
    · exact edit_remaining_totals_decr_right__greedy_common_and_mismatch_steps seg2 i full20 full21 cnt20 cnt21 b
        hi2 hb (by simpa only [hlen2] using hbRange) (by rw [hsc.2.2.2.1,hlen2]) hr.2
  · exact EditGreedyConsumedPrefix_common_one seg1 seg2 full10 full11 full20 full21 i ans cnt10 cnt11 cnt20 cnt21 a b
      hi1 hlen ha hb hn0 hpa hpb hcon

theorem edit_greedy_s1_zero_s2_one_step__greedy_common_and_mismatch_steps
    (s1 s2 t1 t2 : List Int) (n i ans : Int) (seg1 seg2 cnt10 cnt11 cnt20 cnt21 : List Int) (a b : Int)
    (hs : EditGreedyPrefixState s1 s2 t1 t2 n i ans seg1 seg2 cnt10 cnt11 cnt20 cnt21)
    (hi : 0≤i ∧ i<n) (ha : a=Znth i seg1 0) (hb : b=Znth i seg2 0)
    (hn0 : ¬(0<Znth a cnt10 0 ∧ 0<Znth b cnt20 0))
    (hn1 : ¬(0<Znth a cnt11 0 ∧ 0<Znth b cnt21 0))
    (hpa : 0<Znth a cnt10 0) (hpb : 0<Znth b cnt21 0) :
    EditGreedyPrefixState s1 s2 t1 t2 n (i+1) ans seg1 seg2 (replace_Znth a (Znth a cnt10 0-1) cnt10) cnt11 cnt20 (replace_Znth b (Znth b cnt21 0-1) cnt21) := by
  have hrange := edit_greedy_prefix_state_read_bounds__greedy_common_and_mismatch_steps s1 s2 t1 t2 n i ans seg1 seg2 cnt10 cnt11 cnt20 cnt21 hs hi
  have haRange : 0≤a ∧ a<n := by simpa only [ha] using hrange.1
  have hbRange : 0≤b ∧ b<n := by simpa only [hb] using hrange.2.1
  obtain ⟨hib,hans,full10,full11,full20,full21,hb1,hb2,hsc,hr,hcon⟩ := hs
  have hlen1 := hb1.2.2.2.1.1
  have hlen2 := hb2.2.2.2.1.1
  have hi1 : 0≤i ∧ i<Zlength seg1 := by simpa only [hlen1] using hi
  have hi2 : 0≤i ∧ i<Zlength seg2 := by simpa only [hlen2] using hi
  have hlen : Zlength seg2=Zlength seg1 := by omega
  refine ⟨by omega,by omega,full10,full11,full20,full21,hb1,hb2,?_,?_,?_⟩
  · exact ⟨edit_count_bounds_replace_decr__greedy_common_and_mismatch_steps n cnt10 a hsc.1 haRange hpa, hsc.2.1, hsc.2.2.1, edit_count_bounds_replace_decr__greedy_common_and_mismatch_steps n cnt21 b hsc.2.2.2 hbRange hpb⟩
  · constructor
    · exact edit_remaining_totals_decr_left__greedy_common_and_mismatch_steps seg1 i full10 full11 cnt10 cnt11 a
        hi1 ha (by simpa only [hlen1] using haRange) (by rw [hsc.1.1,hlen1]) hr.1
    · exact edit_remaining_totals_decr_right__greedy_common_and_mismatch_steps seg2 i full20 full21 cnt20 cnt21 b
        hi2 hb (by simpa only [hlen2] using hbRange) (by rw [hsc.2.2.2.1,hlen2]) hr.2
  · exact EditGreedyConsumedPrefix_s1_zero_s2_one seg1 seg2 full10 full11 full20 full21 i ans cnt10 cnt11 cnt20 cnt21 a b
      hi1 hlen ha hb hn0 hn1 hpa hpb hcon

theorem edit_greedy_s1_one_s2_zero_step__greedy_common_and_mismatch_steps
    (s1 s2 t1 t2 : List Int) (n i ans : Int) (seg1 seg2 cnt10 cnt11 cnt20 cnt21 : List Int) (a b : Int)
    (hs : EditGreedyPrefixState s1 s2 t1 t2 n i ans seg1 seg2 cnt10 cnt11 cnt20 cnt21)
    (hi : 0≤i ∧ i<n) (ha : a=Znth i seg1 0) (hb : b=Znth i seg2 0)
    (hn0 : ¬(0<Znth a cnt10 0 ∧ 0<Znth b cnt20 0))
    (hn1 : ¬(0<Znth a cnt11 0 ∧ 0<Znth b cnt21 0))
    (hna : ¬(0<Znth a cnt10 0))
    (hpa : 0<Znth a cnt11 0) (hpb : 0<Znth b cnt20 0) :
    EditGreedyPrefixState s1 s2 t1 t2 n (i+1) ans seg1 seg2 cnt10 (replace_Znth a (Znth a cnt11 0-1) cnt11) (replace_Znth b (Znth b cnt20 0-1) cnt20) cnt21 := by
  have hrange := edit_greedy_prefix_state_read_bounds__greedy_common_and_mismatch_steps s1 s2 t1 t2 n i ans seg1 seg2 cnt10 cnt11 cnt20 cnt21 hs hi
  have haRange : 0≤a ∧ a<n := by simpa only [ha] using hrange.1
  have hbRange : 0≤b ∧ b<n := by simpa only [hb] using hrange.2.1
  obtain ⟨hib,hans,full10,full11,full20,full21,hb1,hb2,hsc,hr,hcon⟩ := hs
  have hlen1 := hb1.2.2.2.1.1
  have hlen2 := hb2.2.2.2.1.1
  have hi1 : 0≤i ∧ i<Zlength seg1 := by simpa only [hlen1] using hi
  have hi2 : 0≤i ∧ i<Zlength seg2 := by simpa only [hlen2] using hi
  have hlen : Zlength seg2=Zlength seg1 := by omega
  refine ⟨by omega,by omega,full10,full11,full20,full21,hb1,hb2,?_,?_,?_⟩
  · exact ⟨hsc.1, edit_count_bounds_replace_decr__greedy_common_and_mismatch_steps n cnt11 a hsc.2.1 haRange hpa, edit_count_bounds_replace_decr__greedy_common_and_mismatch_steps n cnt20 b hsc.2.2.1 hbRange hpb, hsc.2.2.2⟩
  · constructor
    · exact edit_remaining_totals_decr_right__greedy_common_and_mismatch_steps seg1 i full10 full11 cnt10 cnt11 a
        hi1 ha (by simpa only [hlen1] using haRange) (by rw [hsc.2.1.1,hlen1]) hr.1
    · exact edit_remaining_totals_decr_left__greedy_common_and_mismatch_steps seg2 i full20 full21 cnt20 cnt21 b
        hi2 hb (by simpa only [hlen2] using hbRange) (by rw [hsc.2.2.1.1,hlen2]) hr.2
  · exact EditGreedyConsumedPrefix_s1_one_s2_zero seg1 seg2 full10 full11 full20 full21 i ans cnt10 cnt11 cnt20 cnt21 a b
      hi1 hlen ha hb hn0 hn1 hna hpa hpb hcon

end SimpleC.EE.LLM_bench.Algorithms.edit_strings.edit_strings_lib

namespace SimpleC.EE.LLM_bench.Algorithms.edit_strings
export edit_strings_lib (edit_zrange edit_zrange_between EditBinaryList edit_edge_open edit_edge_openb edit_all_edges_openb EditBlockStart edit_block_startb edit_bit_atb edit_count_bit_in_block_prefix EditZeroPrefix EditZeroFull EditSegmentPrefix EditCountsForPrefix EditBuildState EditCountBounds EditScratchCountsBound edit_count_positions_in_seg_prefix EditGreedyRemainingTotals EditReachableString edit_match_count EditStringsFeasibleMatchCount EditStringsMatchUpperBound EditStringsMaximum EditGreedyConsumedPrefix EditGreedyFinalOptimality EditGreedyPrefixState EditGreedyCurrentAvailability EditGreedyCompletedMaximumFacts EditGreedyCompletedStateFacts)
end SimpleC.EE.LLM_bench.Algorithms.edit_strings
