import Algorithms.huffman_encoding.lean.groundtruth.huffman_encoding_goal
import Algorithms.huffman_encoding.lean.groundtruth.huffman_encoding_proof_auto
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import ListLib.General.Length

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace Algorithms.huffman_encoding.lean.groundtruth.huffman_encoding_proof_manual

open Algorithms.huffman_encoding.lean

open AUXLib


open MaxMinLib

def HuffmanTreeHeight : HuffmanTree → Int
  | .HuffmanLeaf _ => 0
  | .HuffmanNode left_tree right_tree => max (HuffmanTreeHeight left_tree) (HuffmanTreeHeight right_tree) + 1

def HuffmanLeafDepths : HuffmanTree → List Int
  | .HuffmanLeaf _ => [0]
  | .HuffmanNode left_tree right_tree =>
      (HuffmanLeafDepths left_tree).map (fun depth => depth + 1) ++ (HuffmanLeafDepths right_tree).map (fun depth => depth + 1)

inductive HuffmanTreeContext : Type
  | HuffmanRootContext : HuffmanTreeContext
  | HuffmanLeftContext : HuffmanTreeContext → HuffmanTree → HuffmanTreeContext
  | HuffmanRightContext : HuffmanTree → HuffmanTreeContext → HuffmanTreeContext
export HuffmanTreeContext (HuffmanRootContext HuffmanLeftContext HuffmanRightContext)

def HuffmanPlug (context : HuffmanTreeContext) (hole : HuffmanTree) : HuffmanTree :=
  match context with
  | .HuffmanRootContext => hole
  | .HuffmanLeftContext inner right_tree => .HuffmanNode (HuffmanPlug inner hole) right_tree
  | .HuffmanRightContext left_tree inner => .HuffmanNode left_tree (HuffmanPlug inner hole)

def HuffmanContextDepth : HuffmanTreeContext → Int
  | .HuffmanRootContext => 0
  | .HuffmanLeftContext inner _ => HuffmanContextDepth inner + 1
  | .HuffmanRightContext _ inner => HuffmanContextDepth inner + 1

def HuffmanContextLeaves (context : HuffmanTreeContext) (hole_leaves : List Int) : List Int :=
  match context with
  | .HuffmanRootContext => hole_leaves
  | .HuffmanLeftContext inner right_tree => HuffmanContextLeaves inner hole_leaves ++ HuffmanLeaves right_tree
  | .HuffmanRightContext left_tree inner => HuffmanLeaves left_tree ++ HuffmanContextLeaves inner hole_leaves

def HuffmanContextWeight (context : HuffmanTreeContext) (hole_weight : Int) : Int :=
  match context with
  | .HuffmanRootContext => hole_weight
  | .HuffmanLeftContext inner right_tree => HuffmanContextWeight inner hole_weight + HuffmanTreeWeight right_tree
  | .HuffmanRightContext left_tree inner => HuffmanTreeWeight left_tree + HuffmanContextWeight inner hole_weight

def HuffmanContextPathLength (context : HuffmanTreeContext) (hole_weight hole_path_length : Int) : Int :=
  match context with
  | .HuffmanRootContext => hole_path_length
  | .HuffmanLeftContext inner right_tree =>
      HuffmanContextPathLength inner hole_weight hole_path_length + HuffmanWeightedPathLength right_tree +
        HuffmanContextWeight inner hole_weight + HuffmanTreeWeight right_tree
  | .HuffmanRightContext left_tree inner =>
      HuffmanWeightedPathLength left_tree + HuffmanContextPathLength inner hole_weight hole_path_length +
        HuffmanTreeWeight left_tree + HuffmanContextWeight inner hole_weight

def HuffmanWeightedDepths (weights depths : List Int) : Int :=
  sum ((weights.zip depths).map (fun pair : Int × Int => pair.1 * pair.2))

def HuffmanDeepestSibling (tree : HuffmanTree) (context : HuffmanTreeContext) (left_weight right_weight : Int) : Prop :=
  tree = HuffmanPlug context (.HuffmanNode (.HuffmanLeaf left_weight) (.HuffmanLeaf right_weight)) ∧
    HuffmanContextDepth context + 1 = HuffmanTreeHeight tree

def HuffmanContractSibling (context : HuffmanTreeContext) (left_weight right_weight : Int) : HuffmanTree :=
  HuffmanPlug context (.HuffmanLeaf (left_weight + right_weight))

private theorem forall_append {A : Type} (P : A → Prop) (l r : List A) :
    Forall P (l++r) ↔ Forall P l ∧ Forall P r := by
  simp only [Forall.iff_forall_mem, List.mem_append]
  constructor
  · intro h; exact ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩
  · rintro ⟨hl, hr⟩ x (hx | hx); exact hl x hx; exact hr x hx

private theorem forall_nth {A : Type} {P : A → Prop} (l : List A) (d : A) (i : Int)
    (hp : Forall P l) (hi : 0 ≤ i ∧ i < Zlength l) : P (Znth i l d) := by
  induction hp generalizing i with
  | nil => simp [Zlength] at hi; omega
  | @cons a l ha ht ih =>
    rw [Zlength_cons] at hi
    by_cases he : i = 0
    · subst i; simpa only [Znth0_cons] using ha
    · rw [Znth_cons d i a l (by omega)]
      exact ih (i-1) ⟨by omega, by omega⟩

private theorem nth_mem {A : Type} (l : List A) (d : A) (i : Int)
    (hi : 0 ≤ i ∧ i < Zlength l) : Znth i l d ∈ l :=
  forall_nth l d i (Forall.iff_forall_mem.mpr (by intro x hx; exact hx)) hi

private theorem mem_nth {A : Type} (l : List A) (d : A) (x : A) (hx : x ∈ l) :
    ∃ i : Int, (0 ≤ i ∧ i < Zlength l) ∧ Znth i l d = x := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨0, ⟨by omega, by rw [Zlength_cons]; have := Zlength_nonneg l; omega⟩, rfl⟩
    · rcases ih hx with ⟨i, hi, he⟩
      refine ⟨i+1, ⟨by omega, by rw [Zlength_cons]; omega⟩, ?_⟩
      rw [Znth_cons d (i+1) a l (by omega)]
      simpa only [show i+1-1 = i by omega] using he

private theorem bounded_forall (weights : List Int) (hb : HuffmanInputBounded weights) :
    Forall (fun x => 1 ≤ x ∧ x ≤ 1000) weights := by
  apply Forall.iff_forall_mem.mpr
  intro x hx
  rcases mem_nth weights 0 x hx with ⟨i, hi, he⟩
  rw [← he]; exact hb i hi

private theorem weighted_cons (x d : Int) (xs ds : List Int) :
    HuffmanWeightedDepths (x::xs) (d::ds) = x*d+HuffmanWeightedDepths xs ds := rfl

theorem huffman_tree_weight_leaves (tree : HuffmanTree) : HuffmanTreeWeight tree = sum (HuffmanLeaves tree) := by
  induction tree with
  | HuffmanLeaf w => simp [HuffmanTreeWeight, HuffmanLeaves, sum]
  | HuffmanNode l r ihl ihr => simp only [HuffmanTreeWeight, HuffmanLeaves, sum_app, ihl, ihr]

theorem huffman_weighted_depths_app (w1 w2 d1 d2 : List Int) (hl : w1.length = d1.length) :
    HuffmanWeightedDepths (w1++w2) (d1++d2) = HuffmanWeightedDepths w1 d1+HuffmanWeightedDepths w2 d2 := by
  induction w1 generalizing d1 with
  | nil => cases d1 with
    | nil => simp [HuffmanWeightedDepths, sum]
    | cons a l => simp at hl
  | cons w ws ih =>
    cases d1 with
    | nil => simp at hl
    | cons d ds =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      change w*d+HuffmanWeightedDepths (ws++w2) (ds++d2) = (w*d+HuffmanWeightedDepths ws ds)+_
      rw [ih ds hl]; omega

theorem huffman_weighted_depths_lift (weights depths : List Int) (hl : weights.length = depths.length) :
    HuffmanWeightedDepths weights (depths.map (fun d => d+1)) = HuffmanWeightedDepths weights depths+sum weights := by
  induction weights generalizing depths with
  | nil => cases depths with
    | nil => rfl
    | cons a l => simp at hl
  | cons w ws ih =>
    cases depths with
    | nil => simp at hl
    | cons d ds =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      change w*(d+1)+HuffmanWeightedDepths ws (ds.map (fun d => d+1)) = (w*d+HuffmanWeightedDepths ws ds)+(w+sum ws)
      rw [ih ds hl]; ring

theorem huffman_leaf_depth_profile (tree : HuffmanTree) :
    (HuffmanLeaves tree).length = (HuffmanLeafDepths tree).length ∧
      HuffmanWeightedDepths (HuffmanLeaves tree) (HuffmanLeafDepths tree) = HuffmanWeightedPathLength tree := by
  induction tree with
  | HuffmanLeaf w => exact ⟨rfl, by simp [HuffmanLeaves, HuffmanLeafDepths, HuffmanWeightedDepths, HuffmanWeightedPathLength, sum]⟩
  | HuffmanNode l r ihl ihr =>
    constructor
    · simp only [HuffmanLeaves, HuffmanLeafDepths, List.length_append, List.length_map, ihl.1, ihr.1]
    · simp only [HuffmanLeaves, HuffmanLeafDepths]
      rw [huffman_weighted_depths_app _ _ _ _ (by simpa using ihl.1),
        huffman_weighted_depths_lift _ _ ihl.1, huffman_weighted_depths_lift _ _ ihr.1,
        ihl.2, ihr.2, ← huffman_tree_weight_leaves, ← huffman_tree_weight_leaves]
      simp only [HuffmanWeightedPathLength]; ring

theorem huffman_leaf_depths_bounded (tree : HuffmanTree) :
    Forall (fun d => d ≤ HuffmanTreeHeight tree) (HuffmanLeafDepths tree) := by
  induction tree with
  | HuffmanLeaf w => exact .cons (by simp [HuffmanTreeHeight]) .nil
  | HuffmanNode l r ihl ihr =>
    apply Forall.iff_forall_mem.mpr
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · rcases List.mem_map.mp hd with ⟨old, hin, rfl⟩
      have h := ihl.mem hin
      have hmax := le_max_left (HuffmanTreeHeight l) (HuffmanTreeHeight r)
      change old+1 ≤ max _ _+1; omega
    · rcases List.mem_map.mp hd with ⟨old, hin, rfl⟩
      have h := ihr.mem hin
      have hmax := le_max_right (HuffmanTreeHeight l) (HuffmanTreeHeight r)
      change old+1 ≤ max _ _+1; omega

theorem huffman_tree_height_nonnegative (tree : HuffmanTree) : 0 ≤ HuffmanTreeHeight tree := by
  induction tree with
  | HuffmanLeaf w => exact le_refl _
  | HuffmanNode l r ihl ihr =>
    have hm := le_max_left (HuffmanTreeHeight l) (HuffmanTreeHeight r)
    change 0 ≤ max _ _+1; omega

theorem huffman_plug_leaves (context : HuffmanTreeContext) (hole : HuffmanTree) :
    HuffmanLeaves (HuffmanPlug context hole) = HuffmanContextLeaves context (HuffmanLeaves hole) := by
  induction context <;> simp_all [HuffmanPlug, HuffmanLeaves, HuffmanContextLeaves]

theorem huffman_plug_weight (context : HuffmanTreeContext) (hole : HuffmanTree) :
    HuffmanTreeWeight (HuffmanPlug context hole) = HuffmanContextWeight context (HuffmanTreeWeight hole) := by
  induction context <;> simp_all [HuffmanPlug, HuffmanTreeWeight, HuffmanContextWeight]

theorem huffman_plug_path_length (context : HuffmanTreeContext) (hole : HuffmanTree) :
    HuffmanWeightedPathLength (HuffmanPlug context hole) =
      HuffmanContextPathLength context (HuffmanTreeWeight hole) (HuffmanWeightedPathLength hole) := by
  induction context <;> simp_all [HuffmanPlug, HuffmanWeightedPathLength, HuffmanContextPathLength, huffman_plug_weight]

theorem huffman_context_leaves_permutation (context : HuffmanTreeContext) (l r : List Int)
    (hp : l.Perm r) : (HuffmanContextLeaves context l).Perm (HuffmanContextLeaves context r) := by
  induction context with
  | HuffmanRootContext => exact hp
  | HuffmanLeftContext inner tree ih => exact ih.append (List.Perm.refl _)
  | HuffmanRightContext tree inner ih => exact (List.Perm.refl _).append ih

theorem huffman_plug_leaves_permutation (context : HuffmanTreeContext) (l r : HuffmanTree)
    (hp : (HuffmanLeaves l).Perm (HuffmanLeaves r)) :
    (HuffmanLeaves (HuffmanPlug context l)).Perm (HuffmanLeaves (HuffmanPlug context r)) := by
  rw [huffman_plug_leaves, huffman_plug_leaves]
  exact huffman_context_leaves_permutation context _ _ hp

theorem huffman_context_path_length_shift (context : HuffmanTreeContext) (w cost increment : Int) :
    HuffmanContextPathLength context w (cost+increment) = HuffmanContextPathLength context w cost+increment := by
  induction context <;> simp_all [HuffmanContextPathLength] <;> omega

theorem huffman_deepest_sibling_exists (tree : HuffmanTree)
    (hn : ∃ l r, tree = HuffmanNode l r) :
    ∃ context x y, HuffmanDeepestSibling tree context x y := by
  induction tree with
  | HuffmanLeaf w => rcases hn with ⟨l, r, he⟩; cases he
  | HuffmanNode l r ihl ihr =>
    cases l with
    | HuffmanLeaf x =>
      cases r with
      | HuffmanLeaf y => exact ⟨HuffmanRootContext, x, y, rfl, rfl⟩
      | HuffmanNode rl rr =>
        rcases ihr ⟨rl, rr, rfl⟩ with ⟨ctx, x', y', hs, hd⟩
        refine ⟨HuffmanRightContext (HuffmanLeaf x) ctx, x', y', ?_, ?_⟩
        · change HuffmanNode _ _ = HuffmanNode _ _; rw [← hs]
        · change HuffmanContextDepth ctx+1+1 = max 0 (HuffmanTreeHeight (HuffmanNode rl rr))+1
          rw [hd, max_eq_right (huffman_tree_height_nonnegative _)]
    | HuffmanNode ll lr =>
      by_cases hh : HuffmanTreeHeight r ≤ HuffmanTreeHeight (HuffmanNode ll lr)
      · rcases ihl ⟨ll, lr, rfl⟩ with ⟨ctx, x, y, hs, hd⟩
        refine ⟨HuffmanLeftContext ctx r, x, y, ?_, ?_⟩
        · change HuffmanNode _ _ = HuffmanNode _ _; rw [← hs]
        · change HuffmanContextDepth ctx+1+1 = max (HuffmanTreeHeight (HuffmanNode ll lr)) (HuffmanTreeHeight r)+1
          rw [hd, max_eq_left hh]
      · cases r with
        | HuffmanLeaf y => have := huffman_tree_height_nonnegative (HuffmanNode ll lr); change ¬ 0 ≤ _ at hh; omega
        | HuffmanNode rl rr =>
          rcases ihr ⟨rl, rr, rfl⟩ with ⟨ctx, x, y, hs, hd⟩
          refine ⟨HuffmanRightContext (HuffmanNode ll lr) ctx, x, y, ?_, ?_⟩
          · change HuffmanNode _ _ = HuffmanNode _ _; rw [← hs]
          · change HuffmanContextDepth ctx+1+1 = max (HuffmanTreeHeight (HuffmanNode ll lr)) (HuffmanTreeHeight (HuffmanNode rl rr))+1
            rw [hd, max_eq_right (by omega)]

theorem permutation_two_across_prefix (A : Type) (pre suf : List A) (x y : A) :
    (pre++x::y::suf).Perm (x::y::(pre++suf)) :=
  (List.perm_middle).trans (List.Perm.cons x List.perm_middle)

theorem huffman_context_pair_depths (context : HuffmanTreeContext) (x y : Int) :
    ∃ other_depths, (HuffmanLeafDepths (HuffmanPlug context (HuffmanNode (HuffmanLeaf x) (HuffmanLeaf y)))).Perm
      ((HuffmanContextDepth context+1)::(HuffmanContextDepth context+1)::other_depths) := by
  induction context with
  | HuffmanRootContext => exact ⟨[], List.Perm.refl _⟩
  | HuffmanLeftContext ctx r ih =>
    rcases ih with ⟨ds, hp⟩
    refine ⟨ds.map (fun d => d+1)++(HuffmanLeafDepths r).map (fun d => d+1), ?_⟩
    exact (hp.map (fun d => d+1)).append (List.Perm.refl _)
  | HuffmanRightContext l ctx ih =>
    rcases ih with ⟨ds, hp⟩
    refine ⟨(HuffmanLeafDepths l).map (fun d => d+1)++ds.map (fun d => d+1), ?_⟩
    exact ((List.Perm.refl _).append (hp.map (fun d => d+1))).trans
      (permutation_two_across_prefix Int _ _ _ _)

theorem huffman_deepest_sibling_profile (tree : HuffmanTree) (hn : ∃ l r, tree = HuffmanNode l r) :
    ∃ context x y ds, HuffmanDeepestSibling tree context x y ∧
      (HuffmanLeafDepths tree).Perm (HuffmanTreeHeight tree::HuffmanTreeHeight tree::ds) ∧
      Forall (fun d => d ≤ HuffmanTreeHeight tree) (HuffmanLeafDepths tree) := by
  rcases huffman_deepest_sibling_exists tree hn with ⟨ctx, x, y, hs, hd⟩
  rcases huffman_context_pair_depths ctx x y with ⟨ds, hp⟩
  refine ⟨ctx, x, y, ds, ⟨hs, hd⟩, ?_, huffman_leaf_depths_bounded tree⟩
  rw [← hd, hs]; exact hp

theorem huffman_contract_leaves (context : HuffmanTreeContext) (x y : Int) :
    HuffmanLeaves (HuffmanContractSibling context x y) = HuffmanContextLeaves context [x+y] := by
  exact huffman_plug_leaves context (HuffmanLeaf (x+y))

theorem huffman_expanded_sibling_leaves (context : HuffmanTreeContext) (x y : Int) :
    HuffmanLeaves (HuffmanPlug context (HuffmanNode (HuffmanLeaf x) (HuffmanLeaf y))) =
      HuffmanContextLeaves context [x,y] := huffman_plug_leaves context _

theorem huffman_contract_weight (context : HuffmanTreeContext) (x y : Int) :
    HuffmanTreeWeight (HuffmanPlug context (HuffmanNode (HuffmanLeaf x) (HuffmanLeaf y))) =
      HuffmanTreeWeight (HuffmanContractSibling context x y) := by
  unfold HuffmanContractSibling
  rw [huffman_plug_weight, huffman_plug_weight]; rfl

theorem huffman_contract_path_length (context : HuffmanTreeContext) (x y : Int) :
    HuffmanWeightedPathLength (HuffmanPlug context (HuffmanNode (HuffmanLeaf x) (HuffmanLeaf y))) =
      HuffmanWeightedPathLength (HuffmanContractSibling context x y)+x+y := by
  unfold HuffmanContractSibling
  rw [huffman_plug_path_length, huffman_plug_path_length]
  have hh := huffman_context_path_length_shift context (x+y) 0 (x+y)
  simpa only [HuffmanTreeWeight, HuffmanWeightedPathLength, Int.zero_add, Int.add_assoc] using hh

theorem huffman_deepest_sibling_contraction (tree : HuffmanTree) (context : HuffmanTreeContext) (x y : Int)
    (hs : HuffmanDeepestSibling tree context x y) :
    tree = HuffmanPlug context (HuffmanNode (HuffmanLeaf x) (HuffmanLeaf y)) ∧
    HuffmanLeaves (HuffmanContractSibling context x y) = HuffmanContextLeaves context [x+y] ∧
    HuffmanTreeWeight tree = HuffmanTreeWeight (HuffmanContractSibling context x y) ∧
    HuffmanWeightedPathLength tree = HuffmanWeightedPathLength (HuffmanContractSibling context x y)+x+y := by
  exact ⟨hs.1, huffman_contract_leaves _ _ _, by rw [hs.1]; exact huffman_contract_weight _ _ _,
    by rw [hs.1]; exact huffman_contract_path_length _ _ _⟩

theorem huffman_feasible_tree_exists__copy_initialization (weights : List Int) (hn : weights ≠ []) :
    ∃ tree, HuffmanTreeFeasible weights tree := by
  induction weights with
  | nil => exact False.elim (hn rfl)
  | cons w ws ih =>
    cases ws with
    | nil => exact ⟨HuffmanLeaf w, List.Perm.refl _⟩
    | cons v vs =>
      obtain ⟨t, ht⟩ := ih (by simp)
      exact ⟨HuffmanNode (HuffmanLeaf w) t, ht.cons w⟩

theorem huffman_tree_cost_nonnegative__copy_initialization (tree : HuffmanTree)
    (hp : Forall (fun w => 0 ≤ w) (HuffmanLeaves tree)) :
    0 ≤ HuffmanTreeWeight tree ∧ 0 ≤ HuffmanWeightedPathLength tree := by
  induction tree with
  | HuffmanLeaf w => have := hp.mem (show w ∈ HuffmanLeaves (HuffmanLeaf w) by simp [HuffmanLeaves]); exact ⟨this, le_refl _⟩
  | HuffmanNode l r ihl ihr =>
    obtain ⟨hl, hr⟩ := (forall_append _ _ _).mp hp
    have := ihl hl; have := ihr hr
    dsimp [HuffmanTreeWeight, HuffmanWeightedPathLength]; omega

private theorem input_nonnegative (w : List Int) (hb : HuffmanInputBounded w) : Forall (fun x => 0 ≤ x) w := by
  apply Forall.iff_forall_mem.mpr
  intro x hx
  have := (bounded_forall w hb).mem hx; omega

theorem huffman_optimal_cost_exists__copy_initialization (weights : List Int) (hn : weights ≠ [])
    (hb : HuffmanInputBounded weights) : ∃ answer, HuffmanOptimalCost weights answer := by
  obtain ⟨t, ht⟩ := huffman_feasible_tree_exists__copy_initialization weights hn
  have nonneg (s : HuffmanTree) (hs : HuffmanTreeFeasible weights s) : 0 ≤ HuffmanWeightedPathLength s :=
    (huffman_tree_cost_nonnegative__copy_initialization s ((input_nonnegative weights hb).perm hs)).2
  obtain ⟨answer, ⟨best, hbest, he⟩, ha, hmin⟩ := MaxMinLib.min_n_in_range
    (fun c => ∃ s, HuffmanTreeFeasible weights s ∧ HuffmanWeightedPathLength s = c)
    (HuffmanWeightedPathLength t) (nonneg t ht) ⟨_, ⟨nonneg t ht, le_refl _⟩, t, ht, rfl⟩
  refine ⟨answer, best, ⟨hbest, ?_⟩, he⟩
  intro s hs
  rw [he]
  by_cases hle : HuffmanWeightedPathLength s ≤ HuffmanWeightedPathLength t
  · exact hmin _ ⟨nonneg s hs, hle⟩ ⟨s, hs, rfl⟩
  · omega

theorem huffman_initial_progress__copy_initialization (weights : List Int)
    (hl : 1 ≤ Zlength weights) (hb : HuffmanInputBounded weights) :
    HuffmanProgress weights weights (Zlength weights) 0 := by
  unfold HuffmanProgress
  rw [sublist_self weights _ rfl]
  obtain ⟨answer, ha⟩ := huffman_optimal_cost_exists__copy_initialization weights (by
    intro he; simp [he, Zlength] at hl) hb
  exact ⟨rfl, answer, ha, by simpa using ha⟩

theorem huffman_input_live_bounds__copy_initialization (weights : List Int) (n : Int)
    (hl : Zlength weights = n) (hb : HuffmanInputBounded weights) (k : Int) (hk : 0 ≤ k ∧ k < n) :
    1 ≤ Znth k weights 0 ∧ Znth k weights 0 ≤ 8000 := by
  have := hb k (by omega); omega

theorem huffman_min_scan_init__min_scan_updates (scratch : List Int) : HuffmanMinScan scratch 1 0 := by
  intro k hk
  have he : k = 0 := by omega
  rw [he]

theorem huffman_min_scan_take_new__min_scan_updates (scratch : List Int) (scanned best : Int)
    (hs : HuffmanMinScan scratch scanned best) (hn : Znth scanned scratch 0 < Znth best scratch 0) :
    HuffmanMinScan scratch (scanned+1) scanned := by
  intro k hk
  by_cases h : k < scanned
  · have := hs k ⟨hk.1, h⟩; omega
  · have he : k = scanned := by omega
    rw [he]

theorem huffman_min_scan_keep_old__min_scan_updates (scratch : List Int) (scanned best : Int)
    (hs : HuffmanMinScan scratch scanned best) (hn : Znth best scratch 0 ≤ Znth scanned scratch 0) :
    HuffmanMinScan scratch (scanned+1) best := by
  intro k hk
  by_cases h : k < scanned
  · exact hs k ⟨hk.1, h⟩
  · have he : k = scanned := by omega
    rw [he]; exact hn

private theorem prefix_length {A : Type} (l : List A) (a : Int) (ha : 0 ≤ a ∧ a ≤ Zlength l) :
    Zlength (sublist 0 a l) = a := by
  have h := ListLib.Zlength_sublist 0 a l ⟨le_refl _, ha.1⟩ ha.2
  simpa only [Int.sub_zero] using h

private theorem prefix_nth {A : Type} (l : List A) (d : A) (a k : Int) (hk : 0 ≤ k ∧ k < a) :
    Znth k (sublist 0 a l) d = Znth k l d := by
  simpa only [Int.sub_zero, Int.add_zero] using Znth_sublist d 0 k a l (le_refl _) (by simpa using hk)

theorem replace_last_removal_permutation__removals_bounds (xs : List Int) (selected active : Int)
    (hs : 0 ≤ selected ∧ selected < active) (ha : active ≤ Zlength xs) :
    List.Perm (sublist 0 active xs) (Znth selected xs 0 ::
      sublist 0 (active-1) (replace_Znth selected (Znth (active-1) xs 0) xs)) := by
  induction xs generalizing selected active with
  | nil => simp [Zlength] at ha; omega
  | cons x xs ih =>
    rw [Zlength_cons] at ha
    by_cases hz : selected = 0
    · subst selected
      by_cases ho : active = 1
      · subst active; change List.Perm [x] [x]; rfl
      · rw [sublist_cons1 active x xs (by omega), Znth0_cons]
        change List.Perm (x::sublist 0 (active-1) xs)
          (x::sublist 0 (active-1) (Znth (active-1) (x::xs) 0 :: xs))
        rw [sublist_cons1 (active-1) _ xs (by omega), Znth_cons 0 (active-1) x xs (by omega)]
        have he : active-1-1 = active-2 := by omega
        rw [he]
        have hsplit := sublist_split 0 (active-1) (active-2) xs ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
        rw [hsplit]
        have hsingle := sublist_single 0 (active-2) xs ⟨by omega, by omega⟩
        simp only [show active-2+1 = active-1 by omega] at hsingle
        rw [hsingle]
        exact (List.perm_append_comm).cons x
    · rw [sublist_cons1 active x xs (by omega), Znth_cons 0 selected x xs (by omega),
        replace_Znth_cons selected _ x xs (by omega), sublist_cons1 (active-1) x _ (by omega),
        Znth_cons 0 (active-1) x xs (by omega)]
      exact ((ih (selected-1) (active-1) ⟨by omega, by omega⟩ (by omega)).cons x).trans (List.Perm.swap _ _ _)

theorem replace_last_live_bounds__removals_bounds (xs : List Int) (selected active lower upper : Int)
    (hs : 0 ≤ selected ∧ selected < active) (ha : active ≤ Zlength xs)
    (hb : ∀ k, (0 ≤ k ∧ k < active) → lower ≤ Znth k xs 0 ∧ Znth k xs 0 ≤ upper)
    (k : Int) (hk : 0 ≤ k ∧ k < active-1) :
    lower ≤ Znth k (replace_Znth selected (Znth (active-1) xs 0) xs) 0 ∧
      Znth k (replace_Znth selected (Znth (active-1) xs 0) xs) 0 ≤ upper := by
  by_cases he : k = selected
  · subst k; rw [Znth_replace_Znth_Same 0 xs selected _ ⟨hs.1, by omega⟩]; exact hb _ ⟨by omega, by omega⟩
  · rw [Znth_replace_Znth_Diff 0 xs selected k _ ⟨hs.1, by omega⟩ ⟨hk.1, by omega⟩ (Ne.symm he)]
    exact hb k ⟨hk.1, by omega⟩

theorem huffman_first_held_after_removal__removals_bounds (input xs : List Int) (selected active accumulated : Int)
    (hs : 0 ≤ selected ∧ selected < active) (ha : active ≤ Zlength xs)
    (hm : HuffmanMinScan xs active selected) (hr : HuffmanResidualOptimum input (sublist 0 active xs) accumulated) :
    HuffmanFirstHeld input (replace_Znth selected (Znth (active-1) xs 0) xs) (active-1) (Znth selected xs 0) accumulated := by
  refine ⟨sublist 0 active xs, replace_last_removal_permutation__removals_bounds xs selected active hs ha, ?_, hr⟩
  intro w hw
  obtain ⟨k, hk, he⟩ := mem_nth (sublist 0 active xs) 0 w hw
  rw [prefix_length xs active ⟨by omega, ha⟩] at hk
  rw [prefix_nth xs 0 active k hk] at he
  rw [← he]; exact hm k hk

theorem in_sublist0_has_index__removals_bounds (A : Type) (l : List A) (d value : A) (active : Int)
    (ha : 0 ≤ active ∧ active ≤ Zlength l) (hv : value ∈ sublist 0 active l) :
    ∃ k, (0 ≤ k ∧ k < active) ∧ Znth k l d = value := by
  obtain ⟨k, hk, he⟩ := mem_nth _ d value hv
  rw [prefix_length l active ha] at hk
  rw [prefix_nth l d active k hk] at he
  exact ⟨k, hk, he⟩

theorem huffman_pair_ready_after_removal__removals_bounds (input scratch : List Int)
    (active held selected accumulated scanned n : Int) (hl : Zlength scratch = n)
    (ha : 1 ≤ active ∧ active < n) (hs : 0 ≤ selected ∧ selected < scanned)
    (hsc : active ≤ scanned ∧ scanned ≤ active) (hh : HuffmanFirstHeld input scratch active held accumulated)
    (hm : HuffmanMinScan scratch scanned selected) :
    HuffmanPairReady input (replace_Znth selected (Znth (active-1) scratch 0) scratch)
      (active-1) held (Znth selected scratch 0) accumulated := by
  have he : scanned = active := by omega
  subst scanned
  obtain ⟨prior, hp, hheld, hr⟩ := hh
  have hrem := replace_last_removal_permutation__removals_bounds scratch selected active hs (by omega)
  refine ⟨prior, hp.trans (hrem.cons held), hheld, ?_, hr⟩
  intro w hw
  obtain ⟨k, hk, he⟩ := in_sublist0_has_index__removals_bounds Int scratch 0 w active
    ⟨by omega, by omega⟩ (hrem.mem_iff.mpr hw)
  rw [← he]; exact hm k hk

theorem sum_permutation__removals_bounds (left right : List Int) (hp : List.Perm left right) : sum left = sum right := by
  induction hp with
  | nil => rfl
  | cons a h ih => exact congrArg (fun z => a+z) ih
  | swap a b l => change b+(a+_) = a+(b+_); omega
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

theorem sum_nonnegative_forall__removals_bounds (l : List Int) (hp : Forall (fun z => 0 ≤ z) l) : 0 ≤ sum l := by
  induction hp with
  | nil => rfl
  | @cons a l h ht ih => change 0 ≤ a+sum l; omega

theorem sum_contains_nonnegative__removals_bounds (l : List Int) (value : Int)
    (hp : Forall (fun z => 0 ≤ z) l) (hv : value ∈ l) : value ≤ sum l := by
  induction hp with
  | nil => simp at hv
  | @cons a l ha ht ih =>
    have := sum_nonnegative_forall__removals_bounds l ht
    rcases List.mem_cons.mp hv with rfl | hv
    · change value ≤ value+sum l; omega
    · have := ih hv; change value ≤ a+sum l; omega

private theorem forall_tail {A : Type} {P : A → Prop} {a : A} {l : List A} (h : Forall P (a::l)) : Forall P l :=
  Forall.iff_forall_mem.mpr (fun x hx => h.mem (List.mem_cons_of_mem _ hx))

private theorem bounded_sum (l : List Int) (hp : Forall (fun z => 0 ≤ z ∧ z ≤ 1000) l) :
    0 ≤ sum l ∧ sum l ≤ Zlength l*1000 := by
  induction hp with
  | nil => simp [sum, Zlength]
  | @cons a l ha ht ih => rw [Zlength_cons]; change 0 ≤ a+sum l ∧ a+sum l ≤ _; omega

theorem huffman_input_sum_bound__removals_bounds (input : List Int) (n : Int)
    (hl : Zlength input = n) (hn : 1 ≤ n ∧ n ≤ 8) (hb : HuffmanInputBounded input) : 0 ≤ sum input ∧ sum input ≤ 8000 := by
  have hp : Forall (fun z => 0 ≤ z ∧ z ≤ 1000) input := Forall.iff_forall_mem.mpr (by
    intro z hz; have := (bounded_forall input hb).mem hz; omega)
  have := bounded_sum input hp; omega

theorem huffman_bounded_competitor__removals_bounds (l : List Int) (hn : l ≠ [])
    (hp : Forall (fun z => 0 ≤ z) l) : ∃ tree, HuffmanLeaves tree = l ∧
      HuffmanWeightedPathLength tree ≤ (_root_.Int.ofNat (l.length-1))*sum l := by
  induction l with
  | nil => exact False.elim (hn rfl)
  | cons a l ih =>
    cases l with
    | nil => exact ⟨HuffmanLeaf a, rfl, by simp [HuffmanWeightedPathLength]⟩
    | cons b bs =>
      obtain ⟨t, ht, hc⟩ := ih (by simp) (forall_tail hp)
      refine ⟨HuffmanNode (HuffmanLeaf a) t, by simp [HuffmanLeaves, ht], ?_⟩
      have ha : 0 ≤ a := hp.mem (by simp)
      have hnprod := mul_nonneg (Int.natCast_nonneg bs.length) ha
      simp only [List.length_cons, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hc ⊢
      simp only [HuffmanWeightedPathLength, HuffmanTreeWeight, huffman_tree_weight_leaves t, ht, Int.zero_add]
      change _ ≤ ((bs.length : Int)+1)*(a+sum (b::bs))
      change HuffmanWeightedPathLength t ≤ (bs.length : Int)*sum (b::bs) at hc
      nlinarith

theorem huffman_optimal_input_upper__removals_bounds (input : List Int) (n optimum : Int)
    (hl : Zlength input = n) (hn : 1 ≤ n ∧ n ≤ 8) (hb : HuffmanInputBounded input)
    (ho : HuffmanOptimalCost input optimum) : optimum ≤ 56000 := by
  obtain ⟨t, ht, hc⟩ := huffman_bounded_competitor__removals_bounds input (by
    intro he; simp [he, Zlength] at hl; omega) (input_nonnegative input hb)
  obtain ⟨best, ⟨hf, hmin⟩, he⟩ := ho
  have hcomp : HuffmanTreeFeasible input t := by unfold HuffmanTreeFeasible; rw [ht]
  have := hmin t hcomp
  have hs := huffman_input_sum_bound__removals_bounds input n hl hn hb
  have hfactor : (_root_.Int.ofNat (input.length-1)) ≤ 7 := by
    change (input.length : Int) = n at hl
    change ((input.length-1 : Nat) : Int) ≤ 7
    omega
  have hprod := mul_le_mul_of_nonneg_right hfactor hs.1
  omega

theorem huffman_tree_cost_nonnegative__removals_bounds (tree : HuffmanTree)
    (hp : Forall (fun z => 0 ≤ z) (HuffmanLeaves tree)) : 0 ≤ HuffmanWeightedPathLength tree :=
  (huffman_tree_cost_nonnegative__copy_initialization tree hp).2

theorem huffman_nontrivial_cost_ge_weight__removals_bounds (tree : HuffmanTree)
    (hl : 2 ≤ Zlength (HuffmanLeaves tree)) (hp : Forall (fun z => 0 ≤ z) (HuffmanLeaves tree)) :
    HuffmanTreeWeight tree ≤ HuffmanWeightedPathLength tree := by
  cases tree with
  | HuffmanLeaf w => simp [HuffmanLeaves, Zlength] at hl
  | HuffmanNode l r =>
    obtain ⟨pl, pr⟩ := (forall_append _ _ _).mp hp
    have := huffman_tree_cost_nonnegative__removals_bounds l pl
    have := huffman_tree_cost_nonnegative__removals_bounds r pr
    dsimp [HuffmanTreeWeight, HuffmanWeightedPathLength]; omega

theorem huffman_optimal_cost_ge_sum__removals_bounds (live : List Int) (optimum : Int)
    (hl : 2 ≤ Zlength live) (hp : Forall (fun z => 0 ≤ z) live) (ho : HuffmanOptimalCost live optimum) :
    sum live ≤ optimum := by
  obtain ⟨best, ⟨hf, _⟩, he⟩ := ho
  have hlen : 2 ≤ Zlength (HuffmanLeaves best) := by unfold Zlength at *; rw [← hf.length_eq]; exact hl
  have := huffman_nontrivial_cost_ge_weight__removals_bounds best hlen (hp.perm hf)
  rw [huffman_tree_weight_leaves, ← sum_permutation__removals_bounds _ _ hf, he] at this
  exact this

theorem huffman_residual_charge_bounds__removals_bounds (input scratch : List Int)
    (active held selected accumulated n : Int) (hli : Zlength input = n) (hls : Zlength scratch = n)
    (hn : 1 ≤ n ∧ n ≤ 8) (hb : HuffmanInputBounded input) (ha : 1 ≤ active ∧ active < n)
    (hs : 0 ≤ selected ∧ selected < active) (hh : 1 ≤ held)
    (hf : HuffmanFirstHeld input scratch active held accumulated) :
    held+Znth selected scratch 0 ≤ 8000 ∧ accumulated+held+Znth selected scratch 0 ≤ 56000 := by
  obtain ⟨prior, hp, hleast, hsum, rem, hopt, htotal⟩ := hf
  have pp : Forall (fun z => 0 ≤ z) prior := Forall.iff_forall_mem.mpr (by intro z hz; have := hleast z hz; omega)
  have ps := forall_tail (pp.perm hp)
  have hlen := prefix_length scratch active ⟨by omega, by omega⟩
  have hmem : Znth selected scratch 0 ∈ sublist 0 active scratch := by
    rw [← prefix_nth scratch 0 active selected hs]
    exact nth_mem _ 0 selected (by rw [hlen]; exact hs)
  have hsumsel := sum_contains_nonnegative__removals_bounds _ _ ps hmem
  have hps := sum_permutation__removals_bounds _ _ hp
  change sum prior = held+sum (sublist 0 active scratch) at hps
  have hbound := huffman_input_sum_bound__removals_bounds input n hli hn hb
  have hlenp : 2 ≤ Zlength prior := by
    have hlp := hp.length_eq
    change ((sublist 0 active scratch).length : Int) = active at hlen
    change (2 : Int) ≤ (prior.length : Int)
    simp only [List.length_cons] at hlp; omega
  have hlower := huffman_optimal_cost_ge_sum__removals_bounds prior rem hlenp pp hopt
  have hupper := huffman_optimal_input_upper__removals_bounds input n (accumulated+rem) hli hn hb htotal
  omega

theorem huffman_optimal_cost_permutation__merge_transition (left right : List Int) (answer : Int)
    (hp : List.Perm left right) (ho : HuffmanOptimalCost left answer) : HuffmanOptimalCost right answer := by
  obtain ⟨best, ⟨hf, hm⟩, he⟩ := ho
  exact ⟨best, ⟨hp.symm.trans hf, fun s hs => hm s (hp.trans hs)⟩, he⟩

theorem permutation_swap_across_middle__merge_transition (A : Type) (first last : A) (middle suffix : List A) :
    List.Perm (first::(middle++last::suffix)) (last::(middle++first::suffix)) := by
  exact ((List.perm_middle.cons first).trans (List.Perm.swap _ _ _)).trans (List.perm_middle.symm.cons last)

theorem huffman_weighted_swap_to_front__merge_transition (first last : Int) (middle suffix : List Int)
    (maximum : Int) (middle_depths : List Int) (last_depth : Int) (suffix_depths : List Int)
    (hl : middle.length = middle_depths.length) (hw : last ≤ first) (hd : last_depth ≤ maximum) :
    HuffmanWeightedDepths (last::(middle++first::suffix)) (maximum::(middle_depths++last_depth::suffix_depths)) ≤
    HuffmanWeightedDepths (first::(middle++last::suffix)) (maximum::(middle_depths++last_depth::suffix_depths)) := by
  have diff (m ds : List Int) (h : m.length = ds.length) :
      HuffmanWeightedDepths (m++first::suffix) (ds++last_depth::suffix_depths) -
      HuffmanWeightedDepths (m++last::suffix) (ds++last_depth::suffix_depths) = (first-last)*last_depth := by
    rw [huffman_weighted_depths_app m _ ds _ h, huffman_weighted_depths_app m _ ds _ h, weighted_cons, weighted_cons]
    ring
  have hh := diff middle middle_depths hl
  rw [weighted_cons, weighted_cons]
  have := mul_nonneg (sub_nonneg.mpr hw) (sub_nonneg.mpr hd)
  nlinarith

private theorem promote_min (x maximum : Int) (weights depths : List Int)
    (hx : x ∈ weights) (hm : ∀ w ∈ weights, x ≤ w)
    (hl : weights.length = (maximum::depths).length) (hd : Forall (fun d => d ≤ maximum) depths) :
    ∃ tail, List.Perm weights (x::tail) ∧
      HuffmanWeightedDepths (x::tail) (maximum::depths) ≤ HuffmanWeightedDepths weights (maximum::depths) := by
  obtain ⟨pre, post, he⟩ := List.append_of_mem hx
  subst weights
  cases pre with
  | nil => exact ⟨post, List.Perm.refl _, le_refl _⟩
  | cons w mid =>
    simp only [List.cons_append, List.length_cons, List.length_append] at hl ⊢
    have hi : mid.length < depths.length := by omega
    let dm := depths.take mid.length
    let d := depths[mid.length]
    let dt := depths.drop (mid.length+1)
    have shape : depths = dm++d::dt := by
      dsimp [dm, d, dt]
      rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
    have hdm : mid.length = dm.length := by dsimp [dm]; rw [List.length_take_of_le (by omega)]
    have hdmax : d ≤ maximum := hd.mem (List.getElem_mem hi)
    refine ⟨mid++w::post, permutation_swap_across_middle__merge_transition Int w x mid post, ?_⟩
    rw [shape]
    exact huffman_weighted_swap_to_front__merge_transition w x mid post maximum dm d dt hdm
      (hm w (by simp)) hdmax

theorem huffman_two_minima_to_maximum_slots__merge_transition (x y : Int) (rest weights depths : List Int)
    (maximum : Int) (hp : List.Perm (x::y::rest) weights)
    (hx : ∀ w ∈ (x::y::rest), x ≤ w) (hy : ∀ w ∈ (y::rest), y ≤ w)
    (hn : depths ≠ []) (hl : weights.length = depths.length)
    (hshape : ∃ tail, depths = maximum::maximum::tail) (hd : Forall (fun d => d ≤ maximum) depths) :
    ∃ reordered_rest, List.Perm rest reordered_rest ∧
      HuffmanWeightedDepths (x::y::reordered_rest) depths ≤ HuffmanWeightedDepths weights depths := by
  obtain ⟨dt, rfl⟩ := hshape
  obtain ⟨tail, ht, hc⟩ := promote_min x maximum weights (maximum::dt)
    (hp.mem_iff.mp (by simp)) (fun w hw => hx w (hp.mem_iff.mpr hw)) hl (forall_tail hd)
  have hp1 : List.Perm (y::rest) tail := (hp.trans ht).cons_inv
  have hlen : tail.length = (maximum::dt).length := by
    have := ht.length_eq; simp only [List.length_cons] at this hl ⊢; omega
  obtain ⟨rr, hr, hc2⟩ := promote_min y maximum tail dt (hp1.mem_iff.mp (by simp))
    (fun w hw => hy w (hp1.mem_iff.mpr hw)) hlen (forall_tail (forall_tail hd))
  refine ⟨rr, (hp1.trans hr).cons_inv, ?_⟩
  rw [weighted_cons] at hc ⊢
  omega

private theorem weight_split (weights : List Int) (l r : HuffmanTree)
    (hl : weights.length = (HuffmanLeaves (HuffmanNode l r)).length) :
    (weights.take (HuffmanLeaves l).length).length = (HuffmanLeaves l).length ∧
    (weights.drop (HuffmanLeaves l).length).length = (HuffmanLeaves r).length := by
  simp only [HuffmanLeaves, List.length_append] at hl
  simp only [List.length_take, List.length_drop]
  omega

private theorem relabel_node_cost (l r nl nr : HuffmanTree) (wl wr : List Int)
    (hll : wl.length = (HuffmanLeaves l).length) (hlr : wr.length = (HuffmanLeaves r).length)
    (hwl : HuffmanTreeWeight nl = sum wl) (hwr : HuffmanTreeWeight nr = sum wr)
    (hcl : HuffmanWeightedDepths wl (HuffmanLeafDepths l) = HuffmanWeightedPathLength nl)
    (hcr : HuffmanWeightedDepths wr (HuffmanLeafDepths r) = HuffmanWeightedPathLength nr) :
    HuffmanWeightedDepths (wl++wr) (HuffmanLeafDepths (HuffmanNode l r)) =
      HuffmanWeightedPathLength (HuffmanNode nl nr) := by
  have ll := hll.trans (huffman_leaf_depth_profile l).1
  have lr := hlr.trans (huffman_leaf_depth_profile r).1
  dsimp [HuffmanLeafDepths]
  rw [huffman_weighted_depths_app wl wr _ _ (by simpa only [List.length_map] using ll),
    huffman_weighted_depths_lift _ _ ll, huffman_weighted_depths_lift _ _ lr, hcl, hcr]
  dsimp [HuffmanWeightedPathLength]
  rw [hwl, hwr]; omega

theorem huffman_relabel_profile__merge_transition (tree : HuffmanTree) (weights : List Int)
    (hl : weights.length = (HuffmanLeaves tree).length) : ∃ relabeled,
      HuffmanLeaves relabeled = weights ∧ HuffmanTreeWeight relabeled = sum weights ∧
      HuffmanWeightedDepths weights (HuffmanLeafDepths tree) = HuffmanWeightedPathLength relabeled := by
  induction tree generalizing weights with
  | HuffmanLeaf w =>
    cases weights with
    | nil => simp [HuffmanLeaves] at hl
    | cons a l =>
      have he : l = [] := by simpa [HuffmanLeaves] using hl
      subst l
      exact ⟨HuffmanLeaf a, rfl, by simp [HuffmanTreeWeight, sum], by simp [HuffmanLeafDepths, HuffmanWeightedPathLength, HuffmanWeightedDepths, sum]⟩
  | HuffmanNode l r ihl ihr =>
    obtain ⟨ll, lr⟩ := weight_split weights l r hl
    obtain ⟨nl, hnl, hwl, hcl⟩ := ihl _ ll
    obtain ⟨nr, hnr, hwr, hcr⟩ := ihr _ lr
    have shape := List.take_append_drop (HuffmanLeaves l).length weights
    refine ⟨HuffmanNode nl nr, ?_, ?_, ?_⟩
    · simpa only [HuffmanLeaves, hnl, hnr] using shape
    · rw [HuffmanTreeWeight, hwl, hwr, ← sum_app, shape]
    · have := relabel_node_cost l r nl nr _ _ ll lr hwl hwr hcl hcr
      simpa only [shape] using this

private def RelabelContract (tree : HuffmanTree) : Prop :=
  ∀ weights, weights.length = (HuffmanLeaves tree).length → ∃ relabeled,
    HuffmanLeaves relabeled = weights ∧ HuffmanTreeWeight relabeled = sum weights ∧
    HuffmanWeightedDepths weights (HuffmanLeafDepths tree) = HuffmanWeightedPathLength relabeled ∧
    ∀ first second rest, weights = first::second::rest → ∃ contracted,
      HuffmanLeaves contracted = (first+second)::rest ∧
      HuffmanTreeWeight relabeled = HuffmanTreeWeight contracted ∧
      HuffmanWeightedPathLength relabeled = HuffmanWeightedPathLength contracted+first+second

private theorem relabel_contract_node (l r : HuffmanTree) (hl : 2 ≤ (HuffmanLeaves l).length)
    (hc : RelabelContract l) : RelabelContract (HuffmanNode l r) := by
  intro weights hw
  obtain ⟨ll, lr⟩ := weight_split weights l r hw
  obtain ⟨nl, hnl, hwl, hcl, hcontract⟩ := hc _ ll
  obtain ⟨nr, hnr, hwr, hcr⟩ := huffman_relabel_profile__merge_transition r _ lr
  have shape := List.take_append_drop (HuffmanLeaves l).length weights
  refine ⟨HuffmanNode nl nr, ?_, ?_, ?_, ?_⟩
  · simpa only [HuffmanLeaves, hnl, hnr] using shape
  · rw [HuffmanTreeWeight, hwl, hwr, ← sum_app, shape]
  · have := relabel_node_cost l r nl nr _ _ ll lr hwl hwr hcl hcr
    simpa only [shape] using this
  · intro first second rest he
    subst weights
    obtain ⟨k, hk⟩ : ∃ k, (HuffmanLeaves l).length = k+2 := ⟨(HuffmanLeaves l).length-2, by omega⟩
    have htake : List.take (HuffmanLeaves l).length (first::second::rest) = first::second::List.take k rest := by
      rw [hk]; rfl
    have hdrop : List.drop (HuffmanLeaves l).length (first::second::rest) = List.drop k rest := by rw [hk]; rfl
    obtain ⟨ct, hct, hwt, hcost⟩ := hcontract first second (rest.take k) htake
    refine ⟨HuffmanNode ct nr, ?_, ?_, ?_⟩
    · simp only [HuffmanLeaves, hct, hnr, hdrop, List.cons_append, List.take_append_drop]
    · dsimp [HuffmanTreeWeight]; rw [hwt]
    · dsimp [HuffmanWeightedPathLength]; rw [hcost, hwt]; omega

theorem huffman_normalized_pair_profile__merge_transition (context : HuffmanTreeContext) (old_first old_second : Int) :
    ∃ normalized depth_tail,
      List.Perm (HuffmanLeaves normalized) (HuffmanLeaves (HuffmanPlug context (HuffmanNode (HuffmanLeaf old_first) (HuffmanLeaf old_second)))) ∧
      HuffmanTreeWeight normalized = HuffmanTreeWeight (HuffmanPlug context (HuffmanNode (HuffmanLeaf old_first) (HuffmanLeaf old_second))) ∧
      HuffmanWeightedPathLength normalized = HuffmanWeightedPathLength (HuffmanPlug context (HuffmanNode (HuffmanLeaf old_first) (HuffmanLeaf old_second))) ∧
      HuffmanTreeHeight normalized = HuffmanTreeHeight (HuffmanPlug context (HuffmanNode (HuffmanLeaf old_first) (HuffmanLeaf old_second))) ∧
      HuffmanLeafDepths normalized = (HuffmanContextDepth context+1)::(HuffmanContextDepth context+1)::depth_tail ∧
      (∀ weights, weights.length = (HuffmanLeaves normalized).length → ∃ relabeled,
        HuffmanLeaves relabeled = weights ∧ HuffmanTreeWeight relabeled = sum weights ∧
        HuffmanWeightedDepths weights (HuffmanLeafDepths normalized) = HuffmanWeightedPathLength relabeled ∧
        ∀ first second rest, weights = first::second::rest → ∃ contracted,
          HuffmanLeaves contracted = (first+second)::rest ∧ HuffmanTreeWeight relabeled = HuffmanTreeWeight contracted ∧
          HuffmanWeightedPathLength relabeled = HuffmanWeightedPathLength contracted+first+second) := by
  induction context with
  | HuffmanRootContext =>
    refine ⟨HuffmanNode (HuffmanLeaf old_first) (HuffmanLeaf old_second), [], List.Perm.refl _, rfl, rfl, rfl, rfl, ?_⟩
    intro weights hl
    cases weights with
    | nil => simp [HuffmanLeaves] at hl
    | cons f fs => cases fs with
      | nil => simp [HuffmanLeaves] at hl
      | cons s rest =>
        have he : rest = [] := by simpa [HuffmanLeaves] using hl
        subst rest
        refine ⟨HuffmanNode (HuffmanLeaf f) (HuffmanLeaf s), rfl, ?_, ?_, ?_⟩
        · simp [HuffmanTreeWeight, sum]
        · simp [HuffmanWeightedPathLength, HuffmanTreeWeight, HuffmanWeightedDepths, HuffmanLeafDepths, sum]
        · intro x y rest he
          simp only [List.cons.injEq, List.nil_eq] at he
          obtain ⟨rfl, rfl, rfl⟩ := he
          exact ⟨HuffmanLeaf (f+s), rfl, rfl, by simp [HuffmanWeightedPathLength, HuffmanTreeWeight]⟩
  | HuffmanLeftContext ctx sibling ih =>
    obtain ⟨nt, dt, hp, hw, hc, hh, hd, hr⟩ := ih
    refine ⟨HuffmanNode nt sibling, dt.map (·+1)++(HuffmanLeafDepths sibling).map (·+1),
      hp.append (List.Perm.refl _), ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [HuffmanPlug, HuffmanTreeWeight, hw]
    · simp only [HuffmanPlug, HuffmanWeightedPathLength, hw, hc]
    · simp only [HuffmanPlug, HuffmanTreeHeight, hh]
    · simp only [HuffmanLeafDepths, hd, List.map_cons, List.cons_append, HuffmanContextDepth]
    · exact relabel_contract_node nt sibling (by
        have hlen := (huffman_leaf_depth_profile nt).1
        rw [hd] at hlen; simp only [List.length_cons] at hlen; omega) hr
  | HuffmanRightContext sibling ctx ih =>
    obtain ⟨nt, dt, hp, hw, hc, hh, hd, hr⟩ := ih
    refine ⟨HuffmanNode nt sibling, dt.map (·+1)++(HuffmanLeafDepths sibling).map (·+1),
      (hp.append (List.Perm.refl _)).trans List.perm_append_comm, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [HuffmanPlug, HuffmanTreeWeight, hw]; omega
    · simp only [HuffmanPlug, HuffmanWeightedPathLength, hw, hc]; omega
    · simp only [HuffmanPlug, HuffmanTreeHeight, hh, _root_.max_comm]
    · simp only [HuffmanLeafDepths, hd, List.map_cons, List.cons_append, HuffmanContextDepth]
    · exact relabel_contract_node nt sibling (by
        have hlen := (huffman_leaf_depth_profile nt).1
        rw [hd] at hlen; simp only [List.length_cons] at hlen; omega) hr

private theorem leaf_context (tree : HuffmanTree) (z : Int) (hz : z ∈ HuffmanLeaves tree) :
    ∃ context, tree = HuffmanPlug context (HuffmanLeaf z) := by
  induction tree with
  | HuffmanLeaf w =>
    have he : z = w := by simpa [HuffmanLeaves] using hz
    subst w; exact ⟨HuffmanRootContext, rfl⟩
  | HuffmanNode l r ihl ihr =>
    rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨ctx, he⟩ := ihl hz; exact ⟨HuffmanLeftContext ctx r, by rw [he]; rfl⟩
    · obtain ⟨ctx, he⟩ := ihr hz; exact ⟨HuffmanRightContext l ctx, by rw [he]; rfl⟩

private theorem context_leaves_frame (context : HuffmanTreeContext) :
    ∃ outside, ∀ hole, List.Perm (HuffmanContextLeaves context hole) (hole++outside) := by
  induction context with
  | HuffmanRootContext => exact ⟨[], fun hole => by simp [HuffmanContextLeaves]⟩
  | HuffmanLeftContext ctx sibling ih =>
    obtain ⟨out, ho⟩ := ih
    refine ⟨out++HuffmanLeaves sibling, fun hole => ?_⟩
    simpa only [HuffmanContextLeaves, List.append_assoc] using (ho hole).append (List.Perm.refl (HuffmanLeaves sibling))
  | HuffmanRightContext sibling ctx ih =>
    obtain ⟨out, ho⟩ := ih
    refine ⟨out++HuffmanLeaves sibling, fun hole => ?_⟩
    have hh := (List.perm_append_comm (l₁ := HuffmanLeaves sibling) (l₂ := HuffmanContextLeaves ctx hole)).trans
      ((ho hole).append (List.Perm.refl (HuffmanLeaves sibling)))
    simpa only [HuffmanContextLeaves, List.append_assoc] using hh

theorem huffman_expand_contracted_tree__merge_transition (x y : Int) (rest : List Int) (contracted : HuffmanTree)
    (hp : List.Perm (rest++[x+y]) (HuffmanLeaves contracted)) : ∃ expanded,
      List.Perm (x::y::rest) (HuffmanLeaves expanded) ∧
      HuffmanTreeWeight expanded = HuffmanTreeWeight contracted ∧
      HuffmanWeightedPathLength expanded = HuffmanWeightedPathLength contracted+x+y := by
  obtain ⟨ctx, he⟩ := leaf_context contracted (x+y) (hp.mem_iff.mp (by simp))
  subst contracted
  obtain ⟨outside, hout⟩ := context_leaves_frame ctx
  have hc := hout [x+y]
  have hl : HuffmanLeaves (HuffmanPlug ctx (HuffmanLeaf (x+y))) = HuffmanContextLeaves ctx [x+y] := huffman_plug_leaves _ _
  have hrest : List.Perm rest outside := by
    have hh := (List.perm_append_comm (l₁ := [x+y]) (l₂ := rest)).trans hp
    rw [hl] at hh
    exact (hh.trans hc).cons_inv
  refine ⟨HuffmanPlug ctx (HuffmanNode (HuffmanLeaf x) (HuffmanLeaf y)), ?_,
    huffman_contract_weight ctx x y, huffman_contract_path_length ctx x y⟩
  rw [huffman_plug_leaves]
  exact ((hrest.cons y).cons x).trans (hout [x,y]).symm

theorem huffman_greedy_contraction__merge_transition (prior : List Int) (x y : Int) (rest : List Int) (remaining : Int)
    (hp : List.Perm prior (x::y::rest)) (hx : ∀ w ∈ prior, x ≤ w) (hy : ∀ w ∈ (y::rest), y ≤ w)
    (ho : HuffmanOptimalCost prior remaining) : ∃ contracted_remaining,
      HuffmanOptimalCost (rest++[x+y]) contracted_remaining ∧ remaining = contracted_remaining+x+y := by
  obtain ⟨best, ⟨hf, hmin⟩, he⟩ := huffman_optimal_cost_permutation__merge_transition prior _ remaining hp ho
  have hnode : ∃ l r, best = HuffmanNode l r := by
    cases best with
    | HuffmanLeaf w => have := hf.length_eq; simp [HuffmanLeaves] at this
    | HuffmanNode l r => exact ⟨l, r, rfl⟩
  obtain ⟨ctx, f, s, hshape, hdepth⟩ := huffman_deepest_sibling_exists best hnode
  obtain ⟨nt, dt, hnperm, hnweight, hncost, hnheight, hndepths, hnrelabel⟩ :=
    huffman_normalized_pair_profile__merge_transition ctx f s
  have hnfeasible : List.Perm (x::y::rest) (HuffmanLeaves nt) := by
    apply hf.trans
    rw [hshape]; exact hnperm.symm
  have hncostbest : HuffmanWeightedPathLength nt = HuffmanWeightedPathLength best := by rw [hshape]; exact hncost
  have depthshape : HuffmanLeafDepths nt = HuffmanTreeHeight nt::HuffmanTreeHeight nt::dt := by
    rw [hndepths, hnheight, ← hshape, ← hdepth]
  obtain ⟨rr, hrr, hexchange⟩ := huffman_two_minima_to_maximum_slots__merge_transition x y rest
    (HuffmanLeaves nt) (HuffmanLeafDepths nt) (HuffmanTreeHeight nt) hnfeasible
    (fun w hw => hx w (hp.mem_iff.mpr hw)) hy (by rw [depthshape]; simp)
    (huffman_leaf_depth_profile nt).1 ⟨dt, depthshape⟩ (huffman_leaf_depths_bounded nt)
  have hlen : (x::y::rr).length = (HuffmanLeaves nt).length := by
    have hl1 := hrr.length_eq; have hl2 := hnfeasible.length_eq
    simp only [List.length_cons] at hl2 ⊢; omega
  obtain ⟨rt, hrl, hrw, hrc, hrcontract⟩ := hnrelabel _ hlen
  obtain ⟨ct, hcl, hcw, hcc⟩ := hrcontract x y rr rfl
  have hrf : HuffmanTreeFeasible (x::y::rest) rt := by
    unfold HuffmanTreeFeasible; rw [hrl]; exact (hrr.cons y).cons x
  have hbestle := hmin rt hrf
  rw [hrc, (huffman_leaf_depth_profile nt).2] at hexchange
  refine ⟨HuffmanWeightedPathLength ct, ⟨ct, ⟨?_, ?_⟩, rfl⟩, ?_⟩
  · unfold HuffmanTreeFeasible
    rw [hcl]
    exact (hrr.append (List.Perm.refl [x+y])).trans List.perm_append_comm
  · intro candidate hcand
    obtain ⟨expanded, hef, hew, hec⟩ := huffman_expand_contracted_tree__merge_transition x y rest candidate hcand
    have := hmin expanded hef; omega
  · omega

theorem replace_nth_decomposition__merge_transition (A : Type) (index : Nat) (values : List A) (value : A)
    (hi : index < values.length) : replace_nth index values value = values.take index++value::values.drop (index+1) := by
  induction values generalizing index with
  | nil => simp at hi
  | cons a l ih =>
    cases index with
    | zero => rfl
    | succ k => simpa only [replace_nth, List.take_succ_cons, List.drop_succ_cons, List.cons_append]
        using congrArg (List.cons a) (ih k (by simpa using hi))

theorem huffman_replace_live_prefix__merge_transition (values : List Int) (index value : Int)
    (hi : 0 ≤ index ∧ index < Zlength values) :
    sublist 0 (index+1) (replace_Znth index value values) = sublist 0 index values++[value] := by
  have hn : index.toNat < values.length := by change (0 ≤ index ∧ index < (values.length : Int)) at hi; omega
  have hs : (index+1).toNat = index.toNat+1 := by omega
  unfold sublist replace_Znth
  simp only [Int.toNat_zero, List.drop_zero, hs]
  rw [replace_nth_decomposition__merge_transition Int _ _ _ hn, List.take_append]
  rw [List.length_take_of_le (by omega), show index.toNat+1-index.toNat = 1 by omega,
    List.take_of_length_le (by rw [List.length_take_of_le (by omega)]; omega)]
  rfl

theorem sum_permutation__merge_transition (left right : List Int) (hp : List.Perm left right) : sum left = sum right :=
  sum_permutation__removals_bounds left right hp

theorem huffman_progress_after_merge__merge_transition (input scratch : List Int) (active x y accumulated : Int)
    (ha : 0 ≤ active ∧ active < Zlength scratch) (hp : HuffmanPairReady input scratch active x y accumulated) :
    HuffmanProgress input (replace_Znth active (x+y) scratch) (active+1) (accumulated+x+y) := by
  obtain ⟨prior, hp, hx, hy, hs, rem, ho, hinput⟩ := hp
  obtain ⟨cr, hc, he⟩ := huffman_greedy_contraction__merge_transition prior x y _ rem hp hx hy ho
  unfold HuffmanProgress HuffmanResidualOptimum
  rw [huffman_replace_live_prefix__merge_transition scratch active (x+y) ha]
  refine ⟨?_, cr, hc, ?_⟩
  · have hsum := sum_permutation__merge_transition _ _ hp
    change sum prior = x+(y+sum (sublist 0 active scratch)) at hsum
    rw [sum_app]; change sum (sublist 0 active scratch)+((x+y)+0) = sum input
    omega
  · convert hinput using 1 <;> omega

theorem huffman_leaves_nonempty__final_result (tree : HuffmanTree) : 1 ≤ (HuffmanLeaves tree).length := by
  induction tree with
  | HuffmanLeaf w => rfl
  | HuffmanNode l r ihl ihr => simp only [HuffmanLeaves, List.length_append]; omega

theorem huffman_singleton_tree_cost_zero__final_result (weight : Int) (tree : HuffmanTree)
    (hf : HuffmanTreeFeasible [weight] tree) : HuffmanWeightedPathLength tree = 0 := by
  cases tree with
  | HuffmanLeaf w => rfl
  | HuffmanNode l r =>
    have hl := hf.length_eq
    have := huffman_leaves_nonempty__final_result l
    have := huffman_leaves_nonempty__final_result r
    simp only [HuffmanLeaves, List.length_append, List.length_singleton] at hl
    omega

theorem huffman_singleton_optimal_zero__final_result (weight answer : Int)
    (ho : HuffmanOptimalCost [weight] answer) : answer = 0 := by
  obtain ⟨tree, ⟨hf, _⟩, he⟩ := ho
  rw [← he]; exact huffman_singleton_tree_cost_zero__final_result weight tree hf

theorem sublist_zero_one__final_result (values : List Int) (hl : 1 ≤ Zlength values) :
    sublist 0 1 values = [Znth 0 values 0] := by
  exact sublist_single 0 0 values ⟨le_refl _, by omega⟩


set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open Algorithms.huffman_encoding.lean.groundtruth.huffman_encoding_goal
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

theorem proof_of_huffman_cost_entail_wit_1 : huffman_cost_entail_wit_1 := by
  unfold huffman_cost_entail_wit_1
  right
  intro n_pre weights_l PreH1 PreH2 PreH3 PreH4
  refine Automation.exp_right_rule (CRules := naive_C_Rules) weights_l ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | rfl | omega

theorem proof_of_huffman_cost_entail_wit_2 : huffman_cost_entail_wit_2 := by
  unfold huffman_cost_entail_wit_2
  right
  intro n_pre weights_l i copied_2 remaining_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  cases remaining_2 with
  | nil =>
    simp only [List.append_nil] at PreH6
    rw [PreH6] at PreH4
    omega
  | cons next tail =>
    have he : Znth (Zlength copied_2) (copied_2++next::tail) 0 = next := by
      rw [app_Znth2 0 copied_2 (next::tail) _ (le_refl _)]
      simp only [Int.sub_self, Znth0_cons]
    refine Automation.exp_right_rule (CRules := naive_C_Rules) tail ?_
    rw [he]
    split_pure_spatial
    · cancel
    · split_pures <;> dump_pre_spatial
      all_goals first
        | simp only [List.append_assoc, List.cons_append, List.nil_append]
        | rw [Zlength_app, Zlength_cons, Zlength_nil]; omega
        | rw [← PreH6]; omega
        | omega

theorem proof_of_huffman_cost_entail_wit_3 : huffman_cost_entail_wit_3 := by
  unfold huffman_cost_entail_wit_3
  right
  intro work_pre n_pre weights_l i copied remaining PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have hei : i = n_pre := by omega
  have hr : remaining = [] := by
    have hh := congrArg Zlength PreH6
    rw [Zlength_app] at hh
    have hz : Zlength remaining = 0 := by omega
    cases remaining with
    | nil => rfl
    | cons a l => rw [Zlength_cons] at hz; have := Zlength_nonneg l; omega
  rw [hr, List.append_nil] at PreH6
  rw [← PreH6, hei]
  have hb := huffman_input_live_bounds__copy_initialization weights_l n_pre PreH4 PreH5
  have hp : HuffmanProgress weights_l weights_l n_pre 0 := by
    rw [← PreH4]; exact huffman_initial_progress__copy_initialization weights_l (by omega) PreH5
  refine Automation.exp_right_rule (CRules := naive_C_Rules) weights_l ?_
  split_pure_spatial
  · simpa only [Int.zero_mul, Int.add_zero, Int.sub_zero] using intArray.seg_to_full work_pre 0 n_pre weights_l
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_huffman_cost_entail_wit_4_split_goal_1 : huffman_cost_entail_wit_4_split_goal_1 := by
  unfold huffman_cost_entail_wit_4_split_goal_1
  intro n_pre weights_l total active work_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  exact huffman_min_scan_init__min_scan_updates work_l_2

theorem proof_of_huffman_cost_entail_wit_4_split_goal_2 : huffman_cost_entail_wit_4_split_goal_2 := by
  unfold huffman_cost_entail_wit_4_split_goal_2
  intro n_pre weights_l total active work_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  exact PreH11

theorem proof_of_huffman_cost_entail_wit_4 : huffman_cost_entail_wit_4 := by
  unfold huffman_cost_entail_wit_4
  right
  intro n_pre weights_l total active work_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_huffman_cost_entail_wit_4_split_goal_1 n_pre weights_l total active work_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_huffman_cost_entail_wit_4_split_goal_2 n_pre weights_l total active work_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_huffman_cost_entail_wit_6_1_split_goal_1 : huffman_cost_entail_wit_6_1_split_goal_1 := by
  unfold huffman_cost_entail_wit_6_1_split_goal_1
  intro n_pre weights_l total first i active work_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  exact huffman_min_scan_take_new__min_scan_updates work_l_2 i first PreH22 PreH1

theorem proof_of_huffman_cost_entail_wit_6_1 : huffman_cost_entail_wit_6_1 := by
  unfold huffman_cost_entail_wit_6_1
  right
  intro n_pre weights_l total first i active work_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_huffman_cost_entail_wit_6_1_split_goal_1 n_pre weights_l total first i active work_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22

theorem proof_of_huffman_cost_entail_wit_6_2_split_goal_1 : huffman_cost_entail_wit_6_2_split_goal_1 := by
  unfold huffman_cost_entail_wit_6_2_split_goal_1
  intro n_pre weights_l total first i active work_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  exact huffman_min_scan_keep_old__min_scan_updates work_l_2 i first PreH22 PreH1

theorem proof_of_huffman_cost_entail_wit_6_2 : huffman_cost_entail_wit_6_2 := by
  unfold huffman_cost_entail_wit_6_2
  right
  intro n_pre weights_l total first i active work_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_huffman_cost_entail_wit_6_2_split_goal_1 n_pre weights_l total first i active work_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22

theorem proof_of_huffman_cost_entail_wit_8_split_goal_1 : huffman_cost_entail_wit_8_split_goal_1 := by
  unfold huffman_cost_entail_wit_8_split_goal_1
  intro n_pre weights_l total first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  apply huffman_first_held_after_removal__removals_bounds weights_l work_l first active total
  · omega
  · omega
  · have he : i = active := by omega
    simpa only [he] using PreH21
  · exact PreH20

theorem proof_of_huffman_cost_entail_wit_8_split_goal_2 : huffman_cost_entail_wit_8_split_goal_2 := by
  unfold huffman_cost_entail_wit_8_split_goal_2
  intro n_pre weights_l total first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  exact replace_last_live_bounds__removals_bounds work_l first active 1 8000 ⟨PreH14, by omega⟩ (by omega) PreH19

theorem proof_of_huffman_cost_entail_wit_8_split_goal_3 : huffman_cost_entail_wit_8_split_goal_3 := by
  unfold huffman_cost_entail_wit_8_split_goal_3
  intro n_pre weights_l total first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  exact (PreH19 first ⟨PreH14, by omega⟩).2

theorem proof_of_huffman_cost_entail_wit_8_split_goal_4 : huffman_cost_entail_wit_8_split_goal_4 := by
  unfold huffman_cost_entail_wit_8_split_goal_4
  intro n_pre weights_l total first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  exact (PreH19 first ⟨PreH14, by omega⟩).1

theorem proof_of_huffman_cost_entail_wit_8_split_goal_5 : huffman_cost_entail_wit_8_split_goal_5 := by
  unfold huffman_cost_entail_wit_8_split_goal_5
  intro n_pre weights_l total first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  rw [Zlength_replace_Znth]; exact PreH7

theorem proof_of_huffman_cost_entail_wit_8 : huffman_cost_entail_wit_8 := by
  unfold huffman_cost_entail_wit_8
  right
  intro n_pre weights_l total first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_huffman_cost_entail_wit_8_split_goal_1 n_pre weights_l total first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
      | exact proof_of_huffman_cost_entail_wit_8_split_goal_2 n_pre weights_l total first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
      | exact proof_of_huffman_cost_entail_wit_8_split_goal_3 n_pre weights_l total first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
      | exact proof_of_huffman_cost_entail_wit_8_split_goal_4 n_pre weights_l total first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
      | exact proof_of_huffman_cost_entail_wit_8_split_goal_5 n_pre weights_l total first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21

theorem proof_of_huffman_cost_entail_wit_9_split_goal_1 : huffman_cost_entail_wit_9_split_goal_1 := by
  unfold huffman_cost_entail_wit_9_split_goal_1
  intro n_pre weights_l work_l_2 active first x total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  exact huffman_min_scan_init__min_scan_updates work_l_2

theorem proof_of_huffman_cost_entail_wit_9_split_goal_2 : huffman_cost_entail_wit_9_split_goal_2 := by
  unfold huffman_cost_entail_wit_9_split_goal_2
  intro n_pre weights_l work_l_2 active first x total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  exact PreH14

theorem proof_of_huffman_cost_entail_wit_9 : huffman_cost_entail_wit_9 := by
  unfold huffman_cost_entail_wit_9
  right
  intro n_pre weights_l work_l_2 active first x total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_huffman_cost_entail_wit_9_split_goal_1 n_pre weights_l work_l_2 active first x total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
      | exact proof_of_huffman_cost_entail_wit_9_split_goal_2 n_pre weights_l work_l_2 active first x total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15

theorem proof_of_huffman_cost_entail_wit_10_1_split_goal_1 : huffman_cost_entail_wit_10_1_split_goal_1 := by
  unfold huffman_cost_entail_wit_10_1_split_goal_1
  intro n_pre weights_l total x second first i active work_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  exact huffman_min_scan_take_new__min_scan_updates work_l_2 i second PreH24 PreH1

theorem proof_of_huffman_cost_entail_wit_10_1 : huffman_cost_entail_wit_10_1 := by
  unfold huffman_cost_entail_wit_10_1
  right
  intro n_pre weights_l total x second first i active work_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_huffman_cost_entail_wit_10_1_split_goal_1 n_pre weights_l total x second first i active work_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_huffman_cost_entail_wit_10_2_split_goal_1 : huffman_cost_entail_wit_10_2_split_goal_1 := by
  unfold huffman_cost_entail_wit_10_2_split_goal_1
  intro n_pre weights_l total x second first i active work_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  exact huffman_min_scan_keep_old__min_scan_updates work_l_2 i second PreH24 PreH1

theorem proof_of_huffman_cost_entail_wit_10_2 : huffman_cost_entail_wit_10_2 := by
  unfold huffman_cost_entail_wit_10_2
  right
  intro n_pre weights_l total x second first i active work_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_huffman_cost_entail_wit_10_2_split_goal_1 n_pre weights_l total x second first i active work_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_huffman_cost_entail_wit_12_split_goal_1 : huffman_cost_entail_wit_12_split_goal_1 := by
  unfold huffman_cost_entail_wit_12_split_goal_1
  intro n_pre weights_l total x second first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  exact huffman_pair_ready_after_removal__removals_bounds weights_l work_l active x second total i n_pre
    PreH7 ⟨PreH9, PreH10⟩ ⟨PreH16, PreH17⟩ ⟨PreH3, PreH12⟩ PreH24 PreH25

theorem proof_of_huffman_cost_entail_wit_12_split_goal_2 : huffman_cost_entail_wit_12_split_goal_2 := by
  unfold huffman_cost_entail_wit_12_split_goal_2
  intro n_pre weights_l total x second first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  exact replace_last_live_bounds__removals_bounds work_l second active 1 8000 ⟨PreH16, by omega⟩ (by omega) PreH23

theorem proof_of_huffman_cost_entail_wit_12_split_goal_3 : huffman_cost_entail_wit_12_split_goal_3 := by
  unfold huffman_cost_entail_wit_12_split_goal_3
  intro n_pre weights_l total x second first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  exact (huffman_residual_charge_bounds__removals_bounds weights_l work_l active x second total n_pre
    PreH6 PreH7 ⟨PreH4, PreH5⟩ PreH8 ⟨PreH9, PreH10⟩ ⟨PreH16, by omega⟩ PreH19 PreH24).2

theorem proof_of_huffman_cost_entail_wit_12_split_goal_4 : huffman_cost_entail_wit_12_split_goal_4 := by
  unfold huffman_cost_entail_wit_12_split_goal_4
  intro n_pre weights_l total x second first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  exact (huffman_residual_charge_bounds__removals_bounds weights_l work_l active x second total n_pre
    PreH6 PreH7 ⟨PreH4, PreH5⟩ PreH8 ⟨PreH9, PreH10⟩ ⟨PreH16, by omega⟩ PreH19 PreH24).1

theorem proof_of_huffman_cost_entail_wit_12_split_goal_5 : huffman_cost_entail_wit_12_split_goal_5 := by
  unfold huffman_cost_entail_wit_12_split_goal_5
  intro n_pre weights_l total x second first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  exact (PreH23 second ⟨PreH16, by omega⟩).2

theorem proof_of_huffman_cost_entail_wit_12_split_goal_6 : huffman_cost_entail_wit_12_split_goal_6 := by
  unfold huffman_cost_entail_wit_12_split_goal_6
  intro n_pre weights_l total x second first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  exact (PreH23 second ⟨PreH16, by omega⟩).1

theorem proof_of_huffman_cost_entail_wit_12_split_goal_7 : huffman_cost_entail_wit_12_split_goal_7 := by
  unfold huffman_cost_entail_wit_12_split_goal_7
  intro n_pre weights_l total x second first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  rw [Zlength_replace_Znth]; exact PreH7

theorem proof_of_huffman_cost_entail_wit_12 : huffman_cost_entail_wit_12 := by
  unfold huffman_cost_entail_wit_12
  right
  intro n_pre weights_l total x second first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_huffman_cost_entail_wit_12_split_goal_1 n_pre weights_l total x second first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
      | exact proof_of_huffman_cost_entail_wit_12_split_goal_2 n_pre weights_l total x second first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
      | exact proof_of_huffman_cost_entail_wit_12_split_goal_3 n_pre weights_l total x second first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
      | exact proof_of_huffman_cost_entail_wit_12_split_goal_4 n_pre weights_l total x second first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
      | exact proof_of_huffman_cost_entail_wit_12_split_goal_5 n_pre weights_l total x second first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
      | exact proof_of_huffman_cost_entail_wit_12_split_goal_6 n_pre weights_l total x second first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
      | exact proof_of_huffman_cost_entail_wit_12_split_goal_7 n_pre weights_l total x second first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_huffman_cost_entail_wit_13_split_goal_1 : huffman_cost_entail_wit_13_split_goal_1 := by
  unfold huffman_cost_entail_wit_13_split_goal_1
  intro n_pre weights_l work_l_2 active first second x y total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  simpa only [Int.add_assoc] using huffman_progress_after_merge__merge_transition weights_l work_l_2 active x y total
    ⟨PreH6, by omega⟩ PreH20

theorem proof_of_huffman_cost_entail_wit_13_split_goal_2 : huffman_cost_entail_wit_13_split_goal_2 := by
  unfold huffman_cost_entail_wit_13_split_goal_2
  intro n_pre weights_l work_l_2 active first second x y total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  intro k hk
  by_cases he : k = active
  · subst k
    rw [Znth_replace_Znth_Same 0 work_l_2 active _ ⟨PreH6, by omega⟩]
    omega
  · rw [Znth_replace_Znth_Diff 0 work_l_2 active k _ ⟨PreH6, by omega⟩ ⟨hk.1, by omega⟩ (Ne.symm he)]
    exact PreH19 k ⟨hk.1, by omega⟩

theorem proof_of_huffman_cost_entail_wit_13_split_goal_3 : huffman_cost_entail_wit_13_split_goal_3 := by
  unfold huffman_cost_entail_wit_13_split_goal_3
  intro n_pre weights_l work_l_2 active first second x y total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  rw [Zlength_replace_Znth]; exact PreH4

theorem proof_of_huffman_cost_entail_wit_13 : huffman_cost_entail_wit_13 := by
  unfold huffman_cost_entail_wit_13
  right
  intro n_pre weights_l work_l_2 active first second x y total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_huffman_cost_entail_wit_13_split_goal_1 n_pre weights_l work_l_2 active first second x y total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
      | exact proof_of_huffman_cost_entail_wit_13_split_goal_2 n_pre weights_l work_l_2 active first second x y total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
      | exact proof_of_huffman_cost_entail_wit_13_split_goal_3 n_pre weights_l work_l_2 active first second x y total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20

theorem proof_of_huffman_cost_entail_wit_14_split_goal_1 : huffman_cost_entail_wit_14_split_goal_1 := by
  unfold huffman_cost_entail_wit_14_split_goal_1
  intro n_pre weights_l total active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have he : active = 1 := by omega
  unfold HuffmanProgress HuffmanResidualOptimum at PreH12
  rw [he, sublist_zero_one__final_result work_l (by omega)] at PreH12
  unfold HuffmanScratchFinal
  simpa only [sum, List.foldr_cons, List.foldr_nil, Int.add_zero] using PreH12.1

theorem proof_of_huffman_cost_entail_wit_14_split_goal_2 : huffman_cost_entail_wit_14_split_goal_2 := by
  unfold huffman_cost_entail_wit_14_split_goal_2
  intro n_pre weights_l total active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have he : active = 1 := by omega
  unfold HuffmanProgress HuffmanResidualOptimum at PreH12
  rw [he, sublist_zero_one__final_result work_l (by omega)] at PreH12
  obtain ⟨_, rem, ho, hi⟩ := PreH12
  have hz := huffman_singleton_optimal_zero__final_result _ rem ho
  simpa only [hz, Int.add_zero] using hi

theorem proof_of_huffman_cost_entail_wit_14 : huffman_cost_entail_wit_14 := by
  unfold huffman_cost_entail_wit_14
  right
  intro n_pre weights_l total active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_huffman_cost_entail_wit_14_split_goal_1 n_pre weights_l total active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_huffman_cost_entail_wit_14_split_goal_2 n_pre weights_l total active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

end Algorithms.huffman_encoding.lean.groundtruth.huffman_encoding_proof_manual
