import Algorithms.lcs_n.lean.groundtruth.lcs_n_goal
import Algorithms.lcs_n.lean.groundtruth.lcs_n_proof_auto
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace Algorithms.lcs_n.lean.groundtruth.lcs_n_proof_manual

open Algorithms.lcs_n.lean
open scoped SimpleC

namespace ProofSupport

open AUXLib

-- Constructor spellings emitted by symexec for the Coq option interface.
private theorem index_bounds (n r c : Int) (hn : 0 ≤ n)
    (hr : 0 ≤ r ∧ r ≤ n) (hc : 0 ≤ c ∧ c ≤ n) :
    0 ≤ LCSNCellIndex n r c ∧ LCSNCellIndex n r c < (n+1)*(n+1) := by
  have h0 := Int.mul_nonneg hr.1 (show 0 ≤ n+1 by omega)
  have h1 := Int.mul_le_mul_of_nonneg_right hr.2 (show 0 ≤ n+1 by omega)
  unfold LCSNCellIndex
  grind

theorem lcsn_cell_index_injective__equal_write_and_row_exit (n r1 c1 r2 c2 : Int)
    (hn : 0 ≤ n) (hr1 : 0 ≤ r1 ∧ r1 ≤ n) (hc1 : 0 ≤ c1 ∧ c1 ≤ n)
    (hr2 : 0 ≤ r2 ∧ r2 ≤ n) (hc2 : 0 ≤ c2 ∧ c2 ≤ n)
    (he : LCSNCellIndex n r1 c1 = LCSNCellIndex n r2 c2) : r1 = r2 ∧ c1 = c2 := by
  unfold LCSNCellIndex at he
  by_cases hlt : r1 < r2
  · have h := Int.mul_le_mul_of_nonneg_right (show r1+1 ≤ r2 by omega) (show 0 ≤ n+1 by omega)
    grind
  · by_cases hgt : r2 < r1
    · have h := Int.mul_le_mul_of_nonneg_right (show r2+1 ≤ r1 by omega) (show 0 ≤ n+1 by omega)
      grind
    · have heq : r1 = r2 := by omega
      exact ⟨heq, by subst r2; omega⟩

theorem lcsn_Znth_replace_other_cell__equal_write_and_row_exit {A : Type} (d : A)
    (l : List A) (n ur uc qr qc : Int) (v : A) (hn : 0 ≤ n)
    (hur : 0 ≤ ur ∧ ur ≤ n) (huc : 0 ≤ uc ∧ uc ≤ n)
    (hqr : 0 ≤ qr ∧ qr ≤ n) (hqc : 0 ≤ qc ∧ qc ≤ n)
    (hl : Zlength l = (n+1)*(n+1)) (hd : ur ≠ qr ∨ uc ≠ qc) :
    Znth (LCSNCellIndex n qr qc) (replace_Znth (LCSNCellIndex n ur uc) v l) d =
      Znth (LCSNCellIndex n qr qc) l d := by
  apply Znth_replace_Znth_Diff
  · rw [hl]; exact index_bounds n ur uc hn hur huc
  · rw [hl]; exact index_bounds n qr qc hn hqr hqc
  · intro he
    have := lcsn_cell_index_injective__equal_write_and_row_exit n ur uc qr qc hn hur huc hqr hqc he
    rcases hd with h | h <;> simp_all

theorem lcsn_boundary_cell_replace_other__equal_write_and_row_exit
    (mixed : List (Option Int)) (table : List Int) (n ur uc qr qc v : Int) (hn : 0 ≤ n)
    (hur : 0 ≤ ur ∧ ur ≤ n) (huc : 0 ≤ uc ∧ uc ≤ n)
    (hqr : 0 ≤ qr ∧ qr ≤ n) (hqc : 0 ≤ qc ∧ qc ≤ n)
    (hm : Zlength mixed = (n+1)*(n+1)) (ht : Zlength table = (n+1)*(n+1))
    (hd : ur ≠ qr ∨ uc ≠ qc) (hp : LCSNBoundaryCell mixed table n qr qc) :
    LCSNBoundaryCell (replace_Znth (LCSNCellIndex n ur uc) (some v) mixed)
      (replace_Znth (LCSNCellIndex n ur uc) v table) n qr qc := by
  unfold LCSNBoundaryCell LCSNCellInitialized at *
  rw [lcsn_Znth_replace_other_cell__equal_write_and_row_exit none mixed n ur uc qr qc (some v) hn hur huc hqr hqc hm hd,
    lcsn_Znth_replace_other_cell__equal_write_and_row_exit 0 table n ur uc qr qc v hn hur huc hqr hqc ht hd]
  exact hp

private theorem boundary_write_same (mixed : List (Option Int)) (table : List Int)
    (n r c : Int) (hn : 0 ≤ n) (hr : 0 ≤ r ∧ r ≤ n) (hc : 0 ≤ c ∧ c ≤ n)
    (hm : Zlength mixed = (n+1)*(n+1)) (ht : Zlength table = (n+1)*(n+1)) :
    LCSNBoundaryCell (replace_Znth (LCSNCellIndex n r c) (some 0) mixed)
      (replace_Znth (LCSNCellIndex n r c) 0 table) n r c := by
  unfold LCSNBoundaryCell LCSNCellInitialized
  rw [Znth_replace_Znth_Same none mixed _ _ (by rw [hm]; exact index_bounds n r c hn hr hc),
    Znth_replace_Znth_Same 0 table _ _ (by rw [ht]; exact index_bounds n r c hn hr hc)]
  exact ⟨rfl, rfl⟩

theorem lcsn_column_progress_zero__column_init_update (n : Int) (hn : 0 ≤ n) :
    LCSNColumnProgress (List.replicate ((n+1)*(n+1)).toNat (none : Option Int))
      (List.replicate ((n+1)*(n+1)).toNat (0 : Int)) n 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hsq := Int.mul_nonneg (show 0 ≤ n+1 by omega) (show 0 ≤ n+1 by omega)
    simp [LCSNLogicalTableShape, Zlength, Int.toNat_of_nonneg hsq]
  · intro r hr; omega
  · intro r hr; exact Znth_repeat none _ _
  · intro r c hr hc; exact Znth_repeat none _ _

theorem lcsn_column_write_progress__column_init_update (mixed : List (Option Int))
    (table : List Int) (n i stride : Int) (hs : stride = n+1) (hn : 0 ≤ n)
    (hi : 0 ≤ i ∧ i ≤ n) (hp : LCSNColumnProgress mixed table n i) :
    LCSNColumnProgress (replace_Znth (stride*i) (some 0) mixed)
      (replace_Znth (stride*i) 0 table) n (i+1) := by
  subst stride
  have he : (n+1)*i = LCSNCellIndex n i 0 := by unfold LCSNCellIndex; grind
  rw [he]
  rcases hp with ⟨⟨hm,ht⟩, hp,hc,ho⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨by rw [Zlength_replace_Znth,hm], by rw [Zlength_replace_Znth,ht]⟩
  · intro r hr
    by_cases heq : r = i
    · subst r; exact boundary_write_same mixed table n i 0 hn hi ⟨by omega,hn⟩ hm ht
    · exact lcsn_boundary_cell_replace_other__equal_write_and_row_exit mixed table n i 0 r 0 0 hn hi ⟨by omega,hn⟩
        ⟨hr.1, by omega⟩ ⟨by omega,hn⟩ hm ht (Or.inl (Ne.symm heq)) (hp r ⟨hr.1,by omega⟩)
  · intro r hr
    unfold LCSNCellUndefined
    rw [lcsn_Znth_replace_other_cell__equal_write_and_row_exit none mixed n i 0 r 0 (some 0) hn hi ⟨by omega,hn⟩
      ⟨by omega,hr.2⟩ ⟨by omega,hn⟩ hm (Or.inl (by omega))]
    exact hc r ⟨by omega,hr.2⟩
  · intro r c hr hcol
    unfold LCSNCellUndefined
    rw [lcsn_Znth_replace_other_cell__equal_write_and_row_exit none mixed n i 0 r c (some 0) hn hi ⟨by omega,hn⟩ hr
      ⟨by omega,hcol.2⟩ hm (Or.inr (by omega))]
    exact ho r c hr hcol

theorem lcsn_column_complete_boundary_start__boundary_phase (mixed : List (Option Int))
    (table : List Int) (n : Int) (hn : 0 ≤ n) (hp : LCSNColumnProgress mixed table n (n+1)) :
    LCSNBoundaryProgress mixed table n 1 := by
  rcases hp with ⟨hs,hc,hu,ho⟩
  exact ⟨hs, fun r hr => hc r ⟨hr.1,by omega⟩, fun c hc => by omega,
    fun c hc => ho 0 c ⟨by omega,hn⟩ hc,
    fun r c hr hc => ho r c ⟨by omega,hr.2⟩ hc⟩

theorem lcsn_boundary_write_progress__boundary_phase (mixed : List (Option Int))
    (table : List Int) (n j : Int) (hj : 1 ≤ j ∧ j ≤ n)
    (hp : LCSNBoundaryProgress mixed table n j) :
    LCSNBoundaryProgress (replace_Znth j (some 0) mixed) (replace_Znth j 0 table) n (j+1) := by
  have hn : 0 ≤ n := by omega
  have he : j = LCSNCellIndex n 0 j := by simp [LCSNCellIndex]
  suffices h : LCSNBoundaryProgress (replace_Znth (LCSNCellIndex n 0 j) (some 0) mixed)
    (replace_Znth (LCSNCellIndex n 0 j) 0 table) n (j+1) by
    simpa only [LCSNCellIndex, Int.zero_mul, Int.zero_add] using h
  rcases hp with ⟨⟨hm,ht⟩,hc,hp,hs,hi⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨by rw [Zlength_replace_Znth,hm], by rw [Zlength_replace_Znth,ht]⟩
  · intro r hr
    exact lcsn_boundary_cell_replace_other__equal_write_and_row_exit mixed table n 0 j r 0 0 hn ⟨by omega,hn⟩
      ⟨by omega,hj.2⟩ hr ⟨by omega,hn⟩ hm ht (Or.inr (by omega)) (hc r hr)
  · intro c hc
    by_cases heq : c = j
    · subst c; exact boundary_write_same mixed table n 0 j hn ⟨by omega,hn⟩ ⟨by omega,hj.2⟩ hm ht
    · exact lcsn_boundary_cell_replace_other__equal_write_and_row_exit mixed table n 0 j 0 c 0 hn ⟨by omega,hn⟩
        ⟨by omega,hj.2⟩ ⟨by omega,hn⟩ ⟨by omega,by omega⟩ hm ht (Or.inr (Ne.symm heq)) (hp c ⟨hc.1,by omega⟩)
  · intro c hc
    unfold LCSNCellUndefined
    rw [lcsn_Znth_replace_other_cell__equal_write_and_row_exit none mixed n 0 j 0 c (some 0) hn ⟨by omega,hn⟩
      ⟨by omega,hj.2⟩ ⟨by omega,hn⟩ ⟨by omega,hc.2⟩ hm (Or.inr (by omega))]
    exact hs c ⟨by omega,hc.2⟩
  · intro r c hr hc
    unfold LCSNCellUndefined
    rw [lcsn_Znth_replace_other_cell__equal_write_and_row_exit none mixed n 0 j r c (some 0) hn ⟨by omega,hn⟩
      ⟨by omega,hj.2⟩ ⟨by omega,hr.2⟩ ⟨by omega,hc.2⟩ hm (Or.inl (by omega))]
    exact hi r c hr hc

theorem lcsn_boundaries_complete_rows_start__row_phase_entry (xs ys : List Int)
    (mixed : List (Option Int)) (table : List Int) (n : Int)
    (hp : LCSNBoundaryProgress mixed table n (n+1)) : LCSNRowsProgress xs ys mixed table n 1 := by
  rcases hp with ⟨hs,hc,hr,hu,hi⟩
  refine ⟨hs, ⟨hc, ?_⟩, ?_, hi⟩
  · intro c hcol
    by_cases he : c = 0
    · subst c; exact hc 0 hcol
    · exact hr c ⟨by omega,by omega⟩
  · intro r c hr hc; omega

theorem lcsn_rows_start_row__row_phase_entry (xs ys : List Int) (mixed : List (Option Int))
    (table : List Int) (n row : Int) (hr : row ≤ n)
    (hp : LCSNRowsProgress xs ys mixed table n row) : LCSNRowProgress xs ys mixed table n row 1 := by
  rcases hp with ⟨hs,hb,hc,hu⟩
  exact ⟨hs,hb,hc,fun c hc => by omega,fun c hc => hu row c ⟨by omega,hr⟩ hc,
    fun r c hr hc => hu r c ⟨by omega,hr.2⟩ hc⟩

private theorem replace_nat_as_take_drop {A : Type} (l : List A) (i : Nat) (v : A)
    (hi : i < l.length) : replace_nth i l v = l.take i ++ v :: l.drop (i+1) := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ i => simpa [replace_nth] using congrArg (List.cons a) (ih i (by simpa using hi))

theorem lcsn_replace_Znth_as_sublist__equal_write_and_row_exit {A : Type} (d : A)
    (l : List A) (k : Int) (v : A) (hk : 0 ≤ k ∧ k < Zlength l) :
    replace_Znth k v l = sublist 0 k l ++ v :: sublist (k+1) (Zlength l) l := by
  have hk' : k.toNat < l.length := by simp only [Zlength, Int.ofNat_eq_coe] at hk; omega
  simpa only [replace_Znth, sublist, Int.toNat_zero, List.drop_zero, Zlength,
    Int.ofNat_eq_coe, Int.toNat_natCast, List.take_length, show (k+1).toNat = k.toNat+1 by omega] using
    replace_nat_as_take_drop l k.toNat v hk'

theorem replace_Znth_sublist__max_write {A : Type} (l : List A) (i : Int) (v : A)
    (hi : 0 ≤ i ∧ i < Zlength l) :
    replace_Znth i v l = sublist 0 i l ++ v :: sublist (i+1) (Zlength l) l :=
  lcsn_replace_Znth_as_sublist__equal_write_and_row_exit v l i v hi

theorem lcsn_interior_cell_replace_before__equal_write_and_row_exit
    (xs ys : List Int) (mixed : List (Option Int)) (table : List Int) (n ur uc qr qc v : Int)
    (hn : 0 ≤ n) (hur : 1 ≤ ur ∧ ur ≤ n) (huc : 1 ≤ uc ∧ uc ≤ n)
    (hqr : 1 ≤ qr ∧ qr ≤ n) (hqc : 1 ≤ qc ∧ qc ≤ n)
    (hm : Zlength mixed = (n+1)*(n+1)) (ht : Zlength table = (n+1)*(n+1))
    (hb : qr < ur ∨ (qr = ur ∧ qc < uc)) (hp : LCSNInteriorCell xs ys mixed table n qr qc) :
    LCSNInteriorCell xs ys (replace_Znth (LCSNCellIndex n ur uc) (some v) mixed)
      (replace_Znth (LCSNCellIndex n ur uc) v table) n qr qc := by
  have hmread := lcsn_Znth_replace_other_cell__equal_write_and_row_exit none mixed n ur uc qr qc (some v)
    hn ⟨by omega,hur.2⟩ ⟨by omega,huc.2⟩ ⟨by omega,hqr.2⟩ ⟨by omega,hqc.2⟩ hm (by omega)
  have hread (r c : Int) (hr : 0 ≤ r ∧ r ≤ n) (hc : 0 ≤ c ∧ c ≤ n)
      (hd : ur ≠ r ∨ uc ≠ c) :=
    lcsn_Znth_replace_other_cell__equal_write_and_row_exit 0 table n ur uc r c v hn
      ⟨by omega,hur.2⟩ ⟨by omega,huc.2⟩ hr hc ht hd
  unfold LCSNInteriorCell LCSNCellInitialized LCSNCellRecurrence at *
  rw [hmread, hread qr qc ⟨by omega,hqr.2⟩ ⟨by omega,hqc.2⟩ (by omega),
    hread (qr-1) (qc-1) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by omega),
    hread (qr-1) qc ⟨by omega,by omega⟩ ⟨by omega,hqc.2⟩ (by omega),
    hread qr (qc-1) ⟨by omega,hqr.2⟩ ⟨by omega,by omega⟩ (by omega)]
  exact hp

private theorem observed_cell (xs ys : List Int) (mixed : List (Option Int)) (table : List Int)
    (n row col r c : Int) (hn : 0 ≤ n) (hrow : 1 ≤ row ∧ row ≤ n) (hcol : 1 ≤ col ∧ col ≤ n)
    (hp : LCSNRowProgress xs ys mixed table n row col)
    (hr : 0 ≤ r ∧ r ≤ n) (hc : 0 ≤ c ∧ c ≤ n)
    (hb : r < row ∨ (r = row ∧ c < col)) :
    LCSNCellInitialized mixed table n r c ∧
      (0 ≤ Znth (LCSNCellIndex n r c) table 0 ∧ Znth (LCSNCellIndex n r c) table 0 ≤ min r c) := by
  rcases hp with ⟨hs,⟨hbcol,hbrow⟩,hcomp,hpre,hsuf,hfuture⟩
  by_cases hr0 : r = 0
  · subst r
    have h := hbrow c hc
    exact ⟨h.1, by rw [h.2]; omega⟩
  · by_cases hc0 : c = 0
    · subst c
      have h := hbcol r hr
      exact ⟨h.1, by rw [h.2]; omega⟩
    · have h : LCSNInteriorCell xs ys mixed table n r c := by
        rcases hb with hb | ⟨he,hb⟩
        · exact hcomp r c ⟨by omega,hb⟩ ⟨by omega,hc.2⟩
        · subst r; exact hpre c ⟨by omega,hb⟩
      exact ⟨h.1,h.2.2⟩

theorem lcsn_diagonal_successor_bound__equal_write_and_row_exit
    (xs ys : List Int) (mixed : List (Option Int)) (table : List Int) (n row col : Int)
    (hn : 0 ≤ n) (hr : 1 ≤ row ∧ row ≤ n) (hc : 1 ≤ col ∧ col ≤ n)
    (hp : LCSNRowProgress xs ys mixed table n row col) :
    0 ≤ Znth (LCSNCellIndex n (row-1) (col-1)) table 0 + 1 ∧
      Znth (LCSNCellIndex n (row-1) (col-1)) table 0 + 1 ≤ min row col := by
  have h := (observed_cell xs ys mixed table n row col (row-1) (col-1) hn hr hc hp
    ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (Or.inl (by omega))).2
  omega

private theorem row_write (xs ys : List Int) (mixed : List (Option Int)) (table : List Int)
    (n row col v : Int) (hn : 0 ≤ n) (hr : 1 ≤ row ∧ row ≤ n) (hc : 1 ≤ col ∧ col ≤ n)
    (hp : LCSNRowProgress xs ys mixed table n row col) (hv : 0 ≤ v ∧ v ≤ min row col)
    (hrec : LCSNCellRecurrence xs ys (replace_Znth (LCSNCellIndex n row col) v table) n row col) :
    LCSNRowProgress xs ys (replace_Znth (LCSNCellIndex n row col) (some v) mixed)
      (replace_Znth (LCSNCellIndex n row col) v table) n row (col+1) := by
  rcases hp with ⟨⟨hm,ht⟩,⟨hbcol,hbrow⟩,hcomp,hpre,hsuf,hfuture⟩
  have hr0 : 0 ≤ row ∧ row ≤ n := ⟨by omega,hr.2⟩
  have hc0 : 0 ≤ col ∧ col ≤ n := ⟨by omega,hc.2⟩
  refine ⟨⟨by rw [Zlength_replace_Znth,hm],by rw [Zlength_replace_Znth,ht]⟩,⟨?_,?_⟩,?_,?_,?_,?_⟩
  · intro r hrr
    exact lcsn_boundary_cell_replace_other__equal_write_and_row_exit mixed table n row col r 0 v hn hr0 hc0 hrr
      ⟨by omega,hn⟩ hm ht (Or.inr (by omega)) (hbcol r hrr)
  · intro c hcc
    exact lcsn_boundary_cell_replace_other__equal_write_and_row_exit mixed table n row col 0 c v hn hr0 hc0
      ⟨by omega,hn⟩ hcc hm ht (Or.inl (by omega)) (hbrow c hcc)
  · intro r c hrr hcc
    exact lcsn_interior_cell_replace_before__equal_write_and_row_exit xs ys mixed table n row col r c v hn hr hc
      ⟨hrr.1,by omega⟩ hcc hm ht (Or.inl hrr.2) (hcomp r c hrr hcc)
  · intro c hcc
    by_cases he : c = col
    · subst c
      refine ⟨?_,hrec,?_⟩
      · unfold LCSNCellInitialized
        rw [Znth_replace_Znth_Same none mixed _ _ (by rw [hm]; exact index_bounds n row col hn hr0 hc0),
          Znth_replace_Znth_Same 0 table _ _ (by rw [ht]; exact index_bounds n row col hn hr0 hc0)]
      · rw [Znth_replace_Znth_Same 0 table _ _ (by rw [ht]; exact index_bounds n row col hn hr0 hc0)]
        exact hv
    · exact lcsn_interior_cell_replace_before__equal_write_and_row_exit xs ys mixed table n row col row c v hn hr hc
        hr ⟨hcc.1,by omega⟩ hm ht (Or.inr ⟨rfl,by omega⟩) (hpre c ⟨hcc.1,by omega⟩)
  · intro c hcc
    unfold LCSNCellUndefined
    rw [lcsn_Znth_replace_other_cell__equal_write_and_row_exit none mixed n row col row c (some v) hn hr0 hc0 hr0
      ⟨by omega,hcc.2⟩ hm (Or.inr (by omega))]
    exact hsuf c ⟨by omega,hcc.2⟩
  · intro r c hrr hcc
    unfold LCSNCellUndefined
    rw [lcsn_Znth_replace_other_cell__equal_write_and_row_exit none mixed n row col r c (some v) hn hr0 hc0
      ⟨by omega,hrr.2⟩ ⟨by omega,hcc.2⟩ hm (Or.inl (by omega))]
    exact hfuture r c hrr hcc

theorem lcsn_equal_write_progress__equal_write_and_row_exit
    (xs ys : List Int) (mixed : List (Option Int)) (table : List Int) (n row col : Int)
    (hn : 0 ≤ n) (hr : 1 ≤ row ∧ row ≤ n) (hc : 1 ≤ col ∧ col ≤ n)
    (he : Znth (row-1) xs 0 = Znth (col-1) ys 0)
    (hp : LCSNRowProgress xs ys mixed table n row col) :
    LCSNRowProgress xs ys (replace_Znth (LCSNCellIndex n row col)
      (some (Znth (LCSNCellIndex n (row-1) (col-1)) table 0 + 1)) mixed)
      (replace_Znth (LCSNCellIndex n row col)
        (Znth (LCSNCellIndex n (row-1) (col-1)) table 0 + 1) table) n row (col+1) := by
  apply row_write xs ys mixed table n row col _ hn hr hc hp
    (lcsn_diagonal_successor_bound__equal_write_and_row_exit xs ys mixed table n row col hn hr hc hp)
  refine Or.inr ⟨by omega,by omega,Or.inl ⟨he,?_⟩⟩
  rw [Znth_replace_Znth_Same 0 table _ _ (by rw [hp.1.2]; exact index_bounds n row col hn ⟨by omega,hr.2⟩ ⟨by omega,hc.2⟩),
    lcsn_Znth_replace_other_cell__equal_write_and_row_exit 0 table n row col (row-1) (col-1) _ hn
      ⟨by omega,hr.2⟩ ⟨by omega,hc.2⟩ ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ hp.1.2 (Or.inl (by omega))]

theorem lcsn_row_finish_progress__equal_write_and_row_exit
    (xs ys : List Int) (mixed : List (Option Int)) (table : List Int) (n row next_col : Int)
    (hn : 0 ≤ n) (hr : 1 ≤ row ∧ row ≤ n) (hc : n < next_col ∧ next_col ≤ n+1)
    (hp : LCSNRowProgress xs ys mixed table n row next_col) :
    LCSNRowsProgress xs ys mixed table n (row+1) := by
  rcases hp with ⟨hs,hb,hcomp,hpre,hsuf,hfuture⟩
  refine ⟨hs,hb,?_,hfuture⟩
  intro r c hrr hcc
  by_cases he : r = row
  · subst r; exact hpre c ⟨hcc.1,by omega⟩
  · exact hcomp r c ⟨hrr.1,by omega⟩ hcc

theorem lcsn_max_write_progress__max_write (xs ys : List Int) (mixed : List (Option Int))
    (table : List Int) (n row col : Int) (hr : 1 ≤ row ∧ row ≤ n) (hc : 1 ≤ col ∧ col ≤ n)
    (hp : LCSNRowProgress xs ys mixed table n row col)
    (hne : Znth (row-1) xs 0 ≠ Znth (col-1) ys 0) :
    LCSNRowProgress xs ys (replace_Znth (LCSNCellIndex n row col)
      (some (max (Znth (LCSNCellIndex n (row-1) col) table 0)
        (Znth (LCSNCellIndex n row (col-1)) table 0))) mixed)
      (replace_Znth (LCSNCellIndex n row col)
        (max (Znth (LCSNCellIndex n (row-1) col) table 0)
          (Znth (LCSNCellIndex n row (col-1)) table 0)) table) n row (col+1) := by
  have hn : 0 ≤ n := by omega
  have ha := (observed_cell xs ys mixed table n row col (row-1) col hn hr hc hp
    ⟨by omega,by omega⟩ ⟨by omega,hc.2⟩ (Or.inl (by omega))).2
  have hl := (observed_cell xs ys mixed table n row col row (col-1) hn hr hc hp
    ⟨by omega,hr.2⟩ ⟨by omega,by omega⟩ (Or.inr ⟨rfl,by omega⟩)).2
  apply row_write xs ys mixed table n row col _ hn hr hc hp (by omega)
  refine Or.inr ⟨by omega,by omega,Or.inr ⟨hne,?_⟩⟩
  rw [Znth_replace_Znth_Same 0 table _ _ (by rw [hp.1.2]; exact index_bounds n row col hn ⟨by omega,hr.2⟩ ⟨by omega,hc.2⟩),
    lcsn_Znth_replace_other_cell__equal_write_and_row_exit 0 table n row col (row-1) col _ hn
      ⟨by omega,hr.2⟩ ⟨by omega,hc.2⟩ ⟨by omega,by omega⟩ ⟨by omega,hc.2⟩ hp.1.2 (Or.inl (by omega)),
    lcsn_Znth_replace_other_cell__equal_write_and_row_exit 0 table n row col row (col-1) _ hn
      ⟨by omega,hr.2⟩ ⟨by omega,hc.2⟩ ⟨by omega,hr.2⟩ ⟨by omega,by omega⟩ hp.1.2 (Or.inr (by omega))]

theorem lcsn_completed_rows_result__finalize_and_return_index
    (xs ys : List Int) (mixed : List (Option Int)) (table : List Int) (n : Int)
    (hn : 0 ≤ n) (hp : LCSNRowsProgress xs ys mixed table n (n+1)) :
    LCSNTableResult xs ys n table := by
  refine ⟨hp.1.2,?_⟩
  intro r c hr hc
  by_cases hr0 : r = 0
  · subst r; exact Or.inl ⟨Or.inl rfl,(hp.2.1.2 c hc).2⟩
  · by_cases hc0 : c = 0
    · subst c; exact Or.inl ⟨Or.inr rfl,(hp.2.1.1 r hr).2⟩
    · exact (hp.2.2.1 r c ⟨by omega,by omega⟩ ⟨by omega,hc.2⟩).2.1

theorem lcsn_diagonal_observation__read_exposure (xs ys : List Int)
    (mixed : List (Option Int)) (table : List Int) (n i j : Int)
    (hi : 1 ≤ i) (hin : i ≤ n) (hj : 1 ≤ j) (hjn : j ≤ n)
    (hp : LCSNRowProgress xs ys mixed table n i j) :
    LCSNCellUndefined mixed n i j ∧ LCSNCellInitialized mixed table n (i-1) (j-1) ∧
    (0 ≤ Znth (LCSNCellIndex n (i-1) (j-1)) table 0 ∧ Znth (LCSNCellIndex n (i-1) (j-1)) table 0 ≤ n) := by
  have h := observed_cell xs ys mixed table n i j (i-1) (j-1) (by omega) ⟨hi,hin⟩ ⟨hj,hjn⟩ hp
    ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (Or.inl (by omega))
  exact ⟨hp.2.2.2.2.1 j ⟨by omega,hjn⟩, h.1, by have := h.2; omega⟩

theorem lcsn_neighbor_observations__read_exposure (xs ys : List Int)
    (mixed : List (Option Int)) (table : List Int) (n i j : Int)
    (hi : 1 ≤ i) (hin : i ≤ n) (hj : 1 ≤ j) (hjn : j ≤ n)
    (hp : LCSNRowProgress xs ys mixed table n i j) :
    LCSNCellUndefined mixed n i j ∧ LCSNCellInitialized mixed table n (i-1) j ∧
      LCSNCellInitialized mixed table n i (j-1) := by
  exact ⟨hp.2.2.2.2.1 j ⟨by omega,hjn⟩,
    (observed_cell xs ys mixed table n i j (i-1) j (by omega) ⟨hi,hin⟩ ⟨hj,hjn⟩ hp
      ⟨by omega,by omega⟩ ⟨by omega,hjn⟩ (Or.inl (by omega))).1,
    (observed_cell xs ys mixed table n i j i (j-1) (by omega) ⟨hi,hin⟩ ⟨hj,hjn⟩ hp
      ⟨by omega,hin⟩ ⟨by omega,by omega⟩ (Or.inr ⟨rfl,by omega⟩)).1⟩

theorem lcsn_initialized_mixed_full_to_full__finalize_and_return_index
    (xs ys : List Int) (mixed : List (Option Int)) (table : List Int) (n : Int)
    (hn : 0 ≤ n) (hp : LCSNRowsProgress xs ys mixed table n (n+1)) :
    mixed = table.map some := by
  apply List.ext_getElem
  · simp only [List.length_map]
    have hm := hp.1.1
    have ht := hp.1.2
    simp only [Zlength, Int.ofNat_eq_coe] at hm ht
    omega
  · intro idx hidx hmap
    have htable : idx < table.length := by simpa using hmap
    have hsquare : (idx : Int) < (n+1)*(n+1) := by
      rw [← hp.1.1]
      exact Int.ofNat_lt.mpr hidx
    let r := (idx : Int).fdiv (n+1)
    let c := (idx : Int).fmod (n+1)
    have hr0 : 0 ≤ r := Int.fdiv_nonneg (by omega) (by omega)
    have hc0 : 0 ≤ c := Int.fmod_nonneg_of_pos _ (by omega)
    have hc1 : c < n+1 := Int.fmod_lt_of_pos _ (by omega)
    have hdecomp : r*(n+1)+c = (idx : Int) := Int.fdiv_mul_add_fmod _ _
    have hr1 : r ≤ n := by
      by_cases h : r ≤ n
      · exact h
      · have hh := Int.mul_le_mul_of_nonneg_right (show n+1 ≤ r by omega) (show 0 ≤ n+1 by omega)
        omega
    have hinit : LCSNCellInitialized mixed table n r c := by
      by_cases hrz : r = 0
      · rw [hrz]; exact (hp.2.1.2 c ⟨hc0,by omega⟩).1
      · by_cases hcz : c = 0
        · rw [hcz]; exact (hp.2.1.1 r ⟨hr0,hr1⟩).1
        · exact (hp.2.2.1 r c ⟨by omega,by omega⟩ ⟨by omega,by omega⟩).1
    change Znth (r*(n+1)+c) mixed none = some (Znth (r*(n+1)+c) table 0) at hinit
    rw [hdecomp] at hinit
    simp only [Znth, Int.toNat_natCast, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hidx, List.getElem?_eq_getElem htable, Option.getD_some] at hinit
    simpa only [List.getElem_map] using hinit

end ProofSupport

open ProofSupport
open Algorithms.lcs_n.lean.groundtruth.lcs_n_goal

open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open Algorithms.lcs_n.lean.groundtruth.lcs_n_goal
open ProofSupport
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

private theorem row_bounds (n r : Int) (hn : 0 ≤ n) (hr : 0 ≤ r ∧ r ≤ n+1) :
    0 ≤ (n+1)*r ∧ (n+1)*r ≤ (n+1)*(n+1) := by
  exact ⟨Int.mul_nonneg (by omega) hr.1, Int.mul_le_mul_of_nonneg_left hr.2 (by omega)⟩

private theorem cell_bounds (n r c : Int) (hn : 0 ≤ n)
    (hr : 0 ≤ r ∧ r ≤ n) (hc : 0 ≤ c ∧ c ≤ n) :
    0 ≤ (n+1)*r+c ∧ (n+1)*r+c < (n+1)*(n+1) := by
  have h0 := Int.mul_nonneg (show 0 ≤ n+1 by omega) hr.1
  have h1 := Int.mul_le_mul_of_nonneg_left hr.2 (show 0 ≤ n+1 by omega)
  grind

private theorem sublist_nested {A : Type} (l : List A) (lo hi a b : Int)
    (hlo : 0 ≤ lo) (ha : 0 ≤ a ∧ a ≤ b) (hb : b ≤ hi-lo) :
    sublist a b (sublist lo hi l) = sublist (a+lo) (b+lo) l := by
  have hmin : lo.toNat+b.toNat ≤ hi.toNat := by omega
  simp only [sublist, List.take_drop, List.take_take, List.drop_drop,
    Nat.min_eq_left hmin]
  congr 2 <;> omega

private theorem append_cell (l : List (Option Int)) (lo k : Int)
    (hlo : 0 ≤ lo ∧ lo ≤ k) (hk : k < Zlength l) :
    sublist lo k l ++ [Znth k l none] = sublist lo (k+1) l := by
  rw [sublist_split lo (k+1) k l hlo ⟨by omega,by omega⟩,
    sublist_single none k l ⟨by omega,hk⟩]

private theorem split_mixed_cell (x lo k hi : Int) (l : List (Option Int))
    (hlo : 0 ≤ lo ∧ lo ≤ k) (hk : k < hi) (hhi : hi ≤ Zlength l) :
    intArray.mixed_seg x lo hi (sublist lo hi l) |--
      intArray.mixed_seg x lo k (sublist lo k l) **
      intArray.mixedstoreA x k (Znth k l none) **
      intArray.mixed_seg x (k+1) hi (sublist (k+1) hi l) := by
  sep_apply (intArray.mixed_seg_split_to_mixed_seg x lo k hi (sublist lo hi l) ⟨hlo.2,by omega⟩)
  rw [sublist_nested l lo hi 0 (k-lo) hlo.1 ⟨by omega,by omega⟩ (by omega),
    sublist_nested l lo hi (k-lo) (hi-lo) hlo.1 ⟨by omega,by omega⟩ (by omega)]
  simp only [Int.zero_add, Int.sub_add_cancel]
  sep_apply (intArray.mixed_seg_split_to_mixed_seg x k (k+1) hi (sublist k hi l) ⟨by omega,by omega⟩)
  rw [sublist_nested l k hi 0 (k+1-k) (by omega) ⟨by omega,by omega⟩ (by omega),
    sublist_nested l k hi (k+1-k) (hi-k) (by omega) ⟨by omega,by omega⟩ (by omega)]
  simp only [Int.zero_add, Int.sub_add_cancel]
  rw [sublist_single none k l ⟨by omega,by omega⟩]
  sep_apply ((intArray.mixed_seg_unfold x k (k+1) ([] : List (Option Int)) (Znth k l none)).1)
  sep_apply ((intArray.mixed_seg_empty x (k+1) (k+1)).1)
  Intros_p he
  cancel


private theorem read_prefix (x k : Int) (l : List (Option Int)) (v : Int)
    (hk : 0 ≤ k ∧ k < Zlength l) (hv : Znth k l none = some v) :
    intArray.mixed_seg x 0 k (sublist 0 k l) **
      ((x + k * sizeof(INT)) # Int |-> v) |--
    intArray.mixed_seg x 0 (k+1) (sublist 0 (k+1) l) := by
  have hs := intArray.mixed_seg_single x k (some v)
  change ((x + k * sizeof(INT)) # Int |-> v) |--
    intArray.mixed_seg x k (k+1) [some v] at hs
  sep_apply hs
  sep_apply (intArray.mixed_seg_merge_to_mixed_seg x 0 k (k+1) (sublist 0 k l) [some v] ⟨hk.1,by omega⟩)
  rw [← hv, append_cell l 0 k ⟨by omega,hk.1⟩ hk.2]
  cancel

private theorem join_written_full (x k total : Int) (l : List (Option Int)) (v : Int)
    (hk : 0 ≤ k ∧ k < total) (hl : Zlength l = total) :
    intArray.mixed_seg x 0 k (sublist 0 k l) **
      ((x + k * sizeof(INT)) # Int |-> v) **
      intArray.mixed_seg x (k+1) total (sublist (k+1) total l) |--
    intArray.mixed_full x total (replace_Znth k (some v) l) := by
  have hs := intArray.mixed_seg_single x k (some v)
  change ((x + k * sizeof(INT)) # Int |-> v) |--
    intArray.mixed_seg x k (k+1) [some v] at hs
  sep_apply hs
  sep_apply (intArray.mixed_seg_merge_to_mixed_seg x 0 k (k+1) (sublist 0 k l) [some v] ⟨hk.1,by omega⟩)
  sep_apply (intArray.mixed_seg_merge_to_mixed_full x 0 (k+1) total
    (sublist 0 k l ++ [some v]) (sublist (k+1) total l) ⟨by omega,by omega⟩)
  simp only [Int.zero_mul,Int.add_zero,Int.sub_zero]
  have he : (sublist 0 k l ++ [some v]) ++ sublist (k+1) total l = replace_Znth k (some v) l := by
    rw [replace_Znth_sublist__max_write l k (some v) ⟨hk.1,by omega⟩,hl]
    simp only [List.append_assoc,List.singleton_append]
  rw [he]
  cancel


private theorem expose_some (x k v : Int) :
    intArray.mixedstoreA x k (some v) |-- ((x + k * sizeof(INT)) # Int |-> v) := by
  exact naive_C_Rules.toContext.derivable1_refl _

private theorem expose_none (x k : Int) :
    intArray.mixedstoreA x k none |-- intArray.undef_seg x k (k+1) := by
  exact intArray.undef_seg_single x k

private theorem cell_properties (x v : Int) :
    (x # Int |-> v) |-- “(isvalidptr_int x ∧ v ≤ Int.max_signed ∧ v ≥ Int.min_signed)” := by
  exact naive_C_Rules.toContext.derivable1_andp_elim1 _ _


theorem proof_of_lcs_n_entail_wit_1 : lcs_n_entail_wit_1 := by
  unfold lcs_n_entail_wit_1
  right
  intro table_pre n_pre ys xs PreH1 PreH2 PreH3 PreH4
  have hp := lcsn_column_progress_zero__column_init_update n_pre PreH1
  have hsq := row_bounds n_pre 0 PreH1 ⟨by omega,by omega⟩
  Exists (List.replicate ((n_pre+1)*(n_pre+1)).toNat (none : Option Int))
    (List.replicate ((n_pre+1)*(n_pre+1)).toNat (0 : Int))
  split_pure_spatial
  · sep_apply (intArray.undef_full_to_mixed_full table_pre ((n_pre+1)*(n_pre+1)))
    cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_lcs_n_entail_wit_2_split_goal_1 : lcs_n_entail_wit_2_split_goal_1 := by
  unfold lcs_n_entail_wit_2_split_goal_1
  intro n_pre ys xs mixed_table table_l i stride PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have h := cell_bounds n_pre i 0 (by omega) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  omega

theorem proof_of_lcs_n_entail_wit_2 : lcs_n_entail_wit_2 := by
  unfold lcs_n_entail_wit_2
  right
  intro n_pre ys xs mixed_table table_l i stride PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have h := cell_bounds n_pre i 0 (by omega) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  aggressive_pre_process
  all_goals try dump_pre_spatial
  all_goals first | omega | int_auto

theorem proof_of_lcs_n_entail_wit_3 : lcs_n_entail_wit_3 := by
  unfold lcs_n_entail_wit_3
  right
  intro n_pre ys xs mixed_table_2 table_l_2 i stride PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hp := lcsn_column_write_progress__column_init_update mixed_table_2 table_l_2 n_pre i stride PreH6 PreH7 ⟨PreH11,PreH5⟩ PreH15
  have hr := row_bounds n_pre (i+1) PreH7 ⟨by omega,by omega⟩
  Exists (replace_Znth (stride*i) (0 : Int) table_l_2)
  rw [PreH6] at hp
  rw [PreH9,PreH6]
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_lcs_n_entail_wit_4 : lcs_n_entail_wit_4 := by
  unfold lcs_n_entail_wit_4
  right
  intro n_pre ys xs mixed_table_2 table_l_2 i stride PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have he : i = n_pre+1 := by omega
  have hp := lcsn_column_complete_boundary_start__boundary_phase mixed_table_2 table_l_2 n_pre PreH3 (by simpa [he] using PreH11)
  Exists table_l_2
  rw [PreH5]
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_lcs_n_entail_wit_6 : lcs_n_entail_wit_6 := by
  unfold lcs_n_entail_wit_6
  right
  intro n_pre ys xs mixed_table_2 table_l_2 j stride PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hp := lcsn_boundary_write_progress__boundary_phase mixed_table_2 table_l_2 n_pre j ⟨PreH13,PreH7⟩ PreH15
  Exists (replace_Znth j (0 : Int) table_l_2)
  rw [PreH11]
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_lcs_n_entail_wit_7 : lcs_n_entail_wit_7 := by
  unfold lcs_n_entail_wit_7
  right
  intro n_pre ys xs mixed_table_2 table_l_2 j stride PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have he : j = n_pre+1 := by omega
  have hp := lcsn_boundaries_complete_rows_start__row_phase_entry xs ys mixed_table_2 table_l_2 n_pre (by simpa [he] using PreH9)
  have hr := row_bounds n_pre 1 PreH3 ⟨by omega,by omega⟩
  Exists table_l_2
  rw [PreH5]
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_lcs_n_entail_wit_8 : lcs_n_entail_wit_8 := by
  unfold lcs_n_entail_wit_8
  right
  intro n_pre ys xs mixed_table_2 table_l_2 i stride PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have hp := lcsn_rows_start_row__row_phase_entry xs ys mixed_table_2 table_l_2 n_pre i PreH1 PreH11
  have hr := cell_bounds n_pre i 1 PreH3 ⟨by omega,PreH1⟩ ⟨by omega,by omega⟩
  Exists table_l_2
  rw [PreH5]
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_lcs_n_entail_wit_9_split_goal_1 : lcs_n_entail_wit_9_split_goal_1 := by
  unfold lcs_n_entail_wit_9_split_goal_1
  intro n_pre ys xs mixed_table table_l j i stride PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have h := cell_bounds n_pre (i - 1) (j) (by omega) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  omega

theorem proof_of_lcs_n_entail_wit_9_split_goal_2 : lcs_n_entail_wit_9_split_goal_2 := by
  unfold lcs_n_entail_wit_9_split_goal_2
  intro n_pre ys xs mixed_table table_l j i stride PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have h := cell_bounds n_pre (i - 1) (j - 1) (by omega) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  omega

theorem proof_of_lcs_n_entail_wit_9_split_goal_3 : lcs_n_entail_wit_9_split_goal_3 := by
  unfold lcs_n_entail_wit_9_split_goal_3
  intro n_pre ys xs mixed_table table_l j i stride PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have h := cell_bounds n_pre (i) (j) (by omega) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  omega

theorem proof_of_lcs_n_entail_wit_9 : lcs_n_entail_wit_9 := by
  unfold lcs_n_entail_wit_9
  right
  intro n_pre ys xs mixed_table table_l j i stride PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have h1 := cell_bounds n_pre (i - 1) (j) (by omega) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  have h2 := cell_bounds n_pre (i - 1) (j - 1) (by omega) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  have h3 := cell_bounds n_pre (i) (j) (by omega) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  aggressive_pre_process
  all_goals try dump_pre_spatial
  all_goals first | omega | int_auto

theorem proof_of_lcs_n_entail_wit_10_1 : lcs_n_entail_wit_10_1 := by
  unfold lcs_n_entail_wit_10_1
  right
  intro table_pre n_pre ys xs mixed_table_2 table_l_2 j i stride mixed_table_3 table_l_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  subst stride
  rw [PreH33] at PreH1 PreH2 PreH3 PreH4 ⊢
  let total := (n_pre+1)*(n_pre+1)
  let current := (n_pre+1)*i+j
  have hcb := cell_bounds n_pre i j PreH31 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  let diag := (n_pre+1)*(i-1)+(j-1)
  let value := Znth diag table_l_3 0 + 1
  have hdb := cell_bounds n_pre (i-1) (j-1) PreH31 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  have hdc : diag+1 ≤ current := by dsimp [diag,current]; grind
  have hlen := PreH9.1.1
  have hp := lcsn_equal_write_progress__equal_write_and_row_exit xs ys mixed_table_3 table_l_3 n_pre i j
    PreH31 ⟨PreH5,PreH6⟩ ⟨PreH7,PreH8⟩ PreH14 PreH9
  have hprogress : LCSNRowProgress xs ys (replace_Znth current (some value) mixed_table_3)
      (replace_Znth current value table_l_3) n_pre i (j+1) := by
    simpa only [LCSNCellIndex,Int.mul_comm,current,value,diag] using hp
  sep_apply (read_prefix table_pre diag mixed_table_3 (Znth diag table_l_3 0) ⟨hdb.1,by omega⟩ PreH11)
  sep_apply (intArray.mixed_seg_merge_to_mixed_seg table_pre 0 (diag+1) current
    (sublist 0 (diag+1) mixed_table_3) (sublist (diag+1) current mixed_table_3) ⟨by omega,hdc⟩)
  rw [← sublist_split 0 current (diag+1) mixed_table_3 ⟨by omega,by omega⟩ ⟨hdc,by omega⟩]
  sep_apply (join_written_full table_pre current total mixed_table_3 value hcb hlen)
  Exists (replace_Znth current (some value) mixed_table_3) (replace_Znth current value table_l_3)
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | trivial | assumption | omega

theorem proof_of_lcs_n_entail_wit_10_2 : lcs_n_entail_wit_10_2 := by
  unfold lcs_n_entail_wit_10_2
  right
  intro table_pre n_pre ys xs mixed_table_2 table_l_2 j i stride mixed_table_3 table_l_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  subst stride
  rw [PreH33] at PreH1 PreH2 PreH3 PreH4 PreH5 ⊢
  let total := (n_pre+1)*(n_pre+1)
  let current := (n_pre+1)*i+j
  have hcb := cell_bounds n_pre i j PreH31 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  let above := (n_pre+1)*(i-1)+j
  let left := (n_pre+1)*i+(j-1)
  let value := Znth above table_l_3 0
  have hab := cell_bounds n_pre (i-1) j PreH31 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  have hlb := cell_bounds n_pre i (j-1) PreH31 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  have hal : above+1 ≤ left := by dsimp [above,left]; grind
  have hlc : left+1 = current := by dsimp [left,current]; omega
  have hlen := PreH10.1.1
  have hp := lcsn_max_write_progress__max_write xs ys mixed_table_3 table_l_3 n_pre i j
    ⟨PreH6,PreH7⟩ ⟨PreH8,PreH9⟩ PreH10 PreH14
  have hmax : max (Znth above table_l_3 0) (Znth left table_l_3 0) = value := by
    exact Int.max_eq_left PreH5
  have hprogress : LCSNRowProgress xs ys (replace_Znth current (some value) mixed_table_3)
      (replace_Znth current value table_l_3) n_pre i (j+1) := by
    have hp' : LCSNRowProgress xs ys
        (replace_Znth current (some (max (Znth above table_l_3 0) (Znth left table_l_3 0))) mixed_table_3)
        (replace_Znth current (max (Znth above table_l_3 0) (Znth left table_l_3 0)) table_l_3) n_pre i (j+1) := by
      simpa only [LCSNCellIndex,Int.mul_comm,current,above,left] using hp
    simpa only [hmax] using hp'
  sep_apply (read_prefix table_pre above mixed_table_3 (Znth above table_l_3 0) ⟨hab.1,by omega⟩ PreH12)
  sep_apply (intArray.mixed_seg_merge_to_mixed_seg table_pre 0 (above+1) left
    (sublist 0 (above+1) mixed_table_3) (sublist (above+1) left mixed_table_3) ⟨by omega,hal⟩)
  rw [← sublist_split 0 left (above+1) mixed_table_3 ⟨by omega,by omega⟩ ⟨hal,by omega⟩]
  sep_apply (read_prefix table_pre left mixed_table_3 (Znth left table_l_3 0) ⟨hlb.1,by omega⟩ PreH13)
  rw [hlc]
  sep_apply (join_written_full table_pre current total mixed_table_3 value hcb hlen)
  Exists (replace_Znth current (some value) mixed_table_3) (replace_Znth current value table_l_3)
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | trivial | assumption | omega

theorem proof_of_lcs_n_entail_wit_10_3 : lcs_n_entail_wit_10_3 := by
  unfold lcs_n_entail_wit_10_3
  right
  intro table_pre n_pre ys xs mixed_table_2 table_l_2 j i stride mixed_table_3 table_l_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  subst stride
  rw [PreH33] at PreH1 PreH2 PreH3 PreH4 PreH5 ⊢
  let total := (n_pre+1)*(n_pre+1)
  let current := (n_pre+1)*i+j
  have hcb := cell_bounds n_pre i j PreH31 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  let above := (n_pre+1)*(i-1)+j
  let left := (n_pre+1)*i+(j-1)
  let value := Znth left table_l_3 0
  have hab := cell_bounds n_pre (i-1) j PreH31 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  have hlb := cell_bounds n_pre i (j-1) PreH31 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  have hal : above+1 ≤ left := by dsimp [above,left]; grind
  have hlc : left+1 = current := by dsimp [left,current]; omega
  have hlen := PreH10.1.1
  have hp := lcsn_max_write_progress__max_write xs ys mixed_table_3 table_l_3 n_pre i j
    ⟨PreH6,PreH7⟩ ⟨PreH8,PreH9⟩ PreH10 PreH14
  have hmax : max (Znth above table_l_3 0) (Znth left table_l_3 0) = value := by
    exact Int.max_eq_right (Int.le_of_lt PreH5)
  have hprogress : LCSNRowProgress xs ys (replace_Znth current (some value) mixed_table_3)
      (replace_Znth current value table_l_3) n_pre i (j+1) := by
    have hp' : LCSNRowProgress xs ys
        (replace_Znth current (some (max (Znth above table_l_3 0) (Znth left table_l_3 0))) mixed_table_3)
        (replace_Znth current (max (Znth above table_l_3 0) (Znth left table_l_3 0)) table_l_3) n_pre i (j+1) := by
      simpa only [LCSNCellIndex,Int.mul_comm,current,above,left] using hp
    simpa only [hmax] using hp'
  sep_apply (read_prefix table_pre above mixed_table_3 (Znth above table_l_3 0) ⟨hab.1,by omega⟩ PreH12)
  sep_apply (intArray.mixed_seg_merge_to_mixed_seg table_pre 0 (above+1) left
    (sublist 0 (above+1) mixed_table_3) (sublist (above+1) left mixed_table_3) ⟨by omega,hal⟩)
  rw [← sublist_split 0 left (above+1) mixed_table_3 ⟨by omega,by omega⟩ ⟨hal,by omega⟩]
  sep_apply (read_prefix table_pre left mixed_table_3 (Znth left table_l_3 0) ⟨hlb.1,by omega⟩ PreH13)
  rw [hlc]
  sep_apply (join_written_full table_pre current total mixed_table_3 value hcb hlen)
  Exists (replace_Znth current (some value) mixed_table_3) (replace_Znth current value table_l_3)
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | trivial | assumption | omega

theorem proof_of_lcs_n_entail_wit_12 : lcs_n_entail_wit_12 := by
  unfold lcs_n_entail_wit_12
  right
  intro n_pre ys xs mixed_table_2 table_l_2 j i stride PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hp := lcsn_row_finish_progress__equal_write_and_row_exit xs ys mixed_table_2 table_l_2 n_pre i j PreH3 ⟨PreH7,PreH8⟩ ⟨PreH1,PreH10⟩ PreH13
  have hr := row_bounds n_pre (i+1) PreH3 ⟨by omega,by omega⟩
  Exists table_l_2
  rw [PreH5]
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_lcs_n_entail_wit_13 : lcs_n_entail_wit_13 := by
  unfold lcs_n_entail_wit_13
  right
  intro table_pre n_pre ys xs mixed_table_2 table_l_2 i stride PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have he : i = n_pre+1 := by omega
  have hp : LCSNRowsProgress xs ys mixed_table_2 table_l_2 n_pre (n_pre+1) := by simpa [he] using PreH11
  have hres := lcsn_completed_rows_result__finalize_and_return_index xs ys mixed_table_2 table_l_2 n_pre PreH3 hp
  have hm := lcsn_initialized_mixed_full_to_full__finalize_and_return_index xs ys mixed_table_2 table_l_2 n_pre PreH3 hp
  Exists mixed_table_2 table_l_2
  split_pure_spatial
  · rw [hm]
    sep_apply (intArray.mixed_full_to_full table_pre ((n_pre+1)*(n_pre+1)) table_l_2)
    cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_lcs_n_entail_wit_14_split_goal_1 : lcs_n_entail_wit_14_split_goal_1 := by
  unfold lcs_n_entail_wit_14_split_goal_1
  intro n_pre ys xs mixed_table table_l stride PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have h := cell_bounds n_pre n_pre n_pre (by omega) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  omega

theorem proof_of_lcs_n_entail_wit_14 : lcs_n_entail_wit_14 := by
  unfold lcs_n_entail_wit_14
  right
  intro n_pre ys xs mixed_table table_l stride PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have h := cell_bounds n_pre n_pre n_pre (by omega) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  aggressive_pre_process
  all_goals try dump_pre_spatial
  all_goals first | omega | int_auto

theorem proof_of_lcs_n_which_implies_wit_1 : lcs_n_which_implies_wit_1 := by
  unfold lcs_n_which_implies_wit_1
  right
  intro n_pre ys xs table_l_2 mixed_table_2 i j table PreH1 PreH2 PreH3 PreH4 PreH5
  have hn : 0 ≤ n_pre := by omega
  have hlen := PreH5.1.1
  let total := (n_pre+1)*(n_pre+1)
  let current := (n_pre+1)*i+j
  have hcb := cell_bounds n_pre i j hn ⟨by omega,PreH2⟩ ⟨by omega,PreH4⟩
  let diag := (n_pre+1)*(i-1)+(j-1)
  have hdb := cell_bounds n_pre (i-1) (j-1) hn ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  have hdc : diag+1 ≤ current := by dsimp [diag,current]; grind
  have hobs := lcsn_diagonal_observation__read_exposure xs ys mixed_table_2 table_l_2 n_pre i j PreH1 PreH2 PreH3 PreH4 PreH5
  rcases hobs with ⟨hcur,hdiag,hval⟩
  have hcur' : Znth current mixed_table_2 none = none := by
    simpa only [LCSNCellUndefined,LCSNCellIndex,Int.mul_comm,current] using hcur
  have hdiag' : Znth diag mixed_table_2 none = some (Znth diag table_l_2 0) := by
    simpa only [LCSNCellInitialized,LCSNCellIndex,Int.mul_comm,diag] using hdiag
  have hval' : 0 ≤ Znth diag table_l_2 0 ∧ Znth diag table_l_2 0 ≤ n_pre := by
    simpa only [LCSNCellIndex,Int.mul_comm,diag] using hval
  dsimp [diag,current] at hcur' hdiag' hval'
  have hsplit := split_mixed_cell table 0 diag total mixed_table_2 ⟨by omega,hdb.1⟩ hdb.2 (by omega)
  rw [sublist_self mixed_table_2 total (by exact hlen.symm)] at hsplit
  sep_apply (intArray.mixed_full_to_mixed_seg table total mixed_table_2)
  sep_apply hsplit
  sep_apply (split_mixed_cell table (diag+1) current total mixed_table_2 ⟨by omega,hdc⟩ hcb.2 (by omega))
  rw [hdiag',hcur']
  sep_apply (expose_none table current)
  sep_apply (expose_some table diag (Znth diag table_l_2 0))
  prop_apply (cell_properties (table+diag*sizeof(INT)) (Znth diag table_l_2 0))
  Intros_p hprop
  Exists mixed_table_2 table_l_2
  split_pure_spatial
  · pre_process
    all_goals cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals try assumption
    all_goals try omega

theorem proof_of_lcs_n_which_implies_wit_2 : lcs_n_which_implies_wit_2 := by
  unfold lcs_n_which_implies_wit_2
  right
  intro n_pre ys xs table_l_2 mixed_table_2 i j table PreH1 PreH2 PreH3 PreH4 PreH5
  have hn : 0 ≤ n_pre := by omega
  have hlen := PreH5.1.1
  let total := (n_pre+1)*(n_pre+1)
  let current := (n_pre+1)*i+j
  have hcb := cell_bounds n_pre i j hn ⟨by omega,PreH2⟩ ⟨by omega,PreH4⟩
  let above := (n_pre+1)*(i-1)+j
  let left := (n_pre+1)*i+(j-1)
  have hab := cell_bounds n_pre (i-1) j hn ⟨by omega,by omega⟩ ⟨by omega,PreH4⟩
  have hlb := cell_bounds n_pre i (j-1) hn ⟨by omega,PreH2⟩ ⟨by omega,by omega⟩
  have hal : above+1 ≤ left := by dsimp [above,left]; grind
  have hlc : left+1 = current := by dsimp [left,current]; omega
  have hobs := lcsn_neighbor_observations__read_exposure xs ys mixed_table_2 table_l_2 n_pre i j PreH1 PreH2 PreH3 PreH4 PreH5
  rcases hobs with ⟨hcur,ha,hl⟩
  have hcur' : Znth current mixed_table_2 none = none := by
    simpa only [LCSNCellUndefined,LCSNCellIndex,Int.mul_comm,current] using hcur
  have ha' : Znth above mixed_table_2 none = some (Znth above table_l_2 0) := by
    simpa only [LCSNCellInitialized,LCSNCellIndex,Int.mul_comm,above] using ha
  have hl' : Znth left mixed_table_2 none = some (Znth left table_l_2 0) := by
    simpa only [LCSNCellInitialized,LCSNCellIndex,Int.mul_comm,left] using hl
  dsimp [above,left,current] at hcur' ha' hl'
  have hsplit := split_mixed_cell table 0 above total mixed_table_2 ⟨by omega,hab.1⟩ hab.2 (by omega)
  rw [sublist_self mixed_table_2 total (by exact hlen.symm)] at hsplit
  sep_apply (intArray.mixed_full_to_mixed_seg table total mixed_table_2)
  sep_apply hsplit
  sep_apply (split_mixed_cell table (above+1) left total mixed_table_2 ⟨by omega,hal⟩ hlb.2 (by omega))
  sep_apply (split_mixed_cell table (left+1) current total mixed_table_2 ⟨by omega,by omega⟩ hcb.2 (by omega))
  rw [ha',hl',hcur',hlc]
  rw [Zsublist_nil mixed_table_2 current current (by omega)]
  sep_apply ((intArray.mixed_seg_empty table current current).1)
  Intros_p he
  sep_apply (expose_none table current)
  sep_apply (expose_some table above (Znth above table_l_2 0))
  sep_apply (expose_some table left (Znth left table_l_2 0))
  prop_apply (cell_properties (table+above*sizeof(INT)) (Znth above table_l_2 0))
  Intros_p haprop
  prop_apply (cell_properties (table+left*sizeof(INT)) (Znth left table_l_2 0))
  Intros_p hlprop
  Exists mixed_table_2 table_l_2
  split_pure_spatial
  · pre_process
    all_goals cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals try assumption
    all_goals try omega

end Algorithms.lcs_n.lean.groundtruth.lcs_n_proof_manual
