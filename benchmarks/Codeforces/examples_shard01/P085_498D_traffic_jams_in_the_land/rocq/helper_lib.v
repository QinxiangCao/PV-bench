Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import PVbench.Codeforces.examples_shard01.P085_498D_traffic_jams_in_the_land.rocq.spec_lib.

Import ListNotations.
Local Open Scope Z_scope.

Fixpoint cross (ps : list Z) (t : Z) : Z :=
  match ps with
  | [] => t
  | p :: rest => cross rest (if Z.eqb (t mod p) 0 then t + 2 else t + 1)
  end.

(* Time spent in a block, as a function of the arrival time. *)

Definition delta (ps : list Z) (r : Z) : Z := cross ps r - r.

(* The road periods the statement allows; every one of them divides 60, which
   is why [delta ps] only depends on the arrival time modulo 60. *)

Definition PeriodsOK (ps : list Z) : Prop := Forall (fun p => 2 <= p <= 6) ps.

(* The block of periods a tree node covering the C segments [lo, hi] owns.
   [arr] mirrors a_[1..n], so C segment j is [Znth (j - 1) arr]. *)

Definition NodeSlice (arr : list Z) (lo hi : Z) : list Z := sublist (lo - 1) hi arr.

(* --- tree geometry ------------------------------------------------- *)

(* A node index [v] together with the range [lo, hi] it covers fits inside the
   400020 rows of seg[][] when the subtree below it is shallow enough.  The
   witness [k] bounds that depth: a range of length at most 2 ^ k has a subtree
   whose largest index is below (v + 1) * 2 ^ k. *)

Definition NodeFits (v lo hi : Z) : Prop :=
  1 <= v /\ 1 <= lo /\ lo <= hi /\
  exists k : Z, 0 <= k /\ hi - lo + 1 <= 2 ^ k /\ (v + 1) * 2 ^ k <= 400020.

(* [InSub v lo hi u a b]: the node [u], covering [a, b], is [v] itself or one
   of its descendants in the tree rooted at [v] over [lo, hi]. *)

Inductive InSub : Z -> Z -> Z -> Z -> Z -> Z -> Prop :=
| InSub_self : forall v lo hi, InSub v lo hi v lo hi
| InSub_left : forall v lo hi u a b,
    lo < hi -> InSub (2 * v) lo ((lo + hi) / 2) u a b -> InSub v lo hi u a b
| InSub_right : forall v lo hi u a b,
    lo < hi -> InSub (2 * v + 1) ((lo + hi) / 2 + 1) hi u a b -> InSub v lo hi u a b.

Definition NodeIn (v lo hi u : Z) : Prop := exists a b, InSub v lo hi u a b.

(* --- the stored tables --------------------------------------------- *)

(* Row [v] of seg[][] holds the travel times of the block [ps]: every one of
   the 60 residues is already written and carries the right value. *)

Definition RowIs (cells : list (list (option Z))) (v : Z) (ps : list Z) : Prop :=
  forall r, 0 <= r < 60 -> Znth r (Znth v cells []) None = Some (delta ps r).

(* The same statement restricted to the residues below [k]: what one of the
   60-iteration loops has established so far. *)

Definition RowPrefixIs
    (cells : list (list (option Z))) (v : Z) (ps : list Z) (k : Z) : Prop :=
  forall r, 0 <= r < k -> Znth r (Znth v cells []) None = Some (delta ps r).

(* Every node of the subtree rooted at [v] stores the table of the block it
   covers.  This is the invariant the tree maintains. *)

Definition TreeOK
    (cells : list (list (option Z))) (arr : list Z) (v lo hi : Z) : Prop :=
  forall u a b, InSub v lo hi u a b -> RowIs cells u (NodeSlice arr a b).

(* Frames.  [pull] rewrites exactly one row, [build] and [update] rewrite only
   rows belonging to the subtree they were called on. *)

Definition RowsAgreeExcept
    (v : Z) (cells cells' : list (list (option Z))) : Prop :=
  forall u, u <> v -> Znth u cells' [] = Znth u cells [].

Definition CellsAgreeOutside
    (v lo hi : Z) (cells cells' : list (list (option Z))) : Prop :=
  forall u, ~ NodeIn v lo hi u -> Znth u cells' [] = Znth u cells [].

(* The rectangular shape of seg[][] as a pure fact; [mixed_full] only reports
   the outer length, and the frozen Ensure asks for the row lengths too. *)

Definition CellsShaped (cells : list (list (option Z))) : Prop :=
  Zlength cells = 400020 /\
  forall i, 0 <= i < 400020 -> Zlength (Znth i cells []) = 60.

(* Two roads that differ in at most one segment: what a 'C' query does. *)

Definition AgreeExceptIdx (k : Z) (arr0 arr : list Z) : Prop :=
  Zlength arr0 = Zlength arr /\
  forall j, 0 <= j -> j <> k -> Znth j arr0 0 = Znth j arr 0.

(* --- solver loop state --------------------------------------------- *)

(* The first [i] queries have been replayed on [states]. *)

Definition QueryStepsOK
    (qs : list TrafficQuery) (states : list (list Z)) (i : Z) : Prop :=
  forall j, 0 <= j < i -> QueryStep qs states j.

(* Every 'A' query among the first [i] has already contributed its answer at
   the position the printed list gives it. *)

Definition AnswersOK
    (qs : list TrafficQuery) (states : list (list Z)) (answers : list Z) (i : Z) : Prop :=
  forall j, 0 <= j < i ->
    let ' (c, x, y) := Znth j qs (0, 0, 0) in c = 65 ->
    exists t, RideTime (Znth j states []) x y t /\ Znth (AskCount qs j) answers 0 = t.

(* --- two computation lemmas that pin the definitions down ----------- *)

Definition QuerySlice (arr : list Z) (lo hi ql qr : Z) : list Z :=
  NodeSlice arr (Z.max lo ql) (Z.min hi qr).

Definition TreeStaleAt (cells : list (list (option Z))) (arr : list Z)
    (v lo hi pos : Z) : Prop :=
  exists arr0, AgreeExceptIdx (pos - 1) arr0 arr /\ TreeOK cells arr0 v lo hi.
