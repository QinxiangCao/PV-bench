Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition DistanceArray (a b : list Z) : Prop :=
  Zlength b = Zlength a /\
  forall i, 0 <= i < Zlength a ->
    min_value_of_subset Z.le
      (fun j : Z =>
        0 <= j < Zlength a /\ Znth j a 0 <> Znth i a 0)
      (fun j => Z.abs (i-j)) (Znth i b 0).

Definition UsesEveryValue (k : Z) (a : list Z) : Prop :=
  Forall (fun x => 1 <= x <= k) a /\
  forall x, 1 <= x <= k -> In x a.

Definition Pre (n k : Z) : Prop :=
  2 <= n <= 200000 /\ 2 <= k <= Z.min n 10.

#[export] Instance finite_distance (n : Z) : Finite (fun d : Z => 0 <= d < n) :=
  finite_Z_range 0 n.

#[export] Instance finite_distance_array (n : Z) :
    Finite (fun b : list Z =>
      Zlength b = n /\ Forall (fun d => 0 <= d < n) b) :=
  Finite_bounded_lists n (fun d : Z => 0 <= d < n).

Definition Spec (n k out : Z) : Prop :=
  out = #(fun b : list Z =>
    (Zlength b = n /\ Forall (fun d => 0 <= d < n) b) /\
    exists a, Zlength a = n /\ UsesEveryValue k a /\ DistanceArray a b)
    mod 998244353.

Require Import Coq.micromega.Lia.

(* Compatibility realization for the frozen [Extern Coq] identifier. *)
Definition Zmin : Z -> Z -> Z := Z.min.

(* Canonical run-length profiles.  The first run may have length two, while
   every subsequently completed non-final run uses the unique representation
   in which length two has been split into two singleton runs. *)
Definition P082CoreCarrier (size runs : Z) (parts : list Z) : Prop :=
  Zlength parts = runs /\ Forall (fun x => 1 <= x < size + 1) parts.

Definition P082CoreComposition (size runs : Z) (parts : list Z) : Prop :=
  P082CoreCarrier size runs parts /\
  fold_right Z.add 0 parts = size /\
  forall t, 1 <= t < runs -> Znth t parts 0 <> 2.

#[export] Instance P082_finite_part_value (size : Z) :
  Finite (fun x : Z => 1 <= x < size + 1) :=
  finite_Z_range 1 (size + 1).

#[export] Instance P082_finite_core_carrier (size runs : Z) :
  Finite (P082CoreCarrier size runs) :=
  Finite_bounded_lists runs (fun x : Z => 1 <= x < size + 1).

#[export] Instance P082_finite_core_composition (size runs : Z) :
  Finite (P082CoreComposition size runs) :=
  Finite_subset (P082CoreCarrier size runs)
    (fun parts => fold_right Z.add 0 parts = size /\
      forall t, 1 <= t < runs -> Znth t parts 0 <> 2).

Require Import Coq.Sorting.Permutation.

From SumLib Require Import ZRect.
