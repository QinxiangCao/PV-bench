Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition LeftAction : Z * Z := (-1, 0).

Definition RightAction : Z * Z := (1, 0).

Definition PrintAction (x : Z) : Z * Z := (0, x).

Definition LeftWalkPlan (k p : Z) : list (Z * Z) :=
  repeat LeftAction (Z.to_nat (k - p)).

Definition RightWalkPlan (k p : Z) : list (Z * Z) :=
  repeat RightAction (Z.to_nat (p - k)).

Definition ForwardSweepPlan (s : list Z) (next : Z) : list (Z * Z) :=
  flat_map (fun p =>
    PrintAction (Znth (p - 1) s 0) ::
    if Z_lt_dec p (Zlength s) then RightAction :: nil else nil)
    (Zrange 1 next).

Definition BackwardSweepPlan (s : list Z) (next : Z) : list (Z * Z) :=
  flat_map (fun p =>
    PrintAction (Znth (p - 1) s 0) ::
    if Z_lt_dec 1 p then LeftAction :: nil else nil)
    (rev (Zrange (next + 1) (Zlength s + 1))).

Definition LeftFirstPlan (k : Z) (s : list Z) : list (Z * Z) :=
  LeftWalkPlan k 1 ++ ForwardSweepPlan s (Zlength s + 1).

Definition RightFirstPlan (k : Z) (s : list Z) : list (Z * Z) :=
  RightWalkPlan k (Zlength s) ++ BackwardSweepPlan s 0.
