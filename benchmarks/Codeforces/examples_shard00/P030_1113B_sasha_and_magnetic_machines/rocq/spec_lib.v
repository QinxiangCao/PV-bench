Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition OneMagneticTransfer (before after : list Z) : Prop :=
  after = before \/
  exists i j x,
    0 <= i < Zlength before /\ 0 <= j < Zlength before /\ i <> j /\
    x > 0 /\ (x | Znth i before 0) /\
    Zlength after = Zlength before /\
    forall k, 0 <= k < Zlength before ->
      Znth k after 0 =
        if Z.eqb k i then Znth k before 0 / x
        else if Z.eqb k j then Znth k before 0 * x
        else Znth k before 0.

Definition TotalPower (a : list Z) : Z := fold_right Z.add 0 a.

Definition Pre (a : list Z) : Prop :=
  2 <= Zlength a <= 50000 /\
  Forall (fun power => 1 <= power <= 100) a.

Definition Spec (a : list Z) (out : Z) : Prop :=
  min_value_of_subset Z.le (OneMagneticTransfer a) TotalPower out.
