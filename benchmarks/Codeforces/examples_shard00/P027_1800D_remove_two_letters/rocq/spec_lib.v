Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition ObtainedByRemovingTwo (s result : list Z) : Prop :=
  exists i, 0 <= i < Zlength s - 1 /\
    result = sublist 0 i s ++ sublist (i + 2) (Zlength s) s.

Definition Pre (s : list Z) : Prop :=
  3 <= Zlength s <= 200000 /\
  Forall (fun c => 97 <= c <= 122) s.

#[local] Instance finite_lowercase : Finite (fun c : Z => 97 <= c < 123) :=
  finite_Z_range 97 123.

#[local] Instance finite_result_string (size : Z) :
    Finite (fun result : list Z =>
      Zlength result = size /\ Forall (fun c => 97 <= c < 123) result) :=
  Finite_bounded_lists size (fun c : Z => 97 <= c < 123).

Definition Spec (s : list Z) (out : Z) : Prop :=
  out = #(fun result : list Z =>
    (Zlength result = Zlength s - 2 /\
     Forall (fun c => 97 <= c < 123) result) /\
    ObtainedByRemovingTwo s result).
