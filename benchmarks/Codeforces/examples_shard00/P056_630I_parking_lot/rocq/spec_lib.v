Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition BeautifulParking (n : Z) (cars : list Z) : Prop :=
  Zlength cars = 2 * n - 2 /\
  Forall (fun c => 1 <= c <= 4) cars /\
  exists i make, 0 <= i /\ i + n <= Zlength cars /\
    (forall j, i <= j < i + n -> Znth j cars 0 = make) /\
    (i = 0 \/ Znth (i - 1) cars 0 <> make) /\
    (i + n = Zlength cars \/ Znth (i + n) cars 0 <> make).

Definition Pre (n : Z) : Prop :=
  3 <= n <= 30.

#[local] Instance finite_car_make : Finite (fun c : Z => 1 <= c < 5) :=
  finite_Z_range 1 5.

#[local] Instance finite_filling (n : Z) :
    Finite (fun cars : list Z =>
      Zlength cars = 2 * n - 2 /\ Forall (fun c => 1 <= c < 5) cars) :=
  Finite_bounded_lists (2 * n - 2) (fun c : Z => 1 <= c < 5).

Definition Spec (n out : Z) : Prop :=
  out = #(fun cars : list Z =>
    (Zlength cars = 2 * n - 2 /\ Forall (fun c => 1 <= c < 5) cars) /\
    BeautifulParking n cars).
