Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition ValidBusLoading (groups : list Z) (capacity : Z) (cuts : list Z) : Prop :=
  2 <= Zlength cuts /\
  Znth 0 cuts 0 = 0 /\
  Znth (Zlength cuts - 1) cuts 0 = Zlength groups /\
  mono_inc cuts /\
  (forall k, 0 <= k < Zlength cuts - 1 ->
     fold_right Z.add 0
       (sublist (Znth k cuts 0) (Znth (k + 1) cuts 0) groups) <= capacity).

Definition Pre (capacity : Z) (groups : list Z) : Prop :=
  1 <= Zlength groups <= 100 /\
  1 <= capacity <= 100 /\
  Forall (fun size => 1 <= size <= capacity) groups.

Definition Spec (capacity : Z) (groups : list Z) (out : Z) : Prop :=
  min_value_of_subset Z.le (ValidBusLoading groups capacity)
    (fun cuts => Zlength cuts - 1) out.
