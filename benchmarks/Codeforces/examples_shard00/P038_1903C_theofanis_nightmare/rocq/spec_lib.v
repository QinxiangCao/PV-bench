Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition Zmap_range {A : Type} (f : Z -> A) (n : Z) : list A :=
  map f (Zrange 0 n).

Definition DivisionValue (a cuts : list Z) (value : Z) : Prop :=
  2 <= Zlength cuts /\ Znth 0 cuts 0 = 0 /\
  Znth (Zlength cuts - 1) cuts 0 = Zlength a /\
  mono_inc cuts /\
  value = fold_right Z.add 0
    (Zmap_range (fun i => (i + 1) * fold_right Z.add 0
      (sublist (Znth i cuts 0) (Znth (i + 1) cuts 0) a))
      (Zlength cuts - 1)).

Definition Pre (a : list Z) : Prop :=
  1 <= Zlength a <= 100000 /\ Forall (fun x => -100000000 <= x <= 100000000) a.

Definition Spec (a : list Z) (out : Z) : Prop :=
  max_value_of_subset Z.le
    (fun candidate : list Z * Z =>
      DivisionValue a (fst candidate) (snd candidate))
    snd out.
