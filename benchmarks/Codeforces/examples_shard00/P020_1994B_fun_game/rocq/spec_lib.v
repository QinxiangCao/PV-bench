Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import Coq.Relations.Relation_Operators.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

(* Character codes: '0' = 48, '1' = 49. *)
Definition BinaryCharacterXor (x y : Z) : Z :=
  if Z.eqb x y then 48 else 49.

Definition OneGameAction (before after : list Z) : Prop :=
  exists l r,
    0 <= l <= r /\ r < Zlength before /\
    Zlength after = Zlength before /\
    forall i, 0 <= i < Zlength before ->
      Znth i after 0 =
        if andb (l <=? i) (i <=? r)
        then BinaryCharacterXor (Znth i before 48) (Znth (i - l) before 48)
        else Znth i before 0.

Definition Pre (s t : list Z) : Prop :=
  1 <= Zlength s <= 200000 /\
  Zlength t = Zlength s /\
  Forall (fun c => c = 48 \/ c = 49) s /\
  Forall (fun c => c = 48 \/ c = 49) t.

Definition Spec (s t : list Z) (out : Z) : Prop :=
  (out = 0 \/ out = 1) /\
  (out = 1 <-> clos_refl_trans OneGameAction s t).
