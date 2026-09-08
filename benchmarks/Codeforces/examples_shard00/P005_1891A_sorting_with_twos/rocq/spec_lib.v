Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import Coq.Relations.Relation_Operators.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition PowerOfTwoPrefix (len n : Z) : Prop :=
  exists m : Z, 0 <= m /\ len = Z.pow 2 m /\ len <= n.

Definition OnePrefixDecrement (before after : list Z) : Prop :=
  exists len,
    PowerOfTwoPrefix len (Zlength before) /\
    Zlength after = Zlength before /\
    forall i, 0 <= i < Zlength before ->
      Znth i after 0 = if i <? len then Znth i before 0 - 1 else Znth i before 0.

Definition Pre (a : list Z) : Prop :=
  1 <= Zlength a <= 20 /\
  Forall (fun x => 0 <= x <= 1000) a.

Definition Spec (a : list Z) (out : Z) : Prop :=
  (out = 0 \/ out = 1) /\
  (out = 1 <-> exists final,
    clos_refl_trans OnePrefixDecrement a final /\ mono_nondec final).
