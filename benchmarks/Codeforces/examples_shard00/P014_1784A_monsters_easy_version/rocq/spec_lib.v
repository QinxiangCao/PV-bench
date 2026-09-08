Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.

Local Open Scope Z_scope.

Definition OneSingleDamage (before after : list Z) : Prop :=
  exists i,
    0 <= i < Zlength before /\ Znth i before 0 > 0 /\
    Zlength after = Zlength before /\
    forall j, 0 <= j < Zlength before ->
      Znth j after 0 = if Z.eqb i j then Znth j before 0 - 1 else Znth j before 0.

Definition SingleDamageTrace (initial final : list Z) (casts : Z) : Prop :=
  exists states,
    Zlength states = casts + 1 /\
    Znth 0 states [] = initial /\
    Znth casts states [] = final /\
    forall k, 0 <= k < casts ->
      OneSingleDamage (Znth k states []) (Znth (k + 1) states []).

Definition OneGlobalDamage (before after : list Z) : Prop :=
  Forall2
    (fun before_hp after_hp => after_hp = Z.max 0 (before_hp - 1))
    before after.

Definition AMonsterDies (before after : list Z) : Prop :=
  exists i, 0 <= i < Zlength before /\
    Znth i before 0 > 0 /\ Znth i after 0 = 0.

Definition GlobalSpellCascade (initial final : list Z) : Prop :=
  exists states,
    2 <= Zlength states /\
    Znth 0 states [] = initial /\
    Znth (Zlength states - 1) states [] = final /\
    (forall k, 0 <= k < Zlength states - 1 ->
       OneGlobalDamage (Znth k states []) (Znth (k + 1) states [])) /\
    (forall k, 0 <= k < Zlength states - 2 ->
       AMonsterDies (Znth k states []) (Znth (k + 1) states [])) /\
    ~ AMonsterDies (Znth (Zlength states - 2) states [])
                   (Znth (Zlength states - 1) states []).

Definition KillsWithSingleCasts (initial : list Z) (casts : Z) : Prop :=
  exists before_global after_global final before_count after_count,
    SingleDamageTrace initial before_global before_count /\
    (after_global = before_global \/ GlobalSpellCascade before_global after_global) /\
    SingleDamageTrace after_global final after_count /\
    Forall (fun hp => hp = 0) final /\
    casts = before_count + after_count.

Definition Pre (health : list Z) : Prop :=
  1 <= Zlength health <= 200000 /\
  Forall (fun hp => 1 <= hp <= Zlength health) health.

Definition Spec (health : list Z) (out : Z) : Prop :=
  min_value_of_subset Z.le (KillsWithSingleCasts health)
    (fun casts => casts) out.

Fixpoint ZListSum (xs : list Z) : Z :=
  match xs with
  | [] => 0
  | x :: tail => x + ZListSum tail
  end.

Definition CascadePreparation (health prepared : list Z) : Prop :=
  Zlength prepared = Zlength health /\
  (forall i, 0 <= i < Zlength health ->
     1 <= Znth i prepared 0 <= Znth i health 0) /\
  (0 < Zlength prepared -> Znth 0 prepared 0 <= 1) /\
  (forall i, 0 <= i < Zlength prepared - 1 ->
     Znth (i + 1) prepared 0 <= Znth i prepared 0 + 1).

Definition MaximalCascadePreparation (health prepared : list Z) : Prop :=
  CascadePreparation health prepared /\
  forall alternative,
    CascadePreparation health alternative ->
    forall i, 0 <= i < Zlength health ->
      Znth i alternative 0 <= Znth i prepared 0.

Definition FullPreparationSpecBridge (original sorted : list Z) : Prop :=
  forall prepared,
    MaximalCascadePreparation sorted prepared ->
    Spec original (ZListSum sorted - ZListSum prepared).
