import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import MaxMinLib.Interface

namespace Codeforces.examples_shard00.P014_1784A_monsters_easy_version.lean

open AUXLib
open MaxMinLib

def OneSingleDamage (before after : List Int) : Prop :=
  ∃ i, (0 ≤ i ∧ i < Zlength before) ∧ Znth i before 0 > 0 ∧
    Zlength after = Zlength before ∧ ∀ j, (0 ≤ j ∧ j < Zlength before) →
      Znth j after 0 = if i = j then Znth j before 0 - 1 else Znth j before 0

def SingleDamageTrace (initial final : List Int) (casts : Int) : Prop :=
  ∃ states, Zlength states = casts + 1 ∧ Znth 0 states [] = initial ∧
    Znth casts states [] = final ∧ ∀ k, (0 ≤ k ∧ k < casts) →
      OneSingleDamage (Znth k states []) (Znth (k + 1) states [])

def OneGlobalDamage (before after : List Int) : Prop :=
  List.Forall₂ (fun before_hp after_hp => after_hp = max 0 (before_hp - 1)) before after

def AMonsterDies (before after : List Int) : Prop :=
  ∃ i, (0 ≤ i ∧ i < Zlength before) ∧ Znth i before 0 > 0 ∧ Znth i after 0 = 0

def GlobalSpellCascade (initial final : List Int) : Prop :=
  ∃ states, 2 ≤ Zlength states ∧ Znth 0 states [] = initial ∧ Znth (Zlength states - 1) states [] = final ∧
    (∀ k, (0 ≤ k ∧ k < Zlength states - 1) → OneGlobalDamage (Znth k states []) (Znth (k + 1) states [])) ∧
    (∀ k, (0 ≤ k ∧ k < Zlength states - 2) → AMonsterDies (Znth k states []) (Znth (k + 1) states [])) ∧
    ¬ AMonsterDies (Znth (Zlength states - 2) states []) (Znth (Zlength states - 1) states [])

def KillsWithSingleCasts (initial : List Int) (casts : Int) : Prop :=
  ∃ before_global after_global final before_count after_count,
    SingleDamageTrace initial before_global before_count ∧
    (after_global = before_global ∨ GlobalSpellCascade before_global after_global) ∧
    SingleDamageTrace after_global final after_count ∧ Forall (fun hp => hp = 0) final ∧ casts = before_count + after_count

def Pre (health : List Int) : Prop :=
  (1 ≤ Zlength health ∧ Zlength health ≤ 200000) ∧ Forall (fun hp => 1 ≤ hp ∧ hp ≤ Zlength health) health

def Spec (health : List Int) (out : Int) : Prop :=
  min_value_of_subset (· ≤ ·) (KillsWithSingleCasts health) (fun casts => casts) out

def ZListSum : List Int → Int
  | [] => 0
  | x :: tail => x + ZListSum tail

def CascadePreparation (health prepared : List Int) : Prop :=
  Zlength prepared = Zlength health ∧
  (∀ i, (0 ≤ i ∧ i < Zlength health) → (1 ≤ Znth i prepared 0 ∧ Znth i prepared 0 ≤ Znth i health 0)) ∧
  (0 < Zlength prepared → Znth 0 prepared 0 ≤ 1) ∧
  (∀ i, (0 ≤ i ∧ i < Zlength prepared - 1) → Znth (i + 1) prepared 0 ≤ Znth i prepared 0 + 1)

def MaximalCascadePreparation (health prepared : List Int) : Prop :=
  CascadePreparation health prepared ∧ ∀ alternative, CascadePreparation health alternative →
    ∀ i, (0 ≤ i ∧ i < Zlength health) → Znth i alternative 0 ≤ Znth i prepared 0

def FullPreparationSpecBridge (original sorted : List Int) : Prop :=
  ∀ prepared, MaximalCascadePreparation sorted prepared → Spec original (ZListSum sorted - ZListSum prepared)

end Codeforces.examples_shard00.P014_1784A_monsters_easy_version.lean
