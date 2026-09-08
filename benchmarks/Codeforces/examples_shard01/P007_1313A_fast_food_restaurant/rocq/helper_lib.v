Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import PVbench.Codeforces.examples_shard01.P007_1313A_fast_food_restaurant.rocq.spec_lib.

Import ListNotations.
Local Open Scope Z_scope.

(* The seven low bits of [mask] are the characteristic set of menu kinds.
   These predicates describe the finite set being considered, the prefix of
   menu kinds already counted, and the corresponding mathematical optimum. *)
Definition SelectedByMask (mask kind : Z) : Prop :=
  Z.testbit mask (kind - 1) = true.

Definition FamilyPrefix
    (mask next cnt need_a need_b need_c : Z) : Prop :=
  cnt = #(fun kind : Z =>
            1 <= kind < next /\ SelectedByMask mask kind) /\
  need_a = #(fun kind : Z =>
               1 <= kind < next /\ SelectedByMask mask kind /\ UsesA kind) /\
  need_b = #(fun kind : Z =>
               1 <= kind < next /\ SelectedByMask mask kind /\ UsesB kind) /\
  need_c = #(fun kind : Z =>
               1 <= kind < next /\ SelectedByMask mask kind /\ UsesC kind).

(* While the ingredients of the selected current kind [kind] are scanned,
   [ingredient] is the number of ingredient positions already accounted for.
   Earlier kinds are fully accounted for, whereas the current kind contributes
   to A/B/C after positions 0/1/2 respectively have been processed. *)
Definition DishPrefix
    (mask kind ingredient cnt need_a need_b need_c : Z) : Prop :=
  cnt = #(fun k : Z =>
            1 <= k < kind + 1 /\ SelectedByMask mask k) /\
  need_a = #(fun k : Z =>
               1 <= k < kind + 1 /\ SelectedByMask mask k /\ UsesA k /\
               (k < kind \/ 0 < ingredient)) /\
  need_b = #(fun k : Z =>
               1 <= k < kind + 1 /\ SelectedByMask mask k /\ UsesB k /\
               (k < kind \/ 1 < ingredient)) /\
  need_c = #(fun k : Z =>
               1 <= k < kind + 1 /\ SelectedByMask mask k /\ UsesC k /\
               (k < kind \/ 2 < ingredient)).

Definition MaskFeeds (a b c mask guests : Z) : Prop :=
  guests = #(fun kind : Z =>
               1 <= kind < 8 /\ SelectedByMask mask kind) /\
  #(fun kind : Z =>
      1 <= kind < 8 /\ SelectedByMask mask kind /\ UsesA kind) <= a /\
  #(fun kind : Z =>
      1 <= kind < 8 /\ SelectedByMask mask kind /\ UsesB kind) <= b /\
  #(fun kind : Z =>
      1 <= kind < 8 /\ SelectedByMask mask kind /\ UsesC kind) <= c.

Definition FeedsBeforeMask (a b c next guests : Z) : Prop :=
  guests = 0 \/
  exists mask, 0 <= mask < next /\ MaskFeeds a b c mask guests.

Definition BestBeforeMask (a b c next best : Z) : Prop :=
  max_value_of_subset Z.le
    (FeedsBeforeMask a b c next) (fun x => x) best.

(* Append-only repair: the implementation numbers a menu kind by its three
   ingredient bits.  The original [UsesA]/[UsesB]/[UsesC] declarations above
   use a different sequential enumeration, so the implementation-facing
   predicates below state the bit-mask semantics explicitly. *)
Definition UsesAByBits (kind : Z) : Prop :=
  Z.testbit kind 0 = true.

Definition UsesBByBits (kind : Z) : Prop :=
  Z.testbit kind 1 = true.

Definition UsesCByBits (kind : Z) : Prop :=
  Z.testbit kind 2 = true.

Definition FamilyPrefixByBits
    (mask next cnt need_a need_b need_c : Z) : Prop :=
  cnt = #(fun kind : Z =>
            1 <= kind < next /\ SelectedByMask mask kind) /\
  need_a = #(fun kind : Z =>
               1 <= kind < next /\ SelectedByMask mask kind /\
               UsesAByBits kind) /\
  need_b = #(fun kind : Z =>
               1 <= kind < next /\ SelectedByMask mask kind /\
               UsesBByBits kind) /\
  need_c = #(fun kind : Z =>
               1 <= kind < next /\ SelectedByMask mask kind /\
               UsesCByBits kind).

Definition DishPrefixByBits
    (mask kind ingredient cnt need_a need_b need_c : Z) : Prop :=
  cnt = #(fun k : Z =>
            1 <= k < kind + 1 /\ SelectedByMask mask k) /\
  need_a = #(fun k : Z =>
               1 <= k < kind + 1 /\ SelectedByMask mask k /\
               UsesAByBits k /\ (k < kind \/ 0 < ingredient)) /\
  need_b = #(fun k : Z =>
               1 <= k < kind + 1 /\ SelectedByMask mask k /\
               UsesBByBits k /\ (k < kind \/ 1 < ingredient)) /\
  need_c = #(fun k : Z =>
               1 <= k < kind + 1 /\ SelectedByMask mask k /\
               UsesCByBits k /\ (k < kind \/ 2 < ingredient)).

Definition MaskFeedsByBits (a b c mask guests : Z) : Prop :=
  guests = #(fun kind : Z =>
               1 <= kind < 8 /\ SelectedByMask mask kind) /\
  #(fun kind : Z =>
      1 <= kind < 8 /\ SelectedByMask mask kind /\ UsesAByBits kind) <= a /\
  #(fun kind : Z =>
      1 <= kind < 8 /\ SelectedByMask mask kind /\ UsesBByBits kind) <= b /\
  #(fun kind : Z =>
      1 <= kind < 8 /\ SelectedByMask mask kind /\ UsesCByBits kind) <= c.

Definition FeedsBeforeMaskByBits (a b c next guests : Z) : Prop :=
  guests = 0 \/
  exists mask, 0 <= mask < next /\ MaskFeedsByBits a b c mask guests.

Definition BestBeforeMaskByBits (a b c next best : Z) : Prop :=
  max_value_of_subset Z.le
    (FeedsBeforeMaskByBits a b c next) (fun x => x) best.

(* The inner ingredient loop is entered only for a kind selected by the
   current family mask.  Package that branch fact with the dish-prefix state
   so every inner-loop entry, step, and exit uses one complete interface. *)
Definition SelectedDishPrefixByBits
    (mask kind ingredient cnt need_a need_b need_c : Z) : Prop :=
  SelectedByMask mask kind /\
  DishPrefixByBits mask kind ingredient cnt need_a need_b need_c.

