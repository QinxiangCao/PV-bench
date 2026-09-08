
Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import Coq.Sorting.Permutation.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Require Import AUXLib.ListLib.

Local Open Scope Z_scope.

(** [LowerBoundResult xs x r] gives the mathematical meaning of a lower-bound
    search.  It deliberately describes the partition around [r], rather than
    the binary-search control flow used to find it. *)
Definition LowerBoundResult (xs : list Z) (x r : Z) : Prop :=
  0 <= r <= Zlength xs /\
  (forall i, 0 <= i < r -> Znth i xs 0 < x) /\
  (forall i, r <= i < Zlength xs -> x <= Znth i xs 0).

Definition CompareResult (x y out : Z) : Prop :=
  (x < y /\ out = -1) \/
  (x = y /\ out = 0) \/
  (y < x /\ out = 1).

Definition KeyAt (keys : list Z) (x index : Z) : Prop :=
  0 <= index < Zlength keys /\ Znth index keys 0 = x.

(** [UniqueKeys values keys] says that [keys] is a duplicate-free table for
    exactly the values occurring in [values]. *)
Definition UniqueKeys (values keys : list Z) : Prop :=
  increasing keys /\
  (forall i, 0 <= i < Zlength values ->
    exists j, 0 <= j < Zlength keys /\
      Znth i values 0 = Znth j keys 0) /\
  (forall j, 0 <= j < Zlength keys ->
    exists i, 0 <= i < Zlength values /\
      Znth j keys 0 = Znth i values 0) /\
  (forall p q,
    0 <= p < Zlength keys ->
    0 <= q < Zlength keys ->
    Znth p keys 0 = Znth q keys 0 -> p = q).

(** The processed prefix of the sorted input has already been compressed into
    the leading [used] cells of [storage]. *)
Definition CompressionState
    (sorted : list Z) (processed used : Z) (storage : list Z) : Prop :=
  0 <= processed <= Zlength sorted /\
  0 <= used <= processed /\
  Zlength storage = Zlength sorted /\
  UniqueKeys (sublist 0 processed sorted) (sublist 0 used storage) /\
  (forall i, processed - 1 <= i < Zlength sorted ->
    Znth i storage 0 = Znth i sorted 0).

Definition FrequencyProfile
    (values : list Z) (lo hi : Z) (keys counts : list Z) : Prop :=
  Zlength counts = Zlength keys /\
  0 <= lo <= hi /\ hi <= Zlength values /\
  forall j, 0 <= j < Zlength keys ->
    Znth j counts 0 =
      #(fun i : Z => lo <= i < hi /\
        Znth i values 0 = Znth j keys 0).

Definition RightBuildState
    (values : list Z) (processed : Z) (keys counts : list Z) : Prop :=
  FrequencyProfile values 0 processed keys counts.

(** At loop position [middle], [left] counts the strict prefix, [right]
    counts the current suffix, and [answer] counts exactly the completed
    triples whose middle index is already in the strict prefix. *)
Definition CountingState
    (k : Z) (values : list Z) (middle : Z)
    (keys left right : list Z) (answer : Z) : Prop :=
  FrequencyProfile values 0 middle keys left /\
  FrequencyProfile values middle (Zlength values) keys right /\
  answer = #(fun q : Z * (Z * Z) =>
    (0 <= fst q < Zlength values /\
     0 <= fst (snd q) < Zlength values /\
     0 <= snd (snd q) < Zlength values) /\
    fst (snd q) < middle /\
    fst q < fst (snd q) /\ fst (snd q) < snd (snd q) /\
    Znth (fst (snd q)) values 0 = Znth (fst q) values 0 * k /\
    Znth (snd (snd q)) values 0 =
      Znth (fst (snd q)) values 0 * k).
