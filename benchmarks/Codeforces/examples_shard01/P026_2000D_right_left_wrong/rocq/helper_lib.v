Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Import SetsNotation.
Local Open Scope sets.
Local Open Scope Z_scope.

(* A mathematical prefix-sum profile.  [pref] may be a proper prefix of the
   complete profile while the C loop is still filling its work array. *)
Definition PrefixSumsPrefix (a pref : list Z) : Prop :=
  1 <= Zlength pref <= Zlength a + 1 /\
  forall i, 0 <= i < Zlength pref ->
    Znth i pref 0 = sum_range 0 (i - 1) (fun k => Znth k a 0).

Definition PrefixSums (a pref : list Z) : Prop :=
  Zlength pref = Zlength a + 1 /\
  forall i, 0 <= i <= Zlength a ->
    Znth i pref 0 = sum_range 0 (i - 1) (fun k => Znth k a 0).

Definition PairScore (a : list Z) (pairs : list (Z * Z)) : Z :=
  fold_right
    (fun p acc =>
       sum_range (fst p) (snd p) (fun i => Znth i a 0) + acc)
    0 pairs.

(* [pairs] lists already chosen endpoint pairs from outside to inside.  The
   frontier clauses say precisely which L endpoints lie to the left of [l]
   and which R endpoints lie to the right of [r]; the order clause makes the
   finite pairing independent of any particular implementation. *)
Definition OrderedGreedyPairs
    (s : list Z) (l r : Z) (pairs : list (Z * Z)) : Prop :=
  Forall
    (fun p =>
       0 <= fst p < snd p /\ snd p < Zlength s /\
       Znth (fst p) s 0 = 76 /\ Znth (snd p) s 0 = 82 /\
       fst p < l /\ r < snd p)
  pairs /\
  (forall i j,
     0 <= i /\ i < j /\ j < Zlength pairs ->
     fst (Znth i pairs (0, 0)) < fst (Znth j pairs (0, 0)) /\
     snd (Znth j pairs (0, 0)) < snd (Znth i pairs (0, 0))) /\
  (forall i, 0 <= i < l ->
     (Znth i s 0 = 76 <-> In i (map fst pairs))) /\
  (forall i, r < i < Zlength s ->
     (Znth i s 0 = 82 <-> In i (map snd pairs))).

Definition GreedyProgress
    (a s : list Z) (l r score : Z) : Prop :=
  exists pairs,
    OrderedGreedyPairs s l r pairs /\
    score = PairScore a pairs.
