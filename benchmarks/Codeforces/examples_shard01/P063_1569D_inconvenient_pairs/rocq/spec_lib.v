(* Codeforces 1569/D - Inconvenient Pairs: count the pairs of persons whose
   shortest route along the streets is strictly longer than their Manhattan
   distance. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SumLib.ZRect.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Point p stands on a street: its x is one of the vertical streets' xs, or its y
   is one of the horizontal streets' ys. *)
Definition OnStreet (xs ys : list Z) (p : Z * Z) : Prop := In (fst p) xs \/ In (snd p) ys.

(* p and q are joined by one straight move along a single street: same x, which is
   a vertical street, or same y, which is a horizontal street. *)
Definition StreetSegment (xs ys : list Z) (p q : Z * Z) : Prop :=
  (fst p = fst q /\ In (fst p) xs) \/ (snd p = snd q /\ In (snd p) ys).

(* The distance between two points when travelling in a straight line. *)
Definition Manhattan (p q : Z * Z) : Z :=
  Z.abs (fst p - fst q) + Z.abs (snd p - snd q).

(* [path] runs from [p] to [q], every step along one street. *)
Definition StreetWalk (xs ys : list Z) (p q : Z * Z) (path : list (Z * Z)) : Prop :=
  path <> [] /\
  Znth 0 path (0, 0) = p /\
  Znth (Zlength path - 1) path (0, 0) = q /\
  forall i, 0 <= i < Zlength path - 1 ->
    StreetSegment xs ys (Znth i path (0, 0)) (Znth (i + 1) path (0, 0)).

(* How far one walks along it. *)
Definition WalkLength (path : list (Z * Z)) : Z :=
  sum_range 0 (Zlength path - 2)
    (fun i => Manhattan (Znth i path (0, 0)) (Znth (i + 1) path (0, 0))).

(* d is the length of a shortest street walk from p to q. *)
Definition StreetDistance (xs ys : list Z) (p q : Z * Z) (d : Z) : Prop :=
  min_value_of_subset Z.le
    (fun v => exists path, StreetWalk xs ys p q path /\ v = WalkLength path)
    (fun x => x) d.
Definition Pre (xs ys : list Z) (people : list (Z * Z)) : Prop :=
  (* Stated explicitly in the P063 solver Require, so dropped here:
       2 <= Zlength xs <= 200000 /\
       2 <= Zlength ys <= 200000 /\
       2 <= Zlength people <= 300000 /\
     and the coordinate half of the clause below, whose on-a-street half stays:
       Forall (fun p => 0 <= fst p <= 1000000 /\ 0 <= snd p <= 1000000 /\ OnStreet xs ys p) people *)
  Forall (fun p => OnStreet xs ys p) people /\
  mono_inc xs /\
  mono_inc ys /\
  Znth 0 xs 0 = 0 /\
  Znth (Zlength xs - 1) xs 0 = 1000000 /\
  Znth 0 ys 0 = 0 /\
  Znth (Zlength ys - 1) ys 0 = 1000000 /\
  NoDup people.

(* A pair is inconvenient when the shortest way along the streets is strictly
   longer than going straight. *)
Definition Inconvenient (xs ys : list Z) (p q : Z * Z) : Prop :=
  exists d, StreetDistance xs ys p q d /\ d > Manhattan p q.

(* Count the unordered pairs of persons that are inconvenient. *)
Definition Spec (xs ys : list Z) (people : list (Z * Z)) (out : Z) : Prop :=
  out = #(fun ij : Z * Z =>
            0 <= fst ij < Zlength people /\
            0 <= snd ij < Zlength people /\
            fst ij < snd ij /\
            Inconvenient xs ys
              (Znth (fst ij) people (0, 0)) (Znth (snd ij) people (0, 0))).
