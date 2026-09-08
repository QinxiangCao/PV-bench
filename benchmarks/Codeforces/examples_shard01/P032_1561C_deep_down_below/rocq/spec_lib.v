(* Codeforces 1561/C - Deep Down Below: the hero clears every cave in some order,
   gaining 1 power per monster beaten; find the least starting power that works. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Starting power 'power' suffices, via an order of the caves:
     order is a permutation of 1..|caves|      each cave entered exactly once
     for the ci-th visited cave c and its j-th monster,
       power + (sum of |caves| visited before ci) + j  >  c[j]
   the hero's power being his start plus one per monster already beaten, and it
   must strictly exceed the armor of the monster he now faces. *)
Definition CaveOrderWorks (caves : list (list Z)) (power : Z) : Prop :=
  exists order : list Z, (Permutation order (Zrange 1 ((Zlength caves) + 1))) /\
    forall ci j, 0 <= ci < Zlength caves ->
      0 <= j < Zlength (Znth (Znth ci order 1 - 1) caves []) ->
      power + sum_range 0 (ci - 1)
        (fun q => Zlength (Znth (Znth q order 1 - 1) caves [])) + j >
      Znth j (Znth (Znth ci order 1 - 1) caves []) 0.
Definition Pre (caves : list (list Z)) : Prop :=
  (* Every clause below is stated explicitly in the P032 solver Require, which
     therefore omits the Pre(caves) call:
       1 <= Zlength caves <= 100000 /\
       Forall
         (fun c =>
            1 <= Zlength c <= 100000 /\
            Forall (fun x => 1 <= x <= 1000000000) c)
         caves /\
       Zlength (concat caves) <= 100000. *)
  True.

(* out = min { power : CaveOrderWorks caves power }. *)
Definition Spec (caves : list (list Z)) (out : Z) : Prop := (min_value_of_subset Z.le (CaveOrderWorks caves) (fun x => x)) out.

(* Representation bridge for the normalized solver, which receives one cave per
   entry of two parallel arrays instead of the jagged cave contents: gains[i] is
   cave i's monster count, and requirements[i] is the least power that clears
   cave i, characterized as an upper bound of a_{i,j} + 1 - j that some j
   attains.  Well defined because every cave is non-empty. *)
Definition CaveSummaryBridge
    (caves : list (list Z)) (requirements gains : list Z) : Prop :=
  Zlength requirements = Zlength caves /\
  Zlength gains = Zlength caves /\
  forall i, 0 <= i < Zlength caves ->
    Znth i gains 0 = Zlength (Znth i caves []) /\
    (forall j, 0 <= j < Zlength (Znth i caves []) ->
       Znth j (Znth i caves []) 0 + 1 - j <= Znth i requirements 0) /\
    (exists j, 0 <= j < Zlength (Znth i caves []) /\
       Znth i requirements 0 = Znth j (Znth i caves []) 0 + 1 - j).
