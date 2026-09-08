(* Codeforces 959/C - Mahmoud and Ehab and the wrong algorithm: print an n-node
   tree on which the even/odd-depth heuristic for minimum vertex cover is wrong,
   and one on which it is right, using -1 for a section that has no such tree. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import SimpleC.EE.LLM_bench.Codeforces.GraphInstances.
Require Import GraphLib.reachable.vpath.
Require Import GraphLib.reachable.reachable_basic.

Import ListNotations.
Local Open Scope Z_scope.

(* sel is a vertex cover: a set of vertices within [1, n] containing at least one
   endpoint of every edge. *)
Definition VertexCover (n : Z) (e : list (Z * Z)%type) (sel : Z -> Prop) : Prop :=
  (forall x, sel x -> 1 <= x <= n) /\
  forall q, In q e -> sel (fst q) \/ sel (snd q).

(* v is the true answer: the least size of a vertex cover of e. *)
Definition MinCoverSize (n : Z) (e : list (Z * Z)%type) (v : Z) : Prop :=
  min_value_of_subset Z.le
    (fun z => exists s, VertexCover n e s /\ z = #(fun x : Z => 1 <= x < n + 1 /\ s x))
    (fun x => x) v.

(* v is the heuristic's answer: rooting at 1 and letting d(x) be the depth of x,
   the least length of a simple path from 1 to x,
     v = min( #{ x in 1..n : d(x) even },  #{ x in 1..n : d(x) odd } ) *)
Definition RootParityCount (n : Z) (e : list (Z * Z)%type) (v : Z) : Prop :=
  exists d : Z -> Z, (forall x, 1 <= x <= n ->
  min_value_of_subset Z.le
    (fun q => exists path,
      (1 <= 1 <= n /\ 1 <= x <= n /\
  valid_vpath ({| zv := fun y => 1 <= y <= n ; ze := fun y z => In (y, z) e \/ In (z, y) e|} : ZGraph) 1 path x /\ NoDup path) /\ q = Zlength path - 1)
    (fun q => q) (d x)) /\
    v = Z.min (#(fun x : Z => 1 <= x < n + 1 /\ Z.even (d x) = true))
            (#(fun x : Z => 1 <= x < n + 1 /\ Z.even (d x) = false)).

(* e is a tree on n nodes -- |e| = n - 1, endpoints in [1, n], no self-loop, no
   edge repeated in either direction, connected -- on which the heuristic's answer
   differs from the true minimum cover size. *)
Definition WrongTree (n : Z) (e : list (Z * Z)%type) : Prop :=
  (Zlength e = n - 1 /\ (Forall (fun p => 1 <= fst p <= n /\ 1 <= snd p <= n /\ fst p <> snd p) e /\
  forall p q, In p e -> In q e ->
    (p = q \/ p = (snd q, fst q)) -> p = q) /\
  (connected ({| zv := fun x => 1 <= x <= n ; ze := fun x y => In (x, y) e \/ In (y, x) e|} : ZGraph))) /\ exists a b, RootParityCount n e a /\ MinCoverSize n e b /\ a <> b.

(* The same, except the heuristic's answer equals the true minimum cover size. *)
Definition CorrectTree (n : Z) (e : list (Z * Z)%type) : Prop :=
  (Zlength e = n - 1 /\ (Forall (fun p => 1 <= fst p <= n /\ 1 <= snd p <= n /\ fst p <> snd p) e /\
  forall p q, In p e -> In q e ->
    (p = q \/ p = (snd q, fst q)) -> p = q) /\
  (connected ({| zv := fun x => 1 <= x <= n ; ze := fun x y => In (x, y) e \/ In (y, x) e|} : ZGraph))) /\ exists a, RootParityCount n e a /\ MinCoverSize n e a.
Definition Pre (n : Z) : Prop :=
  (* Every clause below is stated explicitly in the P045 solver Require, which
     therefore omits the Pre(...) call:
       2<=n<=100000. *)
  True.

(* The two output sections: each is None exactly when no tree of that kind exists
   for this n, and Some e for such a tree otherwise.
   C4 exception, recorded rather than closed: the statement's output has two
   independent sections and this Spec carries both, but solver()'s interface
   exposes only the first -- it writes the counterexample tree into eu/ev and
   returns 0/1. Section 2, the star centred at 1, correct for every n >= 2, is
   emitted by main()'s own print loop, so it reaches no solver channel and the
   contract leaves snd out unconstrained: the Ensure asserts only that some valid
   section 2 exists. Closing this needs a second pair of output arrays on
   solver(), i.e. a code change, which is deliberately not made here. *)
Definition Spec (n : Z) (out : option (list (Z * Z)%type) * option (list (Z * Z)%type)) : Prop :=
  ((fst out = None /\ ~exists e, WrongTree n e) \/ exists e, fst out = Some e /\ WrongTree n e) /\
  ((snd out = None /\ ~exists e, CorrectTree n e) \/ exists e, snd out = Some e /\ CorrectTree n e).
