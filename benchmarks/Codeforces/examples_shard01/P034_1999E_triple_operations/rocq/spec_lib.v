(* Codeforces 1999/E - Triple Operations: one operation replaces two board entries
   x, y by 3x and floor(y/3); fewest operations to zero the board l..r. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* One operation: pick positions i <> j and replace a[i] by 3 * a[i] and a[j] by
   floor(a[j] / 3). *)
Definition TripleStep (a b : list Z) : Prop :=
  exists i j, 0 <= i < Zlength a /\ 0 <= j < Zlength a /\ i <> j /\
    b = replace_Znth j (Znth j a 0 / 3) (replace_Znth i (3 * Znth i a 0) a).

(* 'moves' operations suffice: st[0] is the initial board l, l+1, ..., r, each
   step is a TripleStep, and st[moves] is all zeros. *)
Definition TripleReach (l r moves : Z) : Prop :=
  exists st : list (list Z), Zlength st = moves + 1 /\ Znth 0 st [] = Zrange l (r + 1) /\
    (forall q, 0 <= q < moves -> TripleStep (Znth q st []) (Znth (q + 1) st [])) /\
    Forall (fun x => x = 0) (Znth moves st []).
Definition Pre (l r : Z) : Prop :=
  (* Every clause below is stated explicitly in the P034 solver Require, which
     therefore omits the Pre(l, r) call:
       1 <= l < r /\ r <= 200000. *)
  True.

(* out = min { q >= 0 : TripleReach l r q }. *)
Definition Spec (l r out : Z) : Prop :=
  min_value_of_subset Z.le (fun q => q >= 0 /\ TripleReach l r q) (fun x => x) out.

(* Contents of the two precomputed tables the solver reads: fvs.[i] counts the
   base-3 digits of i and pres.[i] accumulates fvs over 1..i, each stated as the
   recurrence that determines it from index 0 upwards. *)
Definition TripleTablesBridge (fvs pres : list Z) : Prop :=
  Zlength fvs = 200005 /\
  Zlength pres = 200005 /\
  Znth 0 fvs 0 = 0 /\
  Znth 0 pres 0 = 0 /\
  (forall i, 1 <= i < 200005 -> Znth i fvs 0 = Znth (i / 3) fvs 0 + 1) /\
  (forall i, 1 <= i < 200005 ->
     Znth i pres 0 = Znth (i - 1) pres 0 + Znth i fvs 0).
