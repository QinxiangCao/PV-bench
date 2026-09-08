(* Codeforces 555/A - Case of Matryoshkas: fewest seconds to rebuild the single
   chain 1 -> 2 -> ... -> n from the given chains, one nesting or unnesting per
   second. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* p is the initial configuration as a parent array:
     |p| = n
     p[x-1] = 0, or the doll x sits directly inside
     within a chain ch:  p[ch[i]-1] = ch[i+1]      each doll nests in the next
                         p[ch[|ch|-1]-1] = 0       the last one is outermost *)
Definition ChainParent (n : Z) (chains : list (list Z)) (p : list Z) : Prop :=
  Zlength p = n /\
  (forall x, 1 <= x <= n -> Znth (x - 1) p 0 = 0 \/ 1 <= Znth (x - 1) p 0 <= n) /\
  (forall ch, In ch chains ->
    (forall i, 0 <= i < Zlength ch - 1 -> Znth (Znth i ch 0 - 1) p 0 = Znth (i + 1) ch 0) /\
    Znth (Znth (Zlength ch - 1) ch 0 - 1) p 0 = 0).

(* One second of work, on dolls a <> b:
     a and b both free and b empty      ->  p[a-1] := b, putting a into b
     p[a-1] = b and b free              ->  p[a-1] := 0, taking a out of b *)
Definition NestStep (n : Z) (p q : list Z) : Prop :=
  exists a b, 1 <= a <= n /\ 1 <= b <= n /\ a <> b /\
   ((Znth (a - 1) p 0 = 0 /\ Znth (b - 1) p 0 = 0 /\
     (forall z, 1 <= z <= n -> Znth (z - 1) p 0 <> b) /\ q = replace_Znth (a - 1) b p) \/
    (Znth (a - 1) p 0 = b /\ Znth (b - 1) p 0 = 0 /\ q = replace_Znth (a - 1) 0 p)).

(* The goal configuration 1 -> 2 -> ... -> n: p[x-1] = x + 1 for x < n, and
   p[n-1] = 0. *)
Definition TargetChain (n : Z) (p : list Z) : Prop :=
  Zlength p = n /\ (forall x, 1 <= x < n -> Znth (x - 1) p 0 = x + 1) /\ Znth (n - 1) p 0 = 0.

(* 'moves' seconds suffice: some chain of that many steps leads from a parent
   array describing the given chains to the target chain. *)
Definition ReachMatryoshka (n moves : Z) (chains : list (list Z)) : Prop :=
  exists init st, ChainParent n chains init /\ Zlength st = moves + 1 /\ Znth 0 st [] = init /\
    (forall i, 0 <= i < moves -> NestStep n (Znth i st []) (Znth (i + 1) st [])) /\ TargetChain n (Znth moves st []).
Definition Pre (n : Z) (chains : list (list Z)) : Prop :=
  (* Stated explicitly in the P042 solver Require, so dropped here:
       1 <= n <= 100000 /\
       1 <= Zlength chains <= 100000 /\
       Forall (fun ch => 1 <= Zlength ch <= n) chains. *)
  concat chains <> [] /\
  Permutation (concat chains) (Zrange 1 (n + 1)) /\
  Forall (fun ch => ch <> []) chains /\
  Forall mono_inc chains.

(* out = min { d >= 0 : ReachMatryoshka n d chains }. *)
Definition Spec (n : Z) (chains : list (list Z)) (out : Z) : Prop :=
  (min_value_of_subset Z.le (fun d => d >= 0 /\ ReachMatryoshka n d chains) (fun x => x)) out.

(* Row lengths of the chain collection, as the solver receives them in m[]. *)
Definition ChainLengths (chains : list (list Z)) : list Z :=
  map (fun row => Zlength row) chains.

(* A candidate prefix is either the always-usable singleton doll [1], or an
   initial segment [1; ...; q] that is already consecutive in one chain. *)
Definition UsablePrefixCandidate (chains : list (list Z)) (q : Z) : Prop :=
  q = 1 \/
  exists ch,
    In ch chains /\
    1 <= q <= Zlength ch /\
    forall i, 0 <= i < q -> Znth i ch 0 = i + 1.

(* q is the largest usable prefix: a candidate that is at least every candidate. *)
Definition IsUsablePrefix (chains : list (list Z)) (q : Z) : Prop :=
  UsablePrefixCandidate chains q /\
  forall r, UsablePrefixCandidate chains r -> r <= q.

(* The finite maximum is represented as a mathematical choice, rather than as
   a second implementation of the C input scan. *)
Definition usable_prefix (chains : list (list Z)) : Z :=
  epsilon (inhabits 1) (IsUsablePrefix chains).
