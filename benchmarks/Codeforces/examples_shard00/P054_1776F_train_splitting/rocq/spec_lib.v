Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Require Import GraphLib.graph_basic.

Require Import GraphLib.reachable.reachable_basic.

Require Import SimpleC.EE.LLM_bench.Codeforces.GraphInstances.

Local Open Scope Z_scope.

Definition CanonicalEdge (p : Z * Z) : Z * Z :=
  if Z.leb (fst p) (snd p) then p else (snd p, fst p).

Definition InputGraph (n : Z) (e : list (Z * Z)) : ZGraph :=
  {| zv := fun v => 0 <= v < n;
     ze := fun u v => exists j,
       0 <= j < Zlength e /\
       (Znth j e (0,0) = (u,v) \/ Znth j e (0,0) = (v,u)) |}.

Definition InputConnected (n : Z) (e : list (Z * Z)) : Prop :=
  forall u v, 0 <= u < n -> 0 <= v < n ->
    reachable (InputGraph n e) u v.

Definition CompanyGraph (n : Z) (c : list Z) (e : list (Z * Z))
    (labels : list Z) : ZGraph :=
  {| zv := fun v => 0 <= v < n;
     ze := fun u v => exists j,
       0 <= j < Zlength e /\
       (Znth j e (0,0) = (u,v) \/ Znth j e (0,0) = (v,u)) /\
       In (Znth j labels 0) c |}.

Definition CompanyConnected (n : Z) (c : list Z) (e : list (Z * Z))
    (labels : list Z) : Prop :=
  forall u v, 0 <= u < n -> 0 <= v < n ->
    reachable (CompanyGraph n c e labels) u v.

Definition ValidTrainPlan (n : Z) (e : list (Z * Z)) (k : Z)
    (labels : list Z) : Prop :=
  2 <= k <= 3 /\ Zlength labels = Zlength e /\
  Forall (fun x => 1 <= x <= k) labels /\
  (forall c, 1 <= c <= k -> ~ CompanyConnected n (c :: nil) e labels) /\
  forall c d, 1 <= c <= k -> 1 <= d <= k -> c <> d ->
    CompanyConnected n (c :: d :: nil) e labels.

Definition Pre (n : Z) (e : list (Z * Z)) : Prop :=
  3 <= n <= 50 /\ n - 1 <= Zlength e /\ Zlength e <= 1225 /\
  Forall (fun p => 0 <= fst p < n /\
    0 <= snd p < n /\ fst p <> snd p) e /\
  NoDup (map CanonicalEdge e) /\ InputConnected n e.

Definition Spec (n : Z) (e : list (Z * Z)) (out : Z * list Z) : Prop :=
  ValidTrainPlan n e (fst out) (snd out).
