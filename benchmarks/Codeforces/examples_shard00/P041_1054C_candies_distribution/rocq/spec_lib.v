Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition ExplainsCandyReports (l r a : list Z) : Prop :=
  Zlength a = Zlength l /\ Forall (fun x => 1 <= x <= Zlength a) a /\
  forall i, 0 <= i < Zlength a ->
    Znth i l 0 = Zlength (filter (fun j => Znth i a 0 <? Znth j a 0) (Zrange 0 i)) /\
    Znth i r 0 = Zlength (filter (fun j => Znth i a 0 <? Znth j a 0) (Zrange (i+1) (Zlength a))).

Definition Pre (l r : list Z) : Prop :=
  1 <= Zlength l <= 1000 /\ Zlength r = Zlength l /\
  Forall (fun x => 0 <= x <= Zlength l) l /\ Forall (fun x => 0 <= x <= Zlength l) r.

Definition Spec (l r : list Z) (out : option (list Z)) : Prop :=
  (exists a, out = Some a /\ ExplainsCandyReports l r a) \/
  (out = None /\ forall a, ~ ExplainsCandyReports l r a).
