Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition CopyPasteStep (current : list Z) (op : Z * Z) : list Z :=
  current ++ sublist (fst op - 1) (snd op) current.

Definition Pre (s : list Z) (ops : list (Z * Z)) (queries : list Z) : Prop :=
  1 <= Zlength s <= 200000 /\ 1 <= Zlength ops <= 40 /\
  1 <= Zlength queries <= 10000 /\ Forall (fun c => 97 <= c <= 122) s /\
  exists states,
    Zlength states = Zlength ops + 1 /\ Znth 0 states nil = s /\
    (forall i, 0 <= i < Zlength ops ->
       1 <= fst (Znth i ops (0, 0)) <= snd (Znth i ops (0, 0)) /\
       snd (Znth i ops (0, 0)) <= Zlength (Znth i states nil) /\
       Znth (i + 1) states nil = CopyPasteStep (Znth i states nil) (Znth i ops (0, 0))) /\
    Forall (fun k => 1 <= k <= Zlength (Znth (Zlength ops) states nil)) queries.

Definition Spec (s : list Z) (ops : list (Z * Z)) (queries out : list Z) : Prop :=
  let final := fold_left CopyPasteStep ops s in
  Forall2
    (fun query answer => answer = Znth (query - 1) final 0)
    queries out.
