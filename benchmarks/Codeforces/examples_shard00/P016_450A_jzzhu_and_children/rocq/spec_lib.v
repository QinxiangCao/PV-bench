Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.

Local Open Scope Z_scope.

Definition OneCandyTurn
    (m : Z) (before after : list (Z * Z)) : Prop :=
  exists child need rest,
    before = (child, need) :: rest /\
    ((need <= m /\ after = rest) \/
     (need > m /\ after = rest ++ [(child, need - m)])).

Definition CandyQueueTrace
    (m : Z) (initial : list (Z * Z)) (states : list (list (Z * Z))) : Prop :=
  2 <= Zlength states /\
  Znth 0 states [] = initial /\
  Znth (Zlength states - 1) states [] = [] /\
  forall k, 0 <= k < Zlength states - 1 ->
    OneCandyTurn m (Znth k states []) (Znth (k + 1) states []).

Definition Pre (m : Z) (wants : list Z) : Prop :=
  1 <= Zlength wants <= 100 /\
  1 <= m <= 100 /\
  Forall (fun need => 1 <= need <= 100) wants.

Definition Spec (m : Z) (wants : list Z) (out : Z) : Prop :=
  exists states need rest,
    CandyQueueTrace m (combine (Zrange 1 (Zlength wants + 1)) wants) states /\
    Znth (Zlength states - 2) states [] = (out, need) :: rest.
