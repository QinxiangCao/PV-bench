Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.

Local Open Scope Z_scope.

Definition OneAdjacentMatchMove (before after : list Z) : Prop := exists i,
  0 <= i < Zlength before-1 /\
  ((Znth i before 0>0 /\ after = replace_Znth (i + 1) (Znth (i + 1) before 0 + 1) (replace_Znth i (Znth i before 0 - 1) before)) \/
   (Znth (i + 1) before 0 > 0 /\ after = replace_Znth i (Znth i before 0 + 1) (replace_Znth (i + 1) (Znth (i + 1) before 0 - 1) before))).

Definition BalanceTrace (a : list Z) (moves : Z) : Prop := exists states,
  Zlength states = moves + 1 /\ Znth 0 states nil = a /\
  (forall i, 0 <= i < moves -> OneAdjacentMatchMove (Znth i states nil) (Znth (i+1) states nil)) /\
  exists target, Forall (fun x => x = target) (Znth moves states nil).

Definition Pre (a : list Z) : Prop := 1 <= Zlength a <= 50000 /\ Forall (fun x => 0 <= x <= 1000000000) a /\ (Zlength a | fold_right Z.add 0 a).

Definition Spec (a : list Z) (out : Z) : Prop :=
  min_value_of_subset Z.le (BalanceTrace a) (fun moves => moves) out.
