Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition ChangedExactly (commands modified : list Z) (n : Z) : Prop :=
  Zlength modified = Zlength commands /\
  exists counts, Zlength counts = Zlength commands /\
    Forall (fun x => 0 <= x) counts /\ fold_right Z.add 0 counts = n /\
    forall i, 0 <= i < Zlength commands ->
      (Z.even (Znth i counts 0) = true ->
        Znth i modified 0 = Znth i commands 0) /\
      (Z.even (Znth i counts 0) = false ->
        ((Znth i commands 0 = 70 /\ Znth i modified 0 = 84) \/
         (Znth i commands 0 = 84 /\ Znth i modified 0 = 70))).

Definition TurtleEnd (c : list Z) (x : Z) : Prop :=
  exists states, Zlength states = Zlength c + 1 /\
    Znth 0 states (0, 1) = (0, 1) /\
    (forall i, 0 <= i < Zlength c ->
      let '(p, d) := Znth i states (0, 1) in
      Znth (i + 1) states (0, 1) =
        if Z.eqb (Znth i c 0) 84 then (p, -d) else (p + d, d)) /\
    x = fst (Znth (Zlength c) states (0, 1)).

Definition Pre (n : Z) (c : list Z) : Prop :=
  1 <= Zlength c <= 100 /\ 1 <= n <= 50 /\
  Forall (fun x => x = 70 \/ x = 84) c.

Definition Spec (n : Z) (c : list Z) (out : Z) : Prop :=
  max_value_of_subset Z.le
    (fun candidate : list Z * Z =>
      ChangedExactly c (fst candidate) n /\
      TurtleEnd (fst candidate) (snd candidate))
    (fun candidate => Z.abs (snd candidate)) out.
