Require Import PVbench.Codeforces.examples_shard00.P036_1705C_mark_and_his_unfinished_essay.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition CopyPasteStates
    (s : list Z) (ops : list (Z * Z)) (states : list (list Z)) : Prop :=
  Zlength states = Zlength ops + 1 /\
  Znth 0 states nil = s /\
  forall i, 0 <= i < Zlength ops ->
    1 <= fst (Znth i ops (0, 0)) <= snd (Znth i ops (0, 0)) /\
    snd (Znth i ops (0, 0)) <= Zlength (Znth i states nil) /\
    Znth (i + 1) states nil =
      CopyPasteStep (Znth i states nil) (Znth i ops (0, 0)).

Definition StateLengthsPrefix
    (states : list (list Z)) (upto : Z) (lengths : list Z) : Prop :=
  Zlength lengths = upto /\
  forall i, 0 <= i < upto ->
    Znth i lengths 0 = Zlength (Znth i states nil).

Definition BacktrackedPosition
    (states : list (list Z)) (query i k : Z) : Prop :=
  let final_index := Zlength states - 1 in
  -1 <= i < final_index /\
  1 <= query <= Zlength (Znth final_index states nil) /\
  1 <= k <= Zlength (Znth (i + 1) states nil) /\
  Znth (k - 1) (Znth (i + 1) states nil) 0 =
    Znth (query - 1) (Znth final_index states nil) 0.

Definition AnswerPrefix
    (s : list Z) (ops : list (Z * Z))
    (queries : list Z) (upto : Z) (out : list Z) : Prop :=
  let final := fold_left CopyPasteStep ops s in
  0 <= upto <= Zlength queries /\
  Zlength out = upto /\
  forall i, 0 <= i < upto ->
    Znth i out 0 = Znth (Znth i queries 0 - 1) final 0.

Definition FinalCharacter
    (s : list Z) (ops : list (Z * Z)) (query answer : Z) : Prop :=
  answer = Znth (query - 1) (fold_left CopyPasteStep ops s) 0.
