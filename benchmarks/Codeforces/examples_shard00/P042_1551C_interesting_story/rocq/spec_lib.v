Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition InterestingWordSelection (words : list (list Z)) (chosen : Z -> Prop) : Prop :=
  (forall i, chosen i -> 0 <= i < Zlength words) /\
  exists letter, 97 <= letter <= 101 /\
    2 * sum (fun i : Z => 0 <= i < Zlength words /\ chosen i) (fun i =>
      Zlength (filter (Z.eqb letter) (Znth i words nil))) >
    sum (fun i : Z => 0 <= i < Zlength words /\ chosen i)
      (fun i => Zlength (Znth i words nil)).

Definition Pre (words : list (list Z)) : Prop :=
  1 <= Zlength words <= 200000 /\ Forall (fun w => 0 < Zlength w /\
    Forall (fun c => 97 <= c <= 101) w) words.

Definition Spec (words : list (list Z)) (out : Z) : Prop :=
  (out = 0 /\ forall chosen, ~ InterestingWordSelection words chosen) \/
  max_value_of_subset Z.le
    (fun candidate : (Z -> Prop) * Z =>
      InterestingWordSelection words (fst candidate) /\
      snd candidate = #(fun i : Z =>
        0 <= i < Zlength words /\ fst candidate i))
    snd out.

Require Import Coq.Sorting.Permutation.

From AUXLib Require ListLib.

Definition TotalLength (words : list (list Z)) : Z :=
  fold_right Z.add 0 (map (@Zlength Z) words).
