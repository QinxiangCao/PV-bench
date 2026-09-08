
Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition CandyCandidateAt (n : Z) (l r : list Z) (i : Z) : Z :=
  n - Znth i l 0 - Znth i r 0.

Definition CandyCandidatePrefix
    (n : Z) (l r : list Z) (k : Z) (a : list Z) : Prop :=
  Zlength a = k /\
  forall i, 0 <= i < k -> Znth i a 0 = CandyCandidateAt n l r i.

Definition CandyLeftCount
    (a : list Z) (i j count : Z) : Prop :=
  count = Zlength
    (filter (fun k => Znth i a 0 <? Znth k a 0) (Zrange 0 j)).

Definition CandyRightCount
    (a : list Z) (i j count : Z) : Prop :=
  count = Zlength
    (filter (fun k => Znth i a 0 <? Znth k a 0) (Zrange (i + 1) j)).

Definition CandyCheckedPrefix
    (l r a : list Z) (k : Z) : Prop :=
  forall i, 0 <= i < k ->
    1 <= Znth i a 0 <= Zlength a /\
    Znth i l 0 = Zlength
      (filter (fun j => Znth i a 0 <? Znth j a 0) (Zrange 0 i)) /\
    Znth i r 0 = Zlength
      (filter (fun j => Znth i a 0 <? Znth j a 0)
        (Zrange (i + 1) (Zlength a))).
