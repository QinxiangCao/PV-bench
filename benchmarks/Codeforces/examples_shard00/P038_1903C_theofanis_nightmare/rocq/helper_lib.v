
Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition SuffixSum (a : list Z) (lo : Z) : Z :=
  fold_right Z.add 0 (sublist lo (Zlength a) a).

Definition SuffixContribution (a : list Z) (i : Z) : Z :=
  if Z.eq_dec i 0 then SuffixSum a 0 else Z.max 0 (SuffixSum a i).

Definition SuffixContributionSum (a : list Z) (lo value : Z) : Prop :=
  0 <= lo <= Zlength a /\
  value = fold_right Z.add 0
    (map (SuffixContribution a) (Zrange lo (Zlength a))).
