Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition PositionTable
    (values table : list Z) (n : Z) : Prop :=
  Zlength values = n /\
  Zlength table = n + 1 /\
  (forall i, 0 <= i < n ->
    1 <= Znth i values 0 <= n /\
    Znth (Znth i values 0) table 0 = i) /\
  (forall v, 1 <= v <= n -> 0 <= Znth v table 0 < n).

Definition RotationTallyPrefix
    (pa pb : list Z) (n next : Z) (counts : list Z) : Prop :=
  Zlength counts = n /\
  1 <= next <= n + 1 /\
  forall s, 0 <= s < n ->
    Znth s counts 0 =
      #(fun v : Z =>
          1 <= v < next /\
          (Znth v pa 0 - Znth v pb 0) mod n = s) /\
    0 <= Znth s counts 0 <= next - 1.

Definition CountPrefixMaximum
    (counts : list Z) (upto best : Z) : Prop :=
  0 <= upto <= Zlength counts /\
  0 <= best /\
  (forall s, 0 <= s < upto -> Znth s counts 0 <= best) /\
  (upto = 0 -> best = 0) /\
  (0 < upto -> exists s, 0 <= s < upto /\ Znth s counts 0 = best).
