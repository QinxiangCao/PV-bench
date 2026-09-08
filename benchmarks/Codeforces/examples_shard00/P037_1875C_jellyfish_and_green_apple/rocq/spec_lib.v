Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import Coq.Sorting.Permutation.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.

Local Open Scope Z_scope.

Definition Zmap_range {A : Type} (f : Z -> A) (n : Z) : list A :=
  map f (Zrange 0 n).

Definition OneAppleCut (before after : list Z) : Prop :=
  exists prefix e suffix,
    before = prefix ++ e :: suffix /\ after = prefix ++ [e + 1; e + 1] ++ suffix.

Definition EqualDyadicShares (m : Z) (pieces : list Z) : Prop :=
  exists shares depth,
    Zlength shares = m /\ Permutation pieces (concat shares) /\
    Forall (fun e => 0 <= e <= depth) pieces /\
    forall i j, 0 <= i < m -> 0 <= j < m ->
      fold_right (fun e total => 2 ^ (depth - e) + total) 0 (Znth i shares nil) =
      fold_right (fun e total => 2 ^ (depth - e) + total) 0 (Znth j shares nil).

Definition AchievableAppleDivision (n m cuts : Z) : Prop :=
  exists states,
    Zlength states = cuts + 1 /\
    Znth 0 states nil = Zmap_range (fun _ => 0) n /\
    (forall i, 0 <= i < cuts -> OneAppleCut (Znth i states nil) (Znth (i + 1) states nil)) /\
    EqualDyadicShares m (Znth cuts states nil).

Definition Pre (n m : Z) : Prop := 1 <= n <= 1000000000 /\ 1 <= m <= 1000000000.

Definition Spec (n m out : Z) : Prop :=
  min_value_of_subset Z.le
    (fun cuts : Z => 0 <= cuts /\ AchievableAppleDivision n m cuts)
    (fun cuts => cuts) out \/
  (out = -1 /\ forall cuts, ~ (0 <= cuts /\ AchievableAppleDivision n m cuts)).
