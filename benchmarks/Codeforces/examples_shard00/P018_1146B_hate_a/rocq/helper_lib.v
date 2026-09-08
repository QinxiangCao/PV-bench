
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Local Open Scope Z_scope.

Definition FilteredPrefix
    (given : list Z) (i : Z) (filtered : list Z) : Prop :=
  filtered = filter (fun c => negb (Z.eqb c 97)) (sublist 0 i given).

Definition NoAInterval (given : list Z) (lo hi : Z) : Prop :=
  forall j, lo <= j < hi -> Znth j given 0 <> 97.

Definition MatchedSuffixPrefix
    (filtered given : list Z) (prefix matched : Z) : Prop :=
  forall j,
    0 <= j < matched ->
    Znth j filtered 0 = Znth (prefix + j) given 0.
