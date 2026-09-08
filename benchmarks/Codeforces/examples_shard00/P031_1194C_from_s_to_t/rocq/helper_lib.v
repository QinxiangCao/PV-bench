
Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import Coq.Sorting.Permutation.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition PrefixEmbedding
    (source target : list Z) (source_len target_len : Z) : Prop :=
  exists positions,
    Zlength positions = source_len /\
    mono_inc positions /\
    (forall k, 0 <= k < source_len ->
      0 <= Znth k positions 0 < target_len /\
      Znth (Znth k positions 0) target 0 = Znth k source 0).

Definition GreedyPrefixMatch
    (source target : list Z) (target_len matched : Z) : Prop :=
  0 <= matched <= Zlength source /\
  0 <= target_len <= Zlength target /\
  PrefixEmbedding source target matched target_len /\
  forall k,
    0 <= k <= Zlength source ->
    PrefixEmbedding source target k target_len ->
    k <= matched.

Definition IsSubsequence (source target : list Z) : Prop :=
  PrefixEmbedding source target (Zlength source) (Zlength target).

Definition NoSubsequence (source target : list Z) : Prop :=
  ~ IsSubsequence source target.

Definition LetterCount (text : list Z) (letter : Z) : Z :=
  Z.of_nat (count_occ Z.eq_dec text letter).

Definition CountState
    (source pool target : list Z)
    (source_done pool_done target_done : Z)
    (counts : list Z) : Prop :=
  Zlength counts = 26 /\
  forall c, 0 <= c < 26 ->
    Znth c counts 0 =
      LetterCount (sublist 0 source_done source) (97 + c) +
      LetterCount (sublist 0 pool_done pool) (97 + c) -
      LetterCount (sublist 0 target_done target) (97 + c).

Definition NonnegativeCounts (counts : list Z) : Prop :=
  forall c, 0 <= c < 26 -> 0 <= Znth c counts 0.

Definition SupplyShortage
    (source pool target : list Z) : Prop :=
  exists c,
    0 <= c < 26 /\
    LetterCount (source ++ pool) (97 + c) <
    LetterCount target (97 + c).
