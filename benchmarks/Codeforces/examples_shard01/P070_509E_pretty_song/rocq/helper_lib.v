Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import PVbench.Codeforces.examples_shard01.P070_509E_pretty_song.rocq.spec_lib.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope R_scope.

Definition VowelPrefixCounts (s counts : list Z) : Prop :=
  forall k, (0 <= k < Zlength counts)%Z ->
    Znth k counts 0%Z =
      #(fun q : Z => (0 <= q < k)%Z /\ Vowel (Znth q s 0%Z)).

Definition PrefixCountTotals (counts totals : list Z) : Prop :=
  forall k, (0 <= k < Zlength totals)%Z ->
    Znth k totals 0%Z =
      sum_range 0 k (fun q => Znth q counts 0%Z).

Definition PrettyTermPrefix (s terms : list Z) : Prop :=
  forall len, (1 <= len <= Zlength terms)%Z ->
    Znth (len - 1)%Z terms 0%Z = PrettyTerm s len.

(* Begin the append-only proof/dependency area after the frozen declarations. *)
