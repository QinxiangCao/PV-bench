Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import PVbench.Codeforces.examples_shard01.P042_555A_case_of_matryoshkas.rocq.spec_lib.

Import ListNotations.
Local Open Scope Z_scope.

(* Cost of extracting every adjacency in the first [upto] chains. *)
Definition PrefixExtractionCost (chains : list (list Z)) (upto : Z) : Z :=
  fold_right Z.add 0
    (map (fun len => len - 1)
      (sublist 0 upto (ChainLengths chains))).
