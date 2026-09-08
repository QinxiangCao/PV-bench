Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Mathematical cost of making one residue class constant. *)
Definition ResidueValueCount
    (k r upto value : Z) (a : list Z) : Z :=
  #(fun i : Z =>
      0 <= i < Zlength a /\
      i < upto /\
      Z.modulo i k = r /\
      Znth i a 0 = value).

Definition ResidueChangeCost (k r : Z) (a : list Z) : Z :=
  Z.min (ResidueValueCount k r (Zlength a) 1 a)
        (ResidueValueCount k r (Zlength a) 2 a).

Definition ProcessedChangeCost (k r : Z) (a : list Z) : Z :=
  fold_right Z.add 0
    (map
       (fun rn => ResidueChangeCost k (Z.of_nat rn) a)
       (seq 0 (Z.to_nat r))).

Definition PrefixCost
    (k r : Z) (a : list Z) (changes : Z) : Prop :=
  changes = ProcessedChangeCost k r a.

Definition ResidueScan
    (k r upto : Z) (a : list Z) (ones twos : Z) : Prop :=
  ones = ResidueValueCount k r upto 1 a /\
  twos = ResidueValueCount k r upto 2 a.
