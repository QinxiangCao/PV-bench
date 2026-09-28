Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import Coq.Sorting.Permutation.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition MaximalPrefixSum (a : list Z) (value : Z) : Prop :=
  max_value_of_subset Z.le
    (fun i : Z => 0 <= i < Zlength a + 1)
    (fun i => fold_right Z.add 0 (sublist 0 i a)) value.

Definition IsSign (x : Z) : Prop := -1 <= x < 2 /\ (x = -1 \/ x = 1).

#[export] Instance finite_sign : Finite IsSign :=
  Finite_subset (fun x : Z => -1 <= x < 2) (fun x => x = -1 \/ x = 1).

#[export] Instance finite_sign_array (size : Z) :
    Finite (fun a : list Z =>
      Zlength a = size /\ Forall IsSign a) :=
  Finite_bounded_lists size IsSign.

#[export] Instance finite_array_and_maximum (n m : Z) :
    Finite (fun candidate : list Z * Z =>
      (Zlength (fst candidate) = n + m /\
       Forall IsSign (fst candidate)) /\
      0 <= snd candidate < n + 1) :=
  Finite_prod
    (fun a : list Z =>
      Zlength a = n + m /\ Forall IsSign a)
    (fun maximum : Z => 0 <= maximum < n + 1).

Definition Zmap_range {A : Type} (f : Z -> A) (n : Z) : list A :=
  map f (Zrange 0 n).

Definition IsArrayMaximumCandidate (n m : Z) (candidate : list Z * Z) : Prop :=
  Permutation (fst candidate)
    (Zmap_range (fun _ => 1) n ++ Zmap_range (fun _ => -1) m) /\
  MaximalPrefixSum (fst candidate) (snd candidate).

Definition Pre (n m : Z) : Prop := 0 <= n <= 2000 /\ 0 <= m <= 2000.

Definition Spec (n m out : Z) : Prop :=
  out = sum
    (fun candidate : list Z * Z =>
      ((Zlength (fst candidate) = n + m /\
        Forall IsSign (fst candidate)) /\
       0 <= snd candidate < n + 1) /\
      IsArrayMaximumCandidate n m candidate)
    snd mod 998244853.

Require Import Coq.Arith.Factorial.

Require Import Coq.micromega.Lia.

Require Import Coq.ZArith.Zpow_facts.

Require Import Coq.micromega.Psatz.
