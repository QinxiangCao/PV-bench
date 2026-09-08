Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import PVbench.Codeforces.examples_shard01.P044_837C_two_seals.rocq.spec_lib.

Import ListNotations.
Local Open Scope Z_scope.

(* Implementation-facing mathematical interfaces.  [rotate_seal] is the two
   possible orientations of one seal, and [BestBefore] is the optimum over the
   lexicographic prefix of pair/orientation choices preceding [i,j,ri,rj]. *)
Definition rotate_seal (s : Z * Z) (r : Z) : Z * Z :=
  if Z.eq_dec r 0 then s else (snd s, fst s).

Definition FitsDims
    (w1 h1 w2 h2 a b : Z) : Prop :=
  TwoFit a b (w1, h1) (w2, h2).

Definition SealChoice
    (paper : Z * Z) (seals : list (Z * Z))
    (i j ri rj area : Z) : Prop :=
  0 <= i < j /\ j < Zlength seals /\
  0 <= ri < 2 /\ 0 <= rj < 2 /\
  let s1 := rotate_seal (Znth i seals (0, 0)) ri in
  let s2 := rotate_seal (Znth j seals (0, 0)) rj in
  TwoFit (fst paper) (snd paper) s1 s2 /\
  area = fst s1 * snd s1 + fst s2 * snd s2.

Definition ChoiceBefore
    (i j ri rj pi pj pri prj : Z) : Prop :=
  pi < i \/
  (pi = i /\
   (pj < j \/
    (pj = j /\ (pri < ri \/ (pri = ri /\ prj < rj))))).

Definition SealAreaBefore
    (paper : Z * Z) (seals : list (Z * Z))
    (i j ri rj area : Z) : Prop :=
  area = 0 \/
  exists pi pj pri prj,
    ChoiceBefore i j ri rj pi pj pri prj /\
    SealChoice paper seals pi pj pri prj area.

Definition BestBefore
    (paper : Z * Z) (seals : list (Z * Z))
    (i j ri rj best : Z) : Prop :=
  max_value_of_subset Z.le
    (SealAreaBefore paper seals i j ri rj) (fun x => x) best.
