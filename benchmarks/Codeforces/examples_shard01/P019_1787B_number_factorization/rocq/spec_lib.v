(* Codeforces 1787/B - Number Factorization: maximise sum(a_i * p_i) over the
   factorizations n = prod a_i^p_i whose bases are products of distinct primes. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import Coq.ZArith.Znumtheory.

Import ListNotations.
Local Open Scope Z_scope.

(* x is a non-empty product of pairwise distinct primes -- the statement's legal
   bases a_i, so in particular x > 1. *)
Definition SquareFree (x : Z) : Prop :=
  exists ps, ps <> [] /\ NoDup ps /\ Forall prime ps /\ x = fold_right Z.mul 1 ps.

(* Signature: solve_case(n) -> Z. value is attained by some factorization:
     ap = [(a_1, p_1), ...] non-empty
     each a_i square-free and p_i > 0
     n = prod a_i^p_i
     value = sum a_i * p_i *)
Definition ValidFactorization (n value : Z) : Prop :=
  exists ap : list (Z * Z), ap <> [] /\
    Forall (fun q => SquareFree (fst q) /\ snd q > 0) ap /\
    n = (fold_right Z.mul 1) (map (fun q => Z.pow (fst q) (snd q)) ap) /\
    value = (fold_right Z.add 0) (map (fun q => fst q * snd q) ap).

(* 2 <= n <= 10^9. *)
Definition Pre (n : Z) : Prop :=
  (* Stated explicitly in the P019 solver Require, which therefore omits the
     Pre(...) call: 2 <= n <= 1000000000. *)
  True.

(* out = max { value : ValidFactorization n value }. *)
Definition Spec (n out : Z) : Prop := max_value_of_subset Z.le (ValidFactorization n) (fun x => x) out.
