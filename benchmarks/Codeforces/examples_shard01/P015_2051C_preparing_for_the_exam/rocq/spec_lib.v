(* Codeforces 2051/C - Preparing for the Exam: list i contains every question of
   1..n except missing[i]; print for each list whether all its questions are known. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Signature: solve_case(n, missing, known) -> list Z. List i contains every
   question of 1..n except missing[i]; known is the set of questions Monocarp
   knows. Pre: missing is duplicate-free and strictly increasing, and known is
   non-empty.  The numeric range constraints are explicit in the solver
   Require. *)
Definition Pre (n : Z) (missing : list Z) (known : Z -> Prop) : Prop :=
  (* Stated explicitly in the solver Require, so dropped here:
       2 <= n <= 300000 /\
       1 <= Zlength missing <= n /\
       Forall (fun x => 1 <= x <= n) missing /\
       (forall q, known q -> 1 <= q <= n) /\ *)
  NoDup missing /\
  mono_inc missing /\
  exists q, known q.

(* The list omitting missing_question is passable: every q in [1, n] is either
   that omitted question or known. *)
Definition CanPass (n missing_question : Z) (known : Z -> Prop) : Prop :=
  forall q, 1 <= q <= n -> q = missing_question \/ known q.

(* One printed digit: result = 1 when the list is passable, 0 when it is not. *)
Definition QuestionResult
    (n : Z) (known : Z -> Prop) (missing_question result : Z) : Prop :=
  (result = 1 /\ CanPass n missing_question known) \/
  (result = 0 /\ ~CanPass n missing_question known).

(* out[i] is the digit for list i, in the order the lists are given -- pointwise
   QuestionResult over missing, so |out| = |missing|. *)
Definition Spec
    (n : Z) (missing : list Z) (known : Z -> Prop) (out : list Z) : Prop :=
  Forall2 (QuestionResult n known) missing out.

(* C-side lookup table: |flags| = n + 1 and flags[q] <> 0 exactly for the known
   questions q in [1, n]. *)
Definition KnownFlagsBridge
    (n : Z) (known : Z -> Prop) (flags : list Z) : Prop :=
  Zlength flags = n + 1 /\
  forall q, 1 <= q <= n ->
    ((known q /\ Znth q flags 0 <> 0) \/
     (~known q /\ Znth q flags 0 = 0)).

(* Digit character codes: '0' = 48 and '1' = 49. *)
Definition ResultDigitByte (result byte : Z) : Prop :=
  (result = 0 /\ byte = 48) \/ (result = 1 /\ byte = 49).

(* The printed line: bytes[0 .. |out|-1] are the out digits as characters and
   bytes[|out|] = 0, the NUL terminator. *)
Definition ResultStringBridge (out bytes : list Z) : Prop :=
  Zlength bytes = Zlength out + 1 /\
  Forall2 ResultDigitByte out (sublist 0 (Zlength out) bytes) /\
  Znth (Zlength out) bytes 0 = 0.
