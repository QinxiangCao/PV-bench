Require Import PVbench.Codeforces.examples_shard01.P015_2051C_preparing_for_the_exam.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

(* [next] is the first question not yet inspected.  The three cases record
   whether the inspected interval [1,next) has no unknown question, exactly
   one unknown question, or at least two. *)
Definition UnknownPrefixSummary
    (n : Z) (known : Z -> Prop)
    (next unknown only : Z) : Prop :=
  1 <= next <= n + 1 /\
  ((unknown = 0 /\
    forall q, 1 <= q < next -> known q) \/
   (unknown = 1 /\
    1 <= only < next /\
    ~ known only /\
    forall q, 1 <= q < next -> q = only \/ known q) \/
   (2 <= unknown /\
    exists q1 q2,
      1 <= q1 < next /\
      1 <= q2 < next /\
      q1 <> q2 /\
      ~ known q1 /\
      ~ known q2)).

(* The first [upto] answers and their bytes already agree with the problem
   specification; the terminating zero is deliberately outside this prefix. *)
Definition ResultPrefix
    (n : Z) (missing : list Z) (known : Z -> Prop) (upto : Z)
    (out bytes : list Z) : Prop :=
  Zlength out = upto /\
  Zlength bytes = upto /\
  Spec n (sublist 0 upto missing) known out /\
  Forall2 ResultDigitByte out bytes.
