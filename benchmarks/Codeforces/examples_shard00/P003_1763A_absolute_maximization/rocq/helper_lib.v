
Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import Coq.Relations.Relation_Operators.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

(** Mathematical meaning of the two accumulators after [i] loop iterations.
    The AND accumulator starts at the first input element, so its observed
    prefix has length [max 1 i]; the OR accumulator starts from zero. *)
Definition BitwiseScanState
    (a : list Z) (i acc_or acc_and : Z) : Prop :=
  0 <= i <= Zlength a /\
  (forall b, 0 <= b ->
    (Z.testbit acc_or b = true <->
      exists j, 0 <= j < i /\ Z.testbit (Znth j a 0) b = true)) /\
  (forall b, 0 <= b ->
    (Z.testbit acc_and b = true <->
      forall j, 0 <= j < Z.max 1 i ->
        Z.testbit (Znth j a 0) b = true)).
