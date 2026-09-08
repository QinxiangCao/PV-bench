
Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Require Import GraphLib.graph_basic.

Require Import GraphLib.reachable.vpath.

Require Import SimpleC.EE.LLM_bench.Codeforces.GraphInstances.

Local Open Scope Z_scope.

Definition Feasible (n d h : Z) : Prop :=
  d <= 2 * h /\ (d <> 1 \/ n <= 2).

Definition CanonicalParent (d h k : Z) : Z :=
  if Z_lt_dec k h then k + 1
  else if Z.eq_dec d h then 2
  else if Z.eq_dec k h then 1
  else if Z_lt_dec k d then k + 1
  else 1.

Definition CanonicalEndpoints (d h k u v : Z) : Prop :=
  u = CanonicalParent d h k /\ v = k + 2.
