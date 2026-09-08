
Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition MusicLoopInvariant
    (t initial q count current : Z) : Prop :=
  0 <= count /\
  current = initial * Z.pow q count /\
  forall i,
    0 <= i < count ->
    initial * Z.pow q i < t.
