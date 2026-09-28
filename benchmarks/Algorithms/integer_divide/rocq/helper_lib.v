Require Export PVbench.Algorithms.integer_divide.rocq.spec_lib.
From Coq Require Import ZArith List Znumtheory Sorting.Sorted.
Import ListNotations.
Local Open Scope Z_scope.
From Coq Require Import Lia.

(** Internal mathematical state shared by both trial-division loop heads.
    Machine ranges, [cnt]/list-length bindings, modulo guards, and array
    ownership deliberately remain visible in the C annotation. *)
Definition FactorizationProgress
    (original : Z) (factors : list Z) (remaining candidate : Z) : Prop :=
  fold_right Z.mul 1 factors * remaining = original /\
  Forall prime factors /\
  Sorted Z.le factors /\
  Forall (fun factor => factor <= candidate) factors /\
  (forall d : Z,
      2 <= d < candidate -> ~ Z.divide d remaining).
