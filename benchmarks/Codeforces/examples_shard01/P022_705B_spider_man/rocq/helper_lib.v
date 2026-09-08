Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(** The total number of splits needed to reduce all cycles to singletons.
    This closed-form quantity is independent of any particular play. *)
Definition CycleMoveCount (added : list Z) : Z :=
  fold_right Z.add 0 added - Zlength added.

(** One output code, stated directly in terms of the parity of the number of
    forced remaining splits: 1 is the first player and 2 is the second. *)
Definition SpiderWinnerCode (moves code : Z) : Prop :=
  (code = 1 /\ Z.odd moves = true) \/
  (code = 2 /\ Z.even moves = true).

(** The mathematical effect of adding one cycle to an already summarized
    prefix. *)
Definition NextParity (par a next : Z) : Prop :=
  0 <= par <= 1 /\
  1 <= a /\
  next = Z.rem (par + (a - 1)) 2.

(** A completed output prefix and the parity summary carried to the next
    iteration.  The output relation is a property of every prefix, not a
    model of the C loop. *)
Definition SpiderPrefixState
    (added out : list Z) (par : Z) : Prop :=
  Zlength out = Zlength added /\
  0 <= par <= 1 /\
  par = Z.rem (CycleMoveCount added) 2 /\
  forall i, 0 <= i < Zlength added ->
    SpiderWinnerCode
      (CycleMoveCount (sublist 0 (i + 1) added))
      (Znth i out 0).
