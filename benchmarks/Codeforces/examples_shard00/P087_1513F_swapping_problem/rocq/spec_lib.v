Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import Coq.Strings.String.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Require Import Coq.micromega.Lia.

From SimpleC.SL Require Import Mem SeparationLogic ArrayLib.

Local Open Scope Z_scope.

Import ListNotations.

Import naive_C_Rules.

Local Open Scope sac.

Local Open Scope string_scope.

Definition Zmap_range {A : Type} (f : Z -> A) (n : Z) : list A :=
  map f (Zrange 0 n).

Definition AtMostOneSwap (before after : list Z) : Prop :=
  after = before \/ exists i j,
    0 <= i < Zlength before /\ 0 <= j < Zlength before /\
    after = replace_Znth j (Znth i before 0)
              (replace_Znth i (Znth j before 0) before).

Definition PairDistanceSum (a b : list Z) : Z :=
  fold_right Z.add 0 (Zmap_range (fun i => Z.abs (Znth i a 0 - Znth i b 0))
                               (Zlength a)).

Definition Pre (a b : list Z) : Prop :=
  1 <= Zlength a <= 200000 /\ Zlength b = Zlength a /\
  Forall (fun x => 1 <= x <= 1000000000) a /\
  Forall (fun x => 1 <= x <= 1000000000) b.

Definition Spec (a b : list Z) (out : Z) : Prop :=
  min_value_of_subset Z.le (AtMostOneSwap b) (PairDistanceSum a) out.

(** A [Seg] value is represented by its left and right endpoints. *)
Definition store_segment
    (base : addr) (i : Z) (segment : Z * Z) : Assertion :=
  let p := base + i * sizeof_front_end_type (FET_alias "<anonymous struct>") in
  (&((p) # "anonymous struct 1" ->ₛ "l") # Int |-> fst segment) **
  (&((p) # "anonymous struct 1" ->ₛ "r") # Int |-> snd segment).

Definition undef_segment (base : addr) (i : Z) : Assertion :=
  let p := base + i * sizeof_front_end_type (FET_alias "<anonymous struct>") in
  (&((p) # "anonymous struct 1" ->ₛ "l") # Int |->_) **
  (&((p) # "anonymous struct 1" ->ₛ "r") # Int |->_).

Module SegArray.
Definition full
    (base : addr) (n : Z) (segments : list (Z * Z)) : Assertion :=
  store_array store_segment base n segments.
Definition undef_full (base : addr) (n : Z) : Assertion :=
  store_undef_array undef_segment base n.
End SegArray.

Require Import Coq.Sorting.Permutation.
