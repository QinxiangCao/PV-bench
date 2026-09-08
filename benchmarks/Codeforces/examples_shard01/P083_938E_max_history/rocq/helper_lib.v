Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition ModPower (base exponent result : Z) : Prop :=
  result = (base ^ exponent) mod 1000000007.

(* ---------------------------------------------------------------- *)
(* Internal predicates: the mathematical state of the C loops.       *)
(* ---------------------------------------------------------------- *)

(* Square-and-multiply invariant of [power]. *)

Definition PowerLoopState
    (original_base original_exponent accumulator current_base
     remaining_exponent : Z) : Prop :=
  (accumulator * (current_base ^ remaining_exponent)) mod 1000000007 =
  (original_base ^ original_exponent) mod 1000000007.

(* Factorial as a plain mathematical function. *)

Fixpoint fact_nat (n : nat) : Z :=
  match n with
  | O => 1
  | S k => Z.of_nat (S k) * fact_nat k
  end.

Definition Zfact (n : Z) : Z := fact_nat (Z.to_nat n).

(* The accumulator of the factorial loop holds (i-1)! reduced mod p. *)

Definition FactorialModState (i value : Z) : Prop :=
  value = (Zfact (i - 1)) mod 1000000007.

(* Index [i] starts a maximal run of equal values of [l] (or is an end). *)

Definition GroupBoundary (l : list Z) (i : Z) : Prop :=
  i = 0 \/ i = Zlength l \/
  (0 < i < Zlength l /\ Znth (i - 1) l 0 < Znth i l 0).

(* Size of the >=-class of [v] inside [l]; it is Permutation-invariant. *)

Definition count_ge (l : list Z) (v : Z) : Z :=
  Zlength (filter (fun w => Z.leb v w) l).

(* Closed-form contribution of one element value of [l]:
   [v] is added once per ordering in which it is first among its >=-class,
   which happens in (Zlength l)! / count_ge l v of them, and only when some
   strictly larger element exists at all. *)

Definition contrib (l : list Z) (v : Z) : Z :=
  if existsb (fun w => Z.ltb v w) l
  then v * (Zfact (Zlength l) / count_ge l v)
  else 0.

Definition contrib_list (l : list Z) : list Z := map (contrib l) l.

(* The scan accumulator [total] is the mod-reduced closed-form sum over the
   first [i] entries of [l]. *)

Definition ContribPrefixSum (l : list Z) (i total : Z) : Prop :=
  total = (fold_right Z.add 0 (sublist 0 i (contrib_list l))) mod 1000000007.

(* ---------------------------------------------------------------- *)
(* Executable witnesses for the existentials of [Spec] (proof side). *)
(* ---------------------------------------------------------------- *)
