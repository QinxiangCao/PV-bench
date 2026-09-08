Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import Coq.Sorting.Permutation.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition Pre (a : list Z) : Prop :=
  2 <= Zlength a <= 100000 /\
  Forall (fun x => 1 <= x <= Zlength a) a /\
  exists x i j, 0 <= i < Zlength a /\ 0 <= j < Zlength a /\ i <> j /\
    Znth i a 0 = x /\ Znth j a 0 = x.

Definition CountPrefix (a : list Z) (i : Z) (counts : list Z) : Prop :=
  Zlength counts = Zlength a + 1 /\
  forall value,
    0 <= value <= Zlength a ->
    Znth value counts 0 =
      Z.of_nat (count_occ Z.eq_dec (sublist 0 i a) value).

Definition MaximumFrequencyPrefix
    (counts : list Z) (i mx multiplicity : Z) : Prop :=
  1 <= i <= Zlength counts /\
  (forall value,
    1 <= value < i ->
    Znth value counts 0 <= mx) /\
  ((i = 1 /\ mx = 0 /\ multiplicity = 0) \/
   (1 < i /\
    (exists value,
      1 <= value < i /\ Znth value counts 0 = mx) /\
    multiplicity =
      Z.of_nat (count_occ Z.eq_dec (sublist 1 i counts) mx))).

(* This is the closed-form characterization of the arrangement optimum used
   by the solver: [mx] is the largest input multiplicity and [multiplicity]
   is the number of values attaining it.  Unlike a loop mirror, the
   characterization depends only on the complete mathematical frequency
   profile of the input. *)
Definition Spec (a : list Z) (out : Z) : Prop :=
  exists counts mx multiplicity,
    CountPrefix a (Zlength a) counts /\
    MaximumFrequencyPrefix counts (Zlength a + 1) mx multiplicity /\
    out = (Zlength a - multiplicity) / (mx - 1) - 1.
