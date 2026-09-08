Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import PVbench.Codeforces.examples_shard01.P066_1288D_minimax_problem.rocq.spec_lib.

Import ListNotations.
Local Open Scope Z_scope.

Definition PairAtLeast
    (rows : list (list Z)) (threshold i j : Z) : Prop :=
  0 <= i < Zlength rows /\
  0 <= j < Zlength rows /\
  forall c,
    0 <= c < Zlength (Znth 0 rows []) ->
    threshold <= CombinedEntry rows i j c.

Definition FeasibleAtThreshold
    (rows : list (list Z)) (threshold : Z) : Prop :=
  exists i j, PairAtLeast rows threshold i j.

(* The stable mathematical meaning of a partially constructed threshold mask.
   Machine ranges and the matrix resource stay explicit in the C invariant. *)

Definition RowMaskPrefix
    (rows : list (list Z))
    (threshold row cols mask : Z) : Prop :=
  0 <= mask < 2 ^ cols /\
  forall c,
    0 <= c < cols ->
    (Z.testbit mask c = true <->
     threshold <= Znth c (Znth row rows []) 0).

(* [reps] is complete and sound for the rows in [0, processed_rows). *)

Definition RepresentativePrefix
    (rows : list (list Z))
    (threshold width processed_rows : Z)
    (reps : list Z) : Prop :=
  forall mask,
    0 <= mask < 2 ^ width ->
    ((Znth mask reps (-1) = -1 /\
      forall row,
        0 <= row < processed_rows ->
        ~ RowMaskPrefix rows threshold row width mask) \/
     (exists row,
        0 <= row < processed_rows /\
        Znth mask reps (-1) = row /\
        RowMaskPrefix rows threshold row width mask)).

(* All represented mask pairs preceding [(first_mask,next_second_mask)] in
   lexicographic search order have been ruled out. *)

Definition NoCoverPrefix
    (reps : list Z) (full first_mask next_second_mask : Z) : Prop :=
  forall s u,
    0 <= s <= full ->
    0 <= u <= full ->
    (s < first_mask \/ (s = first_mask /\ u < next_second_mask)) ->
    0 <= Znth s reps (-1) ->
    0 <= Znth u reps (-1) ->
    Z.lor s u <> full.

Definition OptimalPairScore (rows : list (list Z)) (best : Z) : Prop :=
  max_value_of_subset Z.le
    (fun v => exists i j, PairScore rows i j v)
    (fun x => x) best.

Definition SolverSearchMeaning
    (rows : list (list Z)) (lo hi current_i current_j : Z) : Prop :=
  exists best,
    OptimalPairScore rows best /\
    lo <= best <= hi /\
    PairAtLeast rows lo current_i current_j.
