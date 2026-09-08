Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import PVbench.Codeforces.examples_shard01.P048_1607E_robot_on_the_board_1.rocq.spec_lib.

Import ListNotations.
Local Open Scope Z_scope.

Definition RowOffset (s : list Z) (q : Z) : Z :=
  (fold_right Z.add 0)
    (map fst (map Delta (sublist 0 q s))).

Definition ColOffset (s : list Z) (q : Z) : Z :=
  (fold_right Z.add 0)
    (map snd (map Delta (sublist 0 q s))).

(* [PrefixWindow] gives the geometric meaning of the loop state: [r,c] is
   the displacement after [q] commands, and the four bounds are the attained
   extrema of every displacement in that prefix (including the empty one). *)
Definition PrefixWindow
    (s : list Z) (q r c minr maxr minc maxc : Z) : Prop :=
  0 <= q <= Zlength s /\
  r = RowOffset s q /\ c = ColOffset s q /\
  minr <= 0 <= maxr /\ minc <= 0 <= maxc /\
  (forall p, 0 <= p <= q ->
     minr <= RowOffset s p <= maxr /\
     minc <= ColOffset s p <= maxc) /\
  (exists p, 0 <= p <= q /\ RowOffset s p = minr) /\
  (exists p, 0 <= p <= q /\ RowOffset s p = maxr) /\
  (exists p, 0 <= p <= q /\ ColOffset s p = minc) /\
  (exists p, 0 <= p <= q /\ ColOffset s p = maxc).

Definition WindowFits
    (n m minr maxr minc maxc : Z) : Prop :=
  maxr - minr < n /\ maxc - minc < m.

(* This is the stable exit state of the scan.  It records the extremal window
   for an optimal feasible prefix without baking the C loop into the spec. *)
Definition OptimalPrefixWindow
    (n m : Z) (s : list Z) (minr maxr minc maxc : Z) : Prop :=
  exists q r c,
    PrefixWindow s q r c minr maxr minc maxc /\
    WindowFits n m minr maxr minc maxc /\
    max_value_of_subset Z.le
      (fun q' => exists st,
         1 <= fst st <= n /\ 1 <= snd st <= m /\
         Executes n m s st q')
      (fun x => x) q.
