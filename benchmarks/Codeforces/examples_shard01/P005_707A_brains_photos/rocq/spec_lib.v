(* Codeforces 707/A - Brain's Photos: decide whether an n x m photo is coloured
   -- prints #Color -- or black-and-white. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Signature: solve_case(photo : list (list Z)) -> bool; true means #Color.
   A pixel is one of the six colour codes 'C' = 67, 'M' = 77, 'Y' = 89,
   'W' = 87, 'G' = 71, 'B' = 66. *)
Definition Pixel (c : Z) : Prop :=
  c = 67 \/ c = 77 \/ c = 89 \/ c = 87 \/ c = 71 \/ c = 66.

Definition Pre (photo : list (list Z)) : Prop :=
  (* The solver Require states these constraints explicitly:
       1 <= Zlength photo <= 100 /\
       exists m, 1 <= m <= 100 /\
         Forall (fun row => Zlength row = m /\ Forall Pixel row) photo. *)
  True.

(* Some photo[i][j] is 'C', 'M' or 'Y' (67, 77, 89) -- the coloured codes; the
   remaining W, G, B are the black-and-white ones. *)
Definition HasColor (photo : list (list Z)) : Prop :=
  exists row c, In row photo /\ In c row /\ (c = 67 \/ c = 77 \/ c = 89).

(* out = true exactly when the photo has a coloured pixel, i.e. #Color is printed. *)
Definition Spec (photo : list (list Z)) (out : bool) : Prop :=
  (out = true /\ HasColor photo) \/ (out = false /\ ~HasColor photo).

(* C encoding of the verdict: true returns 1, false returns 0. *)
Definition SolverReturnBridge (out : bool) (ret : Z) : Prop :=
  (out = true /\ ret = 1) \/ (out = false /\ ret = 0).
