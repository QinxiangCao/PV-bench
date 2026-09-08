(* Codeforces 459/A - Pashmak and Garden: two trees stand on corners of an
   axis-parallel square; print the other two corners, or -1 if there are none. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.

Import ListNotations.
Local Open Scope Z_scope.

(* Signature: solve_case(x1 y1 x2 y2:Z)->Answer. The input line holds the four
   coordinates of the two known trees; the answer is either "-1" or the four
   coordinates of the two remaining trees. *)
Inductive Answer := NoSolution | Trees (x3 y3 x4 y4 : Z).

(* The four trees stand on the vertices of a square whose sides are parallel to
   the axes: their coordinates are, in some order, the four corners of the
   square [xl, xh] x [yl, yh], whose two side lengths agree. *)
Definition SquareCorners (x1 y1 x2 y2 x3 y3 x4 y4 : Z) : Prop :=
  exists xl xh yl yh,
    xl < xh /\ yl < yh /\ xh - xl = yh - yl /\
    Permutation [(x1, y1) ; (x2, y2) ; (x3, y3) ; (x4, y4)]
                [(xl, yl) ; (xl, yh) ; (xh, yl) ; (xh, yh)].

(* The statement additionally requires every printed coordinate to lie in
   [-1000, 1000]. *)
Definition Printable (x3 y3 x4 y4 : Z) : Prop :=
  Forall (fun v => - 1000 <= v <= 1000) [x3 ; y3 ; x4 ; y4].

Definition Pre (x1 y1 x2 y2 : Z) : Prop :=
  (* The coordinate ranges are stated explicitly in the solver Require:
       -100 <= x1 <= 100 /\ -100 <= y1 <= 100 /\
       -100 <= x2 <= 100 /\ -100 <= y2 <= 100. *)
  ~ (x1 = x2 /\ y1 = y2).

(* The two remaining trees complete the square, and their coordinates may be
   printed. *)
Definition CompletesSquare (x1 y1 x2 y2 x3 y3 x4 y4 : Z) : Prop :=
  Printable x3 y3 x4 y4 /\ SquareCorners x1 y1 x2 y2 x3 y3 x4 y4.

(* No pair of trees completes the square — the "-1" case. *)
Definition NoCompletion (x1 y1 x2 y2 : Z) : Prop :=
  ~exists x3 y3 x4 y4, CompletesSquare x1 y1 x2 y2 x3 y3 x4 y4.

(* out = Trees x3 y3 x4 y4    those two trees complete the square and may be
                             printed, i.e. lie in [-1000, 1000]
   out = NoSolution          no such pair exists, so -1 is printed *)
Definition Spec (x1 y1 x2 y2 : Z) (out : Answer) : Prop :=
  match out with
  | Trees x3 y3 x4 y4 => CompletesSquare x1 y1 x2 y2 x3 y3 x4 y4
  | NoSolution => NoCompletion x1 y1 x2 y2
  end.
