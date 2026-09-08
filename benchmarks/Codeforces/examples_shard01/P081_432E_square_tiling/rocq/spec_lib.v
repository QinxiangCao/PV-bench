(* Codeforces 432/E - Square Tiling: colour every cell of an n x m table so that
   each monochrome connected region is a square, choosing the lexicographically
   smallest such colouring. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import ListLib.General.Presuffix.

Import ListNotations.
Local Open Scope Z_scope.

(* A grid position (row, column). *)
Definition Cell := (Z * Z)%type.

(* Two cells share a side: their Manhattan distance is 1. *)
Definition AdjCell (p q : Cell) : Prop :=
  Z.abs (fst p - fst q) + Z.abs (snd p - snd q) = 1.

(* q lies in p's monochrome region: some path of side-adjacent cells, all inside
   the grid and all of p's colour, runs from p to q. *)
Definition SameColorPath (g : list (list Z)) (p q : Cell) : Prop :=
  exists path : list Cell, path <> [] /\ Znth 0 path (0, 0) = p /\ Znth (Zlength path - 1) path (0, 0) = q /\
  Forall (fun x => 0 <= fst x < Zlength g /\ 0 <= snd x < Zlength (Znth 0 g []) /\
    Znth (snd x) (Znth (fst x) g []) 0 = Znth (snd p) (Znth (fst p) g []) 0) path /\
  forall i, 0 <= i < Zlength path - 1 -> AdjCell (Znth i path (0, 0)) (Znth (i + 1) path (0, 0)).

(* g is a legal colouring:
     |g| = n rows of m entries, each an uppercase letter, code 65..90
     every cell p lies in a square block [r, r+side) x [c, c+side) inside the grid
     and that block is exactly p's monochrome region
   so each connected region of one colour is a square. *)
Definition SquareTiling (n m : Z) (g : list (list Z)) : Prop :=
  (Zlength g = n /\ Forall (fun row => Zlength row = m) g) /\ Forall (Forall (fun c => 65 <= c <= 90)) g /\
  forall p, 0 <= fst p < n -> 0 <= snd p < m -> exists r c side,
    side >= 1 /\ r <= fst p < r + side /\ c <= snd p < c + side /\ r >= 0 /\ c >= 0 /\ r + side <= n /\ c + side <= m /\
    forall q, 0 <= fst q < n -> 0 <= snd q < m ->
      (SameColorPath g p q <-> r <= fst q < r + side /\ c <= snd q < c + side).

(* The cells in reading order, row by row -- the order in which the statement
   compares two colourings. *)
Definition Flatten (g : list (list Z)) : list Z := concat g.
Definition Pre (n m : Z) : Prop :=
  (* Every clause below is stated explicitly in the P081 solver Require, which
     therefore omits the Pre(...) call:
       1 <= n <= 100 /\ 1 <= m <= 100. *)
  True.

(* out is a legal colouring and Flatten(out) <= Flatten(q) lexicographically for
   every other legal q, i.e. out is the smallest one in reading order. *)
Definition Spec (n m : Z) (out : list (list Z)) : Prop :=
  SquareTiling n m out /\ forall q, SquareTiling n m q -> ((Flatten out) = (Flatten q) \/ ((exists i, 0 <= i < Z.min (Zlength (Flatten out)) (Zlength (Flatten q)) /\
    (forall j, 0 <= j < i -> Znth j (Flatten out) 0 = Znth j (Flatten q) 0) /\
    Znth i (Flatten out) 0 < Znth i (Flatten q) 0) \/
  (Zlength (Flatten out) < Zlength (Flatten q) /\ is_prefix (Flatten out) (Flatten q)))).
