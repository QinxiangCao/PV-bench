(* Codeforces 1031/A - Golden Plate: count the cells of a w x h grid covered by the
   k gilded rings, ring i being the border of the rectangle inset 2i on each side. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Signature: solver(w, h, k) -> Z.  Pre is True: the domain
     3 <= w, h <= 100,   1 <= k,   4k <= min(w, h) + 1
   is written out literally in solver's Require clause, which never calls Pre. *)
Definition Pre (w h k : Z) : Prop :=
  True.

(* Cell (row, col) is gilded: it lies on ring i for some i < k, ring i being the
   border of the rectangle [2i, w-1-2i] x [2i, h-1-2i].
     0 <= row < w, 0 <= col < h      the cell is on the plate
     exists i, 0 <= i < k            some ring covers it, and on that ring
       row = 2i or w-1-2i, 2i <= col <= h-1-2i     its top / bottom edge, or
       col = 2i or h-1-2i, 2i <= row <= w-1-2i     its left / right edge
   The two cases overlap at the ring's corners, which is harmless: the answer
   counts cells, i.e. their union. *)
Definition RingCell (w h k row col : Z) : Prop :=
  0 <= row < w /\ 0 <= col < h /\
  exists i, 0 <= i < k /\
    ((row = 2 * i \/ row = w - 1 - 2 * i) /\ 2 * i <= col < h - 2 * i \/
     (col = 2 * i \/ col = h - 1 - 2 * i) /\ 2 * i <= row < w - 2 * i).

(* out = #{ z : 0 <= z < w*h and RingCell(z / h, z mod h) }, the number of gilded
   cells, addressed by the row-major index z = row * h + col. *)
Definition Spec (w h k out : Z) : Prop :=
  out = #(fun z : Z =>
    0 <= z < w * h /\ RingCell w h k (z / h) (z mod h)).
