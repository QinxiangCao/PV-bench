Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import PVbench.Codeforces.examples_shard01.P009_275A_lights_out.rocq.spec_lib.

Import ListNotations.
Local Open Scope Z_scope.

Definition lights_di : list Z := [0; -1; 1; 0; 0].

Definition lights_dj : list Z := [0; 0; 0; -1; 1].

(* Mathematical meaning of a row-major prefix of the output grid.  Cells at
   and after [k] remain unconstrained, which permits the initially undefined
   output storage to be represented by an arbitrary 3-by-3 logical grid. *)

Definition TogglePrefix
    (g : list (list Z)) (i j d tog : Z) : Prop :=
  (d = 0 /\ tog = 0) \/
  (d = 1 /\ tog = cell g i j) \/
  (d = 2 /\ tog = cell g i j + cell g (i - 1) j) \/
  (d = 3 /\ tog = cell g i j + cell g (i - 1) j + cell g (i + 1) j) \/
  (d = 4 /\ tog = cell g i j + cell g (i - 1) j + cell g (i + 1) j +
                        cell g i (j - 1)) \/
  (d = 5 /\ tog = toggles g i j).

(* A canonical staged view of one output row.  Positions before the row-major
   frontier [k] are initialized to their final values; every later position is
   still genuinely uninitialized and is represented by [None]. *)

Definition output_bit (g : list (list Z)) (i j : Z) : Z :=
  if Z.even (toggles g i j) then 1 else 0.

Definition staged_output_cell
    (g : list (list Z)) (i j k : Z) : option Z :=
  if (3 * i + j <? k)%Z then Some (output_bit g i j) else None.

Definition staged_output_row
    (g : list (list Z)) (i k : Z) : list (option Z) :=
  [staged_output_cell g i 0 k;
   staged_output_cell g i 1 k;
   staged_output_cell g i 2 k].

Definition staged_output (g : list (list Z)) (k : Z) : list (list (option Z)) :=
  [staged_output_row g 0 k; staged_output_row g 1 k; staged_output_row g 2 k].

Definition out_grid (g : list (list Z)) : list (list Z) :=
  [[output_bit g 0 0; output_bit g 0 1; output_bit g 0 2];
   [output_bit g 1 0; output_bit g 1 1; output_bit g 1 2];
   [output_bit g 2 0; output_bit g 2 1; output_bit g 2 2]].
