Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import PVbench.Codeforces.examples_shard01.P049_411B_multi_core_processor.rocq.spec_lib.

Import ListNotations.
Local Open Scope Z_scope.

Definition lock_times_before (times : list Z) (t : Z) : list Z :=
  map (fun u => if u <? t then u else 0) times.

(* A cell is dead after [upto] cycles exactly when some already locked core
   addressed it at the cycle where that core locked. *)

Definition CellWasDead
    (ins : list (list Z)) (times : list Z) (upto cell : Z) : Prop :=
  exists i,
    0 <= i < Zlength ins /\
    1 <= Znth i times 0 <= upto /\
    Znth (Znth i times 0 - 1) (Znth i ins []) 0 = cell.

(* [times] gives the earliest trigger seen in cycles 1..upto, or zero when no
   such trigger has occurred yet.  This is the mathematical prefix form of
   the frozen [Spec], independent of the concrete loop organization. *)

Definition LockTimesThrough
    (ins : list (list Z)) (times : list Z) (upto : Z) : Prop :=
  Zlength times = Zlength ins /\
  forall i, 0 <= i < Zlength ins ->
    ((Znth i times 0 = 0 /\
      forall t, 1 <= t <= upto -> ~ LockTrigger ins times i t) \/
     (1 <= Znth i times 0 <= upto /\
      LockTrigger ins times i (Znth i times 0) /\
      forall t, 1 <= t < Znth i times 0 -> ~ LockTrigger ins times i t)).

(* Logical meaning of the persistent [cell_locked] scratch array. *)

Definition DeadCellsThrough
    (ins : list (list Z)) (times : list Z)
    (k upto : Z) (dead : list Z) : Prop :=
  Zlength dead = 105 /\
  Znth 0 dead 0 = 0 /\
  forall cell, 1 <= cell <= k ->
    0 <= Znth cell dead 0 <= 1 /\
    (Znth cell dead 0 = 1 <-> CellWasDead ins times upto cell).

Definition DeadCellsBefore
    (ins : list (list Z)) (times : list Z)
    (k t : Z) (dead : list Z) : Prop :=
  DeadCellsThrough ins (lock_times_before times t) k (t - 1) dead.

(* During the first core scan of cycle [t], only writers to cells that were
   already dead before [t] are locked. *)

Definition DirectLockScan
    (ins : list (list Z)) (times : list Z) (t scanned : Z) : Prop :=
  let old := lock_times_before times t in
  LockTimesThrough ins old (t - 1) /\
  Zlength times = Zlength ins /\
  forall i, 0 <= i < Zlength ins ->
    let cell := Znth (t - 1) (Znth i ins []) 0 in
    (Znth i times 0 = t <->
       i < scanned /\ Znth i old 0 = 0 /\ cell <> 0 /\
       CellWasDead ins old (t - 1) cell) /\
    (Znth i times 0 <> t -> Znth i times 0 = Znth i old 0).

(* Exact live-writer histogram after scanning cores [0,scanned). *)

Definition WriterCounts
    (ins : list (list Z)) (times : list Z)
    (t scanned k : Z) (counts : list Z) : Prop :=
  let old := lock_times_before times t in
  Zlength counts = k + 1 /\
  forall cell, 0 <= cell <= k ->
    Znth cell counts 0 =
      #(fun i : Z =>
          0 <= i < scanned /\
          Znth i old 0 = 0 /\
          cell <> 0 /\
          Znth (t - 1) (Znth i ins []) 0 = cell /\
          ~ CellWasDead ins old (t - 1) cell) /\
    0 <= Znth cell counts 0 <= scanned.

(* Cells below [completed] have had this cycle's collision mark applied. *)

Definition CellMarksPrefix
    (ins : list (list Z)) (times counts : list Z)
    (k t completed : Z) (dead : list Z) : Prop :=
  let old := lock_times_before times t in
  Zlength dead = 105 /\
  Znth 0 dead 0 = 0 /\
  forall cell, 1 <= cell <= k ->
    0 <= Znth cell dead 0 <= 1 /\
    (Znth cell dead 0 = 1 <->
       CellWasDead ins old (t - 1) cell \/
       (cell < completed /\ 2 <= Znth cell counts 0)).

(* Same-cycle collision closure: all colliding cells below [cell_cursor] are
   complete, while [core_done] writers of the current cell have been closed. *)

Definition CollisionClosurePrefix
    (ins : list (list Z)) (times counts : list Z)
    (t cell_cursor core_done : Z) : Prop :=
  let old := lock_times_before times t in
  LockTimesThrough ins old (t - 1) /\
  Zlength times = Zlength ins /\
  forall i, 0 <= i < Zlength ins ->
    let cell := Znth (t - 1) (Znth i ins []) 0 in
    (Znth i times 0 = t <->
       Znth i old 0 = 0 /\ cell <> 0 /\
       (CellWasDead ins old (t - 1) cell \/
        (2 <= Znth cell counts 0 /\
         (cell < cell_cursor \/
          (cell = cell_cursor /\ i < core_done))))) /\
    (Znth i times 0 <> t -> Znth i times 0 = Znth i old 0).
