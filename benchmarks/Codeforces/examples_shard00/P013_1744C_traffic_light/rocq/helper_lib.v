Require Import PVbench.Codeforces.examples_shard00.P013_1744C_traffic_light.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

(** The character observed at an index of the doubled, cyclic scan. *)
Definition DoubledTrafficChar (s : list Z) (index : Z) : Z :=
  Znth (index mod Zlength s) s 0.

(** [next] is the first green strictly after [i] in the part of the
    conceptual doubled string that has already been scanned.  The [-1]
    case describes the initial empty suffix. *)
Definition FirstProcessedGreen (s : list Z) (i next : Z) : Prop :=
  (next = -1 /\
   forall j,
     i < j < 2 * Zlength s ->
     DoubledTrafficChar s j <> 103) \/
  (i < next < 2 * Zlength s /\
   DoubledTrafficChar s next = 103 /\
   forall j,
     i < j < next ->
     DoubledTrafficChar s j <> 103).

(** [ans] is the greatest circular wait among original-string positions
    already covered by the descending scan.  The default makes the empty
    processed set at loop initialization have value zero. *)
Definition ProcessedTrafficMaximum
    (current : Z) (s : list Z) (i ans : Z) : Prop :=
  max_value_of_subset_with_default Z.le
    (fun candidate : Z * Z =>
      i < fst candidate /\
      Znth (fst candidate) s 0 = current /\
      WaitsUntilGreen s (fst candidate) (snd candidate))
    snd 0 ans.

Definition TrafficScanState
    (current : Z) (s : list Z) (i ans next : Z) : Prop :=
  FirstProcessedGreen s i next /\
  ProcessedTrafficMaximum current s i ans.
