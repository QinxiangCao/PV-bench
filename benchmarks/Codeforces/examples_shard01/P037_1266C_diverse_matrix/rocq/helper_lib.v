Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition ConstructionIndices (n : Z) : list Z :=
  map Z.of_nat (seq 0 (Z.to_nat n)).

Definition ConstructionCell (r c i j : Z) : Z :=
  if Z.eqb r 1 then j + 2 else (c + i + 1) * (j + 1).

Definition StagedConstructionCell
    (r c i j frontier : Z) : option Z :=
  if (i * c + j <? frontier)%Z
  then Some (ConstructionCell r c i j)
  else None.

Definition StagedConstructionRow
    (r c i frontier : Z) : list (option Z) :=
  map (fun j => StagedConstructionCell r c i j frontier)
      (ConstructionIndices c).

Definition StagedConstruction
    (r c frontier : Z) : list (list (option Z)) :=
  map (fun i => StagedConstructionRow r c i frontier)
      (ConstructionIndices r).

(* Stable body-level meaning of the partially initialized output.  Machine
   bounds and spatial ownership remain explicit in the C invariants. *)

Definition ConstructionPrefix
    (r c : Z) (rows : list (list (option Z))) (frontier : Z) : Prop :=
  rows = StagedConstruction r c frontier.
