Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import PVbench.Codeforces.examples_shard01.P025_1384A_common_prefixes.rocq.spec_lib.

Import ListNotations.
Local Open Scope Z_scope.

(* The following predicates describe stable partial output states.  They are
   deliberately about the rows already materialised, not about executions of
   the C loops that create them. *)
Definition BinaryAnswerString (s : list Z) : Prop :=
  Zlength s = 200 /\
  forall q, 0 <= q < 200 -> Znth q s 0 = 97 \/ Znth q s 0 = 98.

Definition EncodedRow (s : list Z) : list (option Z) :=
  map (fun z => Some z) (s ++ [0]).

Definition UnwrittenRow : list (option Z) := repeat None 201%nat.

Definition PrefixSpec (a : list Z) (done : Z) (out : list (list Z)) : Prop :=
  Zlength out = done /\
  Forall BinaryAnswerString out /\
  forall i, 0 <= i < done - 1 ->
    LCP (Znth i out []) (Znth (i + 1) out []) (Znth i a 0).

Definition ProducedRows
    (a : list Z) (done : Z) (rows : list (list (option Z))) : Prop :=
  0 <= done <= Zlength a + 1 /\
  exists out,
    PrefixSpec a done out /\
    rows = map EncodedRow out ++
      repeat UnwrittenRow (Z.to_nat (Zlength a + 1 - done)).

Definition InitialRowProgress
    (n j : Z) (rows : list (list (option Z))) : Prop :=
  0 <= j <= 200 /\
  rows =
    (map (fun z => Some z) (repeat 97 (Z.to_nat j)) ++
      repeat None (Z.to_nat (201 - j))) ::
    repeat UnwrittenRow (Z.to_nat n).

Definition CopyRowPrefix (s : list Z) (j : Z) : list (option Z) :=
  map (fun z => Some z) (sublist 0 j (s ++ [0])) ++
  repeat None (Z.to_nat (201 - j)).

Definition CopyProgress
    (a : list Z) (i j : Z) (rows : list (list (option Z))) : Prop :=
  0 <= i < Zlength a /\
  0 <= j <= 201 /\
  exists out,
    PrefixSpec a (i + 1) out /\
    rows = map EncodedRow out ++
      CopyRowPrefix (Znth i out []) j ::
      repeat UnwrittenRow (Z.to_nat (Zlength a - i - 1)).
