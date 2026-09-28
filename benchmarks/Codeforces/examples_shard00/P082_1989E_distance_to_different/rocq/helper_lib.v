Require Export PVbench.Codeforces.examples_shard00.P082_1989E_distance_to_different.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

(* The following declarations are an append-only mathematical interface for the
   column-major dynamic-programming table used by the implementation. *)
Definition P082Modulus : Z := 998244353.

Definition P082Index (k row col : Z) : Z := row * (k + 1) + col.

Definition P082Norm (x : Z) : Z := x mod P082Modulus.

Definition P082InitState
    (n k next_row : Z) (dp pref : list Z) : Prop :=
  Zlength dp = (n + 1) * (k + 1) /\
  Zlength pref = (n + 1) * (k + 1) /\
  (forall q, 0 <= q < Zlength dp ->
     0 <= Znth q dp 0 < P082Modulus /\
     0 <= Znth q pref 0 < P082Modulus) /\
  (forall row, 1 <= row < next_row ->
     Znth (P082Index k row 1) dp 0 = 1 /\
     Znth (P082Index k row 1) pref 0 = row) /\
  (forall row, next_row <= row <= n ->
     Znth (P082Index k row 1) dp 0 = 0 /\
     Znth (P082Index k row 1) pref 0 = 0) /\
  (forall row col, 0 <= row <= n -> 0 <= col <= k ->
     (row = 0 \/ col = 0 \/ 2 <= col) ->
     Znth (P082Index k row col) dp 0 = 0 /\
     Znth (P082Index k row col) pref 0 = 0).

Definition P082BaseColumns
    (n k : Z) (dp pref : list Z) : Prop :=
  Zlength dp = (n + 1) * (k + 1) /\
  Zlength pref = (n + 1) * (k + 1) /\
  (forall q, 0 <= q < Zlength dp ->
     0 <= Znth q dp 0 < P082Modulus /\
     0 <= Znth q pref 0 < P082Modulus) /\
  (forall row, 1 <= row <= n ->
     Znth (P082Index k row 1) dp 0 = 1 /\
     Znth (P082Index k row 1) pref 0 = row) /\
  (forall col, 0 <= col <= k ->
     Znth (P082Index k 0 col) dp 0 = 0 /\
     Znth (P082Index k 0 col) pref 0 = 0).

Definition P082RawCell
    (k row col : Z) (dp pref : list Z) : Z :=
  Znth (P082Index k (row - 1) (col - 1)) pref 0 -
  (if Z_le_dec 3 row
   then Znth (P082Index k (row - 2) (col - 1)) dp 0
   else 0) +
  (if Z.eq_dec col k
   then Znth (P082Index k (row - 1) k) pref 0 -
        (if Z_le_dec 3 row
         then Znth (P082Index k (row - 2) k) dp 0
         else 0)
   else 0).

Definition P082CellEquation
    (k row col : Z) (dp pref : list Z) : Prop :=
  Znth (P082Index k row col) dp 0 =
    P082Norm (P082RawCell k row col dp pref) /\
  Znth (P082Index k row col) pref 0 =
    P082Norm
      (Znth (P082Index k (row - 1) col) pref 0 +
       Znth (P082Index k row col) dp 0).

Definition P082ColumnsState
    (n k next_col : Z) (dp pref : list Z) : Prop :=
  P082BaseColumns n k dp pref /\
  forall col row, 2 <= col < next_col -> 1 <= row <= n ->
    P082CellEquation k row col dp pref.

Definition P082ColumnProgress
    (n k col next_row : Z) (dp pref : list Z) : Prop :=
  P082ColumnsState n k col dp pref /\
  forall row, 1 <= row < next_row ->
    P082CellEquation k row col dp pref.

Definition P082FinalExpression (k n : Z) (dp : list Z) : Z :=
  P082Norm
    (Znth (P082Index k n k) dp 0 +
     Znth (P082Index k (n - 2) (k - 1)) dp 0 +
     Znth (P082Index k (n - 2) k) dp 0).

Definition P082FinalValue (n k : Z) (dp : list Z) (out : Z) : Prop :=
  out = P082FinalExpression k n dp /\ Spec n k out.

Require Import Coq.micromega.Lia.

Definition P082ExactCoreCount (size runs : Z) : Z :=
  #(P082CoreComposition size runs).

Definition P082SaturatedCoreCount (size threshold : Z) : Z :=
  sum_range threshold size (fun runs => P082ExactCoreCount size runs).

Definition P082PrefixCoreCount
    (size threshold cap : Z) : Z :=
  sum_range 0 size
    (fun total =>
       if Z_lt_dec threshold cap
       then P082ExactCoreCount total threshold
       else P082SaturatedCoreCount total threshold).

Definition P082SemanticCell
    (k row col : Z) (dp pref : list Z) : Prop :=
  Znth (P082Index k row col) dp 0 =
    P082Norm
      (if Z_lt_dec col k
       then P082ExactCoreCount row col
       else P082SaturatedCoreCount row k) /\
  Znth (P082Index k row col) pref 0 =
    P082Norm (P082PrefixCoreCount row col k).

Definition P082SemanticInit
    (n k next_row : Z) (dp pref : list Z) : Prop :=
  forall row, 0 <= row < next_row ->
    P082SemanticCell k row 1 dp pref.

Definition P082SemanticColumns
    (n k next_col : Z) (dp pref : list Z) : Prop :=
  forall col row, 1 <= col < next_col -> 0 <= row <= n ->
    P082SemanticCell k row col dp pref.

Definition P082SemanticProgress
    (n k col next_row : Z) (dp pref : list Z) : Prop :=
  P082SemanticColumns n k col dp pref /\
  forall row, 0 <= row < next_row ->
    P082SemanticCell k row col dp pref.

Require Import Coq.Sorting.Permutation.

From SumLib Require Import ZRect.
