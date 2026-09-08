
Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.

Local Open Scope Z_scope.

Definition PrefixImbalance (a : list Z) (upto : Z) : Z :=
  ListLib.sum (sublist 0 upto a) -
  upto * (ListLib.sum a / Zlength a).

Definition PrefixTransportCost (a : list Z) (edges : Z) : Z :=
  sum (fun k : Z => 0 <= k < edges)
      (fun k => Z.abs (PrefixImbalance a (k + 1))).
