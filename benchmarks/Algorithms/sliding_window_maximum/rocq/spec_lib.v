Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition SWMInputSafe (l : list Z) (n k : Z) : Prop :=
  1 <= k /\
  k <= n /\
  n <= 100000 /\
  Zlength l = n /\
  forall idx,
    0 <= idx < n ->
    -10000 <= Znth idx l 0 <= 10000.
Definition WindowMaxValue (l : list Z) (lo hi ans : Z) : Prop :=
  exists pos,
    lo <= pos < hi /\
    ans = Znth pos l 0 /\
    forall idx, lo <= idx < hi -> Znth idx l 0 <= ans.
Definition SlidingWindowMaximum (l : list Z) (k : Z) (out : list Z) : Prop :=
  Zlength out = Zlength l - k + 1 /\
  forall idx,
    0 <= idx < Zlength out ->
    WindowMaxValue l idx (idx + k) (Znth idx out 0).
