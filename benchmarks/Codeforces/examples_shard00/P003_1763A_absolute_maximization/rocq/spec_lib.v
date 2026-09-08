Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import Coq.Relations.Relation_Operators.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition SameBitsExcept (x y b : Z) : Prop :=
  forall k, 0 <= k -> k <> b -> Z.testbit x k = Z.testbit y k.

Definition OneBitSwap (n : Z) (before after : list Z) : Prop :=
  exists i j b xi xj yi yj,
    0 <= i < n /\ 0 <= j < n /\ 0 <= b /\
    xi = Znth i before 0 /\ xj = Znth j before 0 /\
    yi = Znth i after 0 /\ yj = Znth j after 0 /\
    Zlength after = Zlength before /\
    (forall k, 0 <= k < n -> k <> i -> k <> j ->
       Znth k after 0 = Znth k before 0) /\
    SameBitsExcept xi yi b /\ SameBitsExcept xj yj b /\
    Z.testbit yi b = Z.testbit xj b /\
    Z.testbit yj b = Z.testbit xi b.

Definition ReachableByBitSwaps (n : Z) (a out : list Z) : Prop :=
  clos_refl_trans (OneBitSwap n) a out.

Definition ArraySpread (a : list Z) (d : Z) : Prop :=
  max_value_of_subset Z.le
    (fun endpoints : Z * Z => In (fst endpoints) a /\ In (snd endpoints) a)
    (fun endpoints => snd endpoints - fst endpoints) d.

Definition Pre (a : list Z) : Prop :=
  3 <= Zlength a <= 512 /\
  Forall (fun x => 0 <= x < 1024) a.

Definition Spec (a : list Z) (out : Z) : Prop :=
  max_value_of_subset Z.le
    (fun candidate : list Z * Z =>
      ReachableByBitSwaps (Zlength a) a (fst candidate) /\
      ArraySpread (fst candidate) (snd candidate))
    snd out.
