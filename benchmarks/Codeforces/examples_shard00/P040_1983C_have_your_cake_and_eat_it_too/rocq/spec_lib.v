Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition DisjointIntervals (l1 r1 l2 r2 : Z) : Prop := r1 < l2 \/ r2 < l1.

Definition ValidCakeDivision (a b c bounds : list Z) : Prop :=
  exists la ra lb rb lc rc total,
    bounds = la :: ra :: lb :: rb :: lc :: rc :: nil /\
    total = fold_right Z.add 0 a /\
    0 <= la <= ra /\ ra < Zlength a /\
    0 <= lb <= rb /\ rb < Zlength b /\
    0 <= lc <= rc /\ rc < Zlength c /\
    DisjointIntervals la ra lb rb /\ DisjointIntervals la ra lc rc /\
    DisjointIntervals lb rb lc rc /\
    3 * fold_right Z.add 0 (sublist la (ra + 1) a) >= total /\
    3 * fold_right Z.add 0 (sublist lb (rb + 1) b) >= total /\
    3 * fold_right Z.add 0 (sublist lc (rc + 1) c) >= total.

Definition Pre (a b c : list Z) : Prop :=
  3 <= Zlength a <= 200000 /\ Zlength b = Zlength a /\ Zlength c = Zlength a /\
  Forall (fun x => 1 <= x <= 1000000) a /\ Forall (fun x => 1 <= x <= 1000000) b /\
  Forall (fun x => 1 <= x <= 1000000) c /\
  fold_right Z.add 0 a = fold_right Z.add 0 b /\
  fold_right Z.add 0 a = fold_right Z.add 0 c.

Definition Spec (a b c : list Z) (out : option (list Z)) : Prop :=
  (exists bounds, out = Some bounds /\ ValidCakeDivision a b c bounds) \/
  (out = None /\ forall bounds, ~ ValidCakeDivision a b c bounds).

Import ListNotations.
