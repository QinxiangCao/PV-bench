(* Codeforces 817/A - Treasure Hunt: each potion move shifts the position by x in
   the first coordinate and y in the second, either sign; decide whether the
   treasure at (x2, y2) is reachable from (x1, y1). *)

Require Import Coq.ZArith.ZArith.

Local Open Scope Z_scope.

Definition Pre (x1 y1 x2 y2 x y : Z) : Prop :=
  (* -100000 <= x1 <= 100000 /\
     -100000 <= y1 <= 100000 /\
     -100000 <= x2 <= 100000 /\
     -100000 <= y2 <= 100000 /\
     1 <= x <= 100000 /\
     1 <= y <= 100000. *)
  True.

(* Absolute difference |a - b|. *)
Definition AbsDiff (a b : Z) : Z :=
  if a <? b then b - a else a - b.

(* The treasure is reachable exactly when
     x | |x1 - x2|
     y | |y1 - y2|
     |x1 - x2| / x  and  |y1 - y2| / y  have the same parity
   since every move changes both coordinates at once, the two axes take the same
   number of steps. *)
Definition Reachable (x1 y1 x2 y2 x y : Z) : Prop :=
  Z.rem (AbsDiff x1 x2) x = 0 /\
  Z.rem (AbsDiff y1 y2) y = 0 /\
  Z.rem (Z.quot (AbsDiff x1 x2) x) 2 =
  Z.rem (Z.quot (AbsDiff y1 y2) y) 2.

(* out = 1 for YES, 0 for NO. *)
Definition Spec (x1 y1 x2 y2 x y out : Z) : Prop :=
  ((Reachable x1 y1 x2 y2 x y /\ out = 1) \/
   (~Reachable x1 y1 x2 y2 x y /\ out = 0)).
