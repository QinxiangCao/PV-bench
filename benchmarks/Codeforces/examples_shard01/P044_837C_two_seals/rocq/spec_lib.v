(* Codeforces 837/C - Two Seals: pick two of the n seals, each optionally rotated
   90 degrees, that fit without overlapping on the a x b paper, and maximise the
   area they cover. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* o is seal s in one of its two placements: as given, or rotated 90 degrees so
   its sides are swapped. *)
Definition Oriented (s o : Z * Z) : Prop := o = s \/ o = (snd s, fst s).

(* Two oriented rectangles x, y fit on the a x b paper without overlapping:
     x.w + y.w <= a  and  max(x.h, y.h) <= b     placed side by side, or
     max(x.w, y.w) <= a  and  x.h + y.h <= b     one above the other *)
Definition TwoFit (a b : Z) (x y : Z * Z) : Prop :=
  (fst x + fst y <= a /\ Z.max (snd x) (snd y) <= b) \/
  (Z.max (fst x) (fst y) <= a /\ snd x + snd y <= b).

(* v is an attainable covered area: either 0, when no pair is placed, or the sum
   of the areas of two distinct seals i < j, each in some orientation, that fit
   together on the paper. *)
Definition SealArea (paper : Z * Z) (seals : list (Z * Z)) (v : Z) : Prop :=
  (v = 0) \/ exists i j x y, 0 <= i < j /\ j < Zlength seals /\
    Oriented (Znth i seals (0, 0)) x /\ Oriented (Znth j seals (0, 0)) y /\
    TwoFit (fst paper) (snd paper) x y /\ v = fst x * snd x + fst y * snd y.
Definition Pre (paper : Z * Z) (seals : list (Z * Z)) : Prop :=
  (* The solver Require states these constraints explicitly:
       1 <= fst paper <= 100 /\ 1 <= snd paper <= 100 /\
       1 <= Zlength seals <= 100 /\
       Forall (fun s =>
         1 <= fst s <= 100 /\ 1 <= snd s <= 100) seals. *)
  True.

(* out = max { v : SealArea paper seals v }, which is 0 when no two seals fit. *)
Definition Spec (paper : Z * Z) (seals : list (Z * Z)) (out : Z) : Prop := max_value_of_subset Z.le (SealArea paper seals) (fun x => x) out.
