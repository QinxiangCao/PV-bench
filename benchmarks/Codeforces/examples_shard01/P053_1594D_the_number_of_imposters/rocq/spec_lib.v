(* Codeforces 1594/D - The Number of Imposters: imposters always lie and crewmates
   always tell the truth; find the largest number of imposters consistent with the
   comments, or -1 if they contradict each other. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* roles assigns 0 = crewmate or 1 = imposter to every player and satisfies each
   comment (i, j, c):
     roles[i-1] = 0  ->  roles[j-1] = c        a crewmate tells the truth
     roles[i-1] = 1  ->  roles[j-1] <> c       an imposter lies *)
Definition RolesConsistent (n : Z) (comments : list (Z * Z * Z)) (roles : list Z) : Prop :=
  Zlength roles = n /\ Forall (fun r => r = 0 \/ r = 1) roles /\
  forall q, In q comments ->
    let ' (i, j, c) := q in
    (Znth (i - 1) roles 0 = 0 /\ Znth (j - 1) roles 0 = c) \/
    (Znth (i - 1) roles 0 = 1 /\ Znth (j - 1) roles 0 <> c).
Definition Pre (n : Z) (comments : list (Z * Z * Z)) : Prop :=
  (* Stated explicitly in the P053 solver Require, so dropped here:
       Zlength comments <= 500000 /\
       Forall (fun q => let ' (i, j, c) := q in 1 <= i <= n /\ 1 <= j <= n /\ i <> j /\ (c = 0 \/ c = 1)) comments /\
       1 <= n <= 200000   *)
  True.

(* How many of the crewmates are imposters: the roles marked with one. *)
Definition ImposterCount (roles : list Z) : Z := fold_right Z.add 0 roles.

(* out = -1        no consistent assignment exists
   out = max { number of imposters : RolesConsistent }   otherwise *)
Definition Spec (n : Z) (comments : list (Z * Z * Z)) (out : Z) : Prop :=
  (out = (- 1) /\ ~exists r, RolesConsistent n comments r) \/
  (out >= 0 /\ max_value_of_subset Z.le
    (fun v => exists r, RolesConsistent n comments r /\ v = ImposterCount r)
    (fun x => x) out).
