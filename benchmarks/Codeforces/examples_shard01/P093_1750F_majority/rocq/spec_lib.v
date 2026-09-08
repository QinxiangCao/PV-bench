(* Codeforces 1750/F - Majority: an electricity spread turns on a whole range
   whose online servers are at least half of it; count the length-n strings that
   can be brought fully online, modulo m. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* One spread: pick i < j with a[i] = a[j] = 1 and
     2 * (a[i] + ... + a[j]) >= j - i + 1        enough power in the range
   then set a[k] = 1 for every i <= k <= j, leaving the rest unchanged. *)
Definition SpreadStep (a b : list Z) : Prop :=
  exists i j, 0 <= i < j /\ j < Zlength a /\ Znth i a 0 = 1 /\ Znth j a 0 = 1 /\
   2 * (fold_right Z.add 0) (sublist i (j + 1) a) >= j - i + 1 /\ Zlength b = Zlength a /\
   (forall q, 0 <= q < Zlength a -> Znth q b 0 = if (Z.leb i q && Z.leb q j)%bool then 1 else Znth q a 0).

(* s is rated: some chain of spreads, possibly empty, turns s into all ones. *)
Definition Rated (s : list Z) : Prop :=
  exists st : list (list Z), st <> [] /\ Znth 0 st [] = s /\ Forall (fun x => x = 1) (Znth (Zlength st - 1) st []) /\
  forall i, 0 <= i < Zlength st - 1 -> SpreadStep (Znth i st []) (Znth (i + 1) st []).

(* ss lists every binary string of length n exactly once -- the 2^n candidates. *)
Definition AllBinary (n : Z) (ss : list (list Z)) : Prop :=
  NoDup ss /\ forall s, In s ss <-> Zlength s = n /\ Forall (fun x => x = 0 \/ x = 1) s.
Definition Pre (n m : Z) : Prop :=
  (* Stated explicitly in the P093 solver Require, which therefore omits the
     Pre(...) call: 1 <= n <= 5000 /\ 10 <= m <= 1000000000. *)
  True.

(* out = #{ rated binary strings of length n } mod m. *)
Definition Spec (n m out : Z) : Prop :=
  exists ss, AllBinary n ss /\ out = (#(fun i : Z => 0 <= i < Zlength ss /\ Rated (Znth i ss []))) mod m.
