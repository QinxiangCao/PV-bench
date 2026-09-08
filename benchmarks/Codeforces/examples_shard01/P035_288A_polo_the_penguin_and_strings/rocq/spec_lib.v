(* Codeforces 288/A - Polo the Penguin and Strings: the lexicographically smallest
   length-n lowercase string with exactly k distinct letters and no two equal
   neighbours, or -1 when none exists. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import ListLib.General.Presuffix.

Import ListNotations.
Local Open Scope Z_scope.

(* a is lexicographically at most b: equal, or first differing at an index where
   a's character is smaller, or a strict prefix of b. *)
Definition LexLE (a b : list Z) : Prop :=
  a = b \/
  (exists i, 0 <= i < Z.min (Zlength a) (Zlength b) /\
    (forall j, 0 <= j < i -> Znth j a 0 = Znth j b 0) /\
    Znth i a 0 < Znth i b 0) \/
  (Zlength a < Zlength b /\ is_prefix a b).

(* s meets the statement's conditions 1 and 2:
     |s| = n, all lowercase letters
     #{ c : c occurs in s } = k        exactly k distinct letters
     s[i] <> s[i+1] for every i        no two equal neighbours *)
Definition PoloString (n k : Z) (s : list Z) : Prop :=
  Zlength s = n /\
  Forall (fun c => 97 <= c <= 122) s /\
  #(fun c : Z => 97 <= c < 123 /\ In c s) = k /\
  forall i, 0 <= i < n - 1 -> Znth i s 0 <> Znth (i + 1) s 0.

(* 1 <= n <= 10^6 and 1 <= k <= 26. *)
Definition Pre (n k : Z) : Prop :=
  (* Stated explicitly in the P035 solver Require (through its length and
     alphabet_size aliases), which therefore omits the Pre(...) call:
       1 <= n <= 1000000 /\ 1 <= k <= 26. *)
  True.

(* out = None      no such string exists, so -1 is printed
   out = Some s    s qualifies and s <= q lexicographically for every other
                   qualifying q, i.e. s is the smallest one *)
Definition Spec (n k : Z) (out : option (list Z)) : Prop :=
  (out = None /\ ~exists s, PoloString n k s) \/
  (exists s, out = Some s /\ PoloString n k s /\
    forall q, PoloString n k q -> LexLE s q).

(* C encoding: returning 0 means the -1 line is printed, 1 means a string is. *)
Definition P035ReturnBridge (out : option (list Z)) (ret : Z) : Prop :=
  (out = None /\ ret = 0) \/
  (exists xs, out = Some xs /\ ret = 1).
