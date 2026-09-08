Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Closed form of the value the C loop keeps in [pow2]: pow2[k] == 2^k mod m.
   Named here only so the C annotation can state the fact without inlining
   the exponentiation. *)
Definition Pow2Mod (k m : Z) : Z := (2 ^ k) mod m.

(* Lifts a fully-defined content list to the [option Z] cell list [free]'s
   contract expects, so a scratch buffer that was fully written can still be
   handed to the generic (possibly partially-defined) free contract. *)
Definition SomeList (l : list Z) : list (option Z) := map Some l.

Definition Zeros (k : Z) : list Z := repeat 0 (Z.to_nat k).

(* The per-(d, j) tail weight W[d][j] the C loop accumulates into `w`. *)
Definition Wfun (lQ : list Z) (d j m : Z) : Z :=
  let w0 := 1 mod m in
  let Lmax := d - (d + j + 2) / 2 in
  let w1 := if Z.geb Lmax 1 then (w0 + Pow2Mod Lmax m - 1 mod m + m) mod m else w0 in
  let D := d - j - 1 in
  if Z.geb D 0 then (w1 + Znth D lQ 0) mod m else w1.

(* Brow[j] for row i, i.e. A[j] * W[i-j][j] mod m. *)
Definition BrowEntry (lA lQ : list Z) (i j m : Z) : Z :=
  (Znth j lA 0 * Wfun lQ (i - j) j m) mod m.

(* `blocked` after columns 1..k of row i have been folded in. *)
Fixpoint BlockedNat (lA lQ : list Z) (i m : Z) (k : nat) : Z :=
  match k with
  | O => 0
  | S k' => (BlockedNat lA lQ i m k' + BrowEntry lA lQ i (Z.of_nat (S k')) m) mod m
  end.

Definition Blocked (lA lQ : list Z) (i m c : Z) : Z :=
  BlockedNat lA lQ i m (Z.to_nat c).

(* The value written to A[i] at the end of row i's first inner loop. *)
Definition ARowVal (lA lQ : list Z) (i m : Z) : Z :=
  ((Pow2Mod (i - 1) m - Blocked lA lQ i m (i - 1)) mod m + m) mod m.

(* The summand `c` of the prefix-sum loop at column q. *)
Definition RowC (lA lQ : list Z) (i m q : Z) : Z :=
  if Z.eqb q 0 then 0
  else if Z.ltb q i then BrowEntry lA lQ i q m
  else ARowVal lA lQ i m.

(* `run` after the first k columns (0..k-1) have been folded in. *)
Fixpoint RunNat (lA lQ : list Z) (i m : Z) (k : nat) : Z :=
  match k with
  | O => 0
  | S k' => (RunNat lA lQ i m k' + RowC lA lQ i m (Z.of_nat k')) mod m
  end.

Definition RunUpto (lA lQ : list Z) (i m c : Z) : Z :=
  RunNat lA lQ i m (Z.to_nat c).

(* P[q] = the running prefix sum through column q. *)
Definition PEntry (lA lQ : list Z) (i m q : Z) : Z :=
  RunUpto lA lQ i m (q + 1).

(* Q after the first k of row i's updates (t = 0..k-1) have been applied.
   Note the P values fold in the *incoming* lQ, matching the C: P was
   computed from Brow / A[i], which were computed from the incoming Q. *)
Fixpoint QAfterNat (lQ lA : list Z) (i m n : Z) (k : nat) : list Z :=
  match k with
  | O => lQ
  | S k' =>
      let l' := QAfterNat lQ lA i m n k' in
      let t := Z.of_nat k' in
      if Z.leb (i + t) (2 * n)
      then replace_Znth (i + t) ((Znth (i + t) l' 0 + PEntry lA lQ i m t) mod m) l'
      else l'
  end.

(* The (A, Q) pair after the first k outer rows. Coq has no structural
   recursion on Z, so the recursion is on nat with Z.of_nat / Z.to_nat at the
   boundary. *)
Fixpoint DPNat (m n : Z) (k : nat) : (list Z * list Z) :=
  match k with
  | O => (Zeros (n + 2), Zeros (2 * n + 4))
  | S k' =>
      let st := DPNat m n k' in
      let lA := fst st in
      let lQ := snd st in
      let i := Z.of_nat (S k') in
      (replace_Znth i (ARowVal lA lQ i m) lA,
       QAfterNat lQ lA i m n (Z.to_nat i))
  end.

Definition DPA (m n i : Z) : list Z := fst (DPNat m n (Z.to_nat i)).

Definition DPQ (m n i : Z) : list Z := snd (DPNat m n (Z.to_nat i)).

(* Row-local wrappers, so the C annotations can name row i's intermediate
   values without respelling the incoming (A, Q) state each time. *)
Definition RowBrow (m n i j : Z) : Z :=
  BrowEntry (DPA m n (i - 1)) (DPQ m n (i - 1)) i j m.

Definition RowBlocked (m n i c : Z) : Z :=
  Blocked (DPA m n (i - 1)) (DPQ m n (i - 1)) i m c.

Definition RowP (m n i q : Z) : Z :=
  PEntry (DPA m n (i - 1)) (DPQ m n (i - 1)) i m q.

Definition RowRun (m n i c : Z) : Z :=
  RunUpto (DPA m n (i - 1)) (DPQ m n (i - 1)) i m c.

Definition QPartial (m n i t : Z) : list Z :=
  QAfterNat (DPQ m n (i - 1)) (DPA m n (i - 1)) i m n (Z.to_nat t).

(* --- pow2 tail cell (annotation-r6) ---------------------------------------
   pow2 is allocated with n+2 cells but the program only ever writes indices
   0..n, so its last cell stays uninitialised. [free] accepts uninitialised
   cells through [mixed_full] / [option Z], so the cell list handed to it is
   the written prefix lifted by [SomeList] with a single [None] appended. *)
Definition SomeListUndefTail (l : list Z) : list (option Z) :=
  SomeList l ++ [None].
