Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition pow_mod (b e : Z) : Z := (b ^ e) mod 998244353.

(* Closed form, modulo 998244353, of
     W(P) = sum over all sub-multisets A of P of (|A| - 1) * (sum A)^2
   expressed through k = |P|, S = sum P and S2 = sum of squares of P.
   Only k has to be exact; S and S2 may already be reduced modulo p.
   At k = 2 the cross coefficient degenerates to 2^(k-2): the extra term
   carries the factor (k - 2) = 0, and Z.pow with a negative exponent is 0,
   which is why the C code may guard that term with k >= 3. *)

Definition pool_closed_form (k S S2 : Z) : Z :=
  if k <? 2 then 0
  else (S2 * 2 ^ (k - 2) * (k - 1)
        + (S * S - S2) * (2 ^ (k - 2) + (k - 2) * 2 ^ (k - 3))) mod 998244353.

(* ------------------------------------------------------------------ *)
(* Internal state of the sieve: canonical multiset, sub-multiset       *)
(* weights, exact-gcd weights and the running loop aggregates.         *)
(* ------------------------------------------------------------------ *)

(* The canonical expansion of the input: each value repeated as often as
   its frequency says.  It satisfies ExpandedMultiset, and any other
   witness of ExpandedMultiset is a permutation of it. *)

Fixpoint expand (vals freq : list Z) : list Z :=
  match vals, freq with
  | v :: vs, f :: fs => repeat v (Z.to_nat f) ++ expand vs fs
  | _, _ => nil
  end.

(* Every sub-multiset of a list, keeping multiplicity. *)

Fixpoint sub_multisets (l : list Z) : list (list Z) :=
  match l with
  | nil => nil :: nil
  | x :: t => map (cons x) (sub_multisets t) ++ sub_multisets t
  end.

(* The contribution of one selected sub-multiset A: pairing A with each of
   the |A| ways of dropping one element collapses to (|A| - 1) * (sum A)^2. *)

Definition subset_weight (A : list Z) : Z :=
  (Zlength A - 1) * (fold_right Z.add 0 A) ^ 2.

(* W(P): the total weight of every sub-multiset of a pool P. *)

Definition subset_weight_sum (P : list Z) : Z :=
  fold_right Z.add 0 (map subset_weight (sub_multisets P)).

Definition divisible_pool (s : list Z) (d : Z) : list Z :=
  filter (fun x => Z.eqb (x mod d) 0) s.

(* G(d): the weight of the pool of input elements divisible by d. *)

Definition pool_weight (vals freq : list Z) (d : Z) : Z :=
  subset_weight_sum (divisible_pool (expand vals freq) d).

(* F(d): the weight of the sub-multisets whose gcd is exactly d.  The empty
   sub-multiset has gcd 0, so it is excluded for every d >= 1. *)

Definition exact_gcd_weight (vals freq : list Z) (d : Z) : Z :=
  fold_right Z.add 0
    (map subset_weight
       (filter (fun A => Z.eqb (fold_right Z.gcd 0 A) d)
               (sub_multisets (expand vals freq)))).

(* The table entries at the first u multiples of d. *)

Definition multiple_prefix_sum (l : list Z) (d u : Z) : Z :=
  sum_range 1 u (fun i => Znth (i * d) l 0).

Definition PowmodState (b0 e0 b e r : Z) : Prop :=
  pow_mod b0 e0 = (r * pow_mod b e) mod 998244353.

Definition AnsExactPrefix (vals freq : list Z) (maxv : Z)
                          (anslist : list Z) (d : Z) : Prop :=
  forall w, d < w <= maxv ->
    Znth w anslist 0 = (exact_gcd_weight vals freq w) mod 998244353.

Definition PoolAggregate (cnts sums squares : list Z)
                         (d u k S S2 : Z) : Prop :=
  k = multiple_prefix_sum cnts d u /\
  S = (multiple_prefix_sum sums d u) mod 998244353 /\
  S2 = (multiple_prefix_sum squares d u) mod 998244353.

Definition PeelState (vals freq : list Z) (d u cur : Z) : Prop :=
  cur = (pool_weight vals freq d
         - sum_range 2 u (fun i => exact_gcd_weight vals freq (i * d)))
        mod 998244353.
