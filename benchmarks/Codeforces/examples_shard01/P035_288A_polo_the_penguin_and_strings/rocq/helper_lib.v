Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import ListLib.General.Presuffix.

Import ListNotations.
Local Open Scope Z_scope.

Definition AlternatingPrefix (m : Z) : list Z :=
  map (fun i => 97 + i mod 2) (Zrange 0 m).

Definition IncreasingTail (m : Z) : list Z :=
  map (fun i => 99 + i) (Zrange 0 m).

Definition PoloCandidate (n k : Z) : list Z :=
  if Z.eq_dec k 1 then [97]
  else AlternatingPrefix (n - (k - 2)) ++ IncreasingTail (k - 2).
