Require Import PVbench.Codeforces.examples_shard00.P044_545C_woodcutters.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

(** The number of felled trees represented by a list of choices. *)
Definition FellingCount (choices : list Z) : Z :=
  Zlength (filter (fun choice => negb (Z.eqb choice 0)) choices).

(** A prefix choice is admissible when it is internally non-overlapping and
    leaves enough room for the next, still unprocessed tree to stand.  The
    endpoint is the right edge occupied by the last tree in the prefix. *)
Definition PrefixFellingAdmissible
    (trees : list (Z * Z)) (processed : Z)
    (choices : list Z) (endpoint : Z) : Prop :=
  1 <= processed < Zlength trees /\
  ValidFelling (sublist 0 processed trees) choices /\
  (exists left,
    TreeOccupation (Znth (processed - 1) trees (0, 0))
      (Znth (processed - 1) choices 0) left endpoint) /\
  endpoint < fst (Znth processed trees (0, 0)).

(** Mathematical state of the left-to-right greedy scan.  [answer] includes
    the final tree, which is reserved throughout the scan.  The selected
    prefix maximizes the number of felled trees among admissible prefixes;
    among equally good prefixes its occupied endpoint is minimal. *)
Definition PrefixFellingState
    (trees : list (Z * Z))
    (processed occupied answer : Z) : Prop :=
  exists choices,
    PrefixFellingAdmissible trees processed choices occupied /\
    answer = 1 + FellingCount choices /\
    forall competitor competitor_endpoint,
      PrefixFellingAdmissible
        trees processed competitor competitor_endpoint ->
      FellingCount competitor <= FellingCount choices /\
      (FellingCount competitor = FellingCount choices ->
       occupied <= competitor_endpoint).
