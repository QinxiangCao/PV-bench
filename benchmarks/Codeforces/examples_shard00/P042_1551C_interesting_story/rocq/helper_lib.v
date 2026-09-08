
Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Require Import Coq.Sorting.Permutation.

From AUXLib Require ListLib.

(** The score used by the implementation for one word and one letter. *)
Definition LetterCount (letter : Z) (word : list Z) : Z :=
  Zlength (filter (Z.eqb letter) word).

Definition WordScore (letter : Z) (word : list Z) : Z :=
  2 * LetterCount letter word - Zlength word.

Definition ScoreBlock (words : list (list Z)) (letter : Z) : list Z :=
  map (WordScore letter) words.

Definition CountPrefixState
    (word : list Z) (scanned : Z) (counts : list Z) : Prop :=
  Zlength counts = 5 /\ 0 <= scanned <= Zlength word /\
  forall d, 0 <= d < 5 ->
    Znth d counts 0 = LetterCount (97 + d) (sublist 0 scanned word).

(** Memory contents while complete rows of the five score blocks are built. *)
Definition ScoreBuildState
    (words : list (list Z)) (done : Z) (mem : list (option Z)) : Prop :=
  Zlength mem = 5 * Zlength words /\
  forall d k,
    0 <= d < 5 -> 0 <= k < Zlength words ->
    (k < done ->
       Znth (d * Zlength words + k) mem None =
       Some (WordScore (97 + d) (Znth k words nil))) /\
    (done <= k ->
       Znth (d * Zlength words + k) mem None = None).

(** The inner five-iteration loop has filled the first [letters] cells of row
    [row], in addition to every earlier row. *)
Definition ScoreRowState
    (words : list (list Z)) (row letters : Z)
    (mem : list (option Z)) : Prop :=
  Zlength mem = 5 * Zlength words /\
  forall d k,
    0 <= d < 5 -> 0 <= k < Zlength words ->
    (k < row ->
       Znth (d * Zlength words + k) mem None =
       Some (WordScore (97 + d) (Znth k words nil))) /\
    (k = row /\ d < letters ->
       Znth (d * Zlength words + k) mem None =
       Some (WordScore (97 + d) (Znth k words nil))) /\
    (row < k \/ (k = row /\ letters <= d) ->
       Znth (d * Zlength words + k) mem None = None).

Definition ScoreTable (words : list (list Z)) (scores : list Z) : Prop :=
  Zlength scores = 5 * Zlength words /\
  forall d,
    0 <= d < 5 ->
    sublist (d * Zlength words) ((d + 1) * Zlength words) scores =
    ScoreBlock words (97 + d).

(** Blocks before [processed] have been sorted decreasingly; later blocks are
    still in their canonical word order. *)
Definition PreparedScoreTable
    (words : list (list Z)) (processed : Z) (scores : list Z) : Prop :=
  Zlength scores = 5 * Zlength words /\
  forall d,
    0 <= d < 5 ->
    let block := sublist (d * Zlength words)
                         ((d + 1) * Zlength words) scores in
    (d < processed ->
       Permutation (ScoreBlock words (97 + d)) block /\
       ListLib.decreasing block) /\
    (processed <= d -> block = ScoreBlock words (97 + d)).

Definition PositivePrefixState
    (block : list Z) (take acc : Z) : Prop :=
  0 <= take <= Zlength block /\
  acc = fold_right Z.add 0 (sublist 0 take block) /\
  forall k, 0 <= k < take ->
    0 < fold_right Z.add 0 (sublist 0 (k + 1) block).

Definition InterestingForLetter
    (words : list (list Z)) (letter : Z) (chosen : Z -> Prop) : Prop :=
  (forall i, chosen i -> 0 <= i < Zlength words) /\
  2 * sum (fun i : Z => 0 <= i < Zlength words /\ chosen i) (fun i =>
    LetterCount letter (Znth i words nil)) >
  sum (fun i : Z => 0 <= i < Zlength words /\ chosen i)
      (fun i => Zlength (Znth i words nil)).

Definition LetterBest
    (words : list (list Z)) (letter best : Z) : Prop :=
  (best = 0 /\ forall chosen, ~ InterestingForLetter words letter chosen) \/
  max_value_of_subset Z.le
    (fun candidate : (Z -> Prop) * Z =>
      InterestingForLetter words letter (fst candidate) /\
      snd candidate = #(fun i : Z =>
        0 <= i < Zlength words /\ fst candidate i))
    snd best.

(** [answer] is the maximum optimum among letters already processed. *)
Definition AnswerState
    (words : list (list Z)) (processed answer : Z) : Prop :=
  0 <= processed <= 5 /\ 0 <= answer <= Zlength words /\
  (forall d, 0 <= d < processed ->
     exists best,
       LetterBest words (97 + d) best /\ best <= answer) /\
  (answer = 0 \/
   exists d, 0 <= d < processed /\ LetterBest words (97 + d) answer).
