
Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition PrefixChangedByFlips
    (commands modified : list Z) (prefix_len flips : Z) : Prop :=
  0 <= prefix_len <= Zlength commands /\
  Zlength modified = prefix_len /\
  exists marks,
    Zlength marks = prefix_len /\
    Forall (fun x => x = 0 \/ x = 1) marks /\
    fold_right Z.add 0 marks = flips /\
    forall j, 0 <= j < prefix_len ->
      (Znth j marks 0 = 0 ->
         Znth j modified 0 = Znth j commands 0) /\
      (Znth j marks 0 = 1 ->
         ((Znth j commands 0 = 70 /\ Znth j modified 0 = 84) \/
          (Znth j commands 0 = 84 /\ Znth j modified 0 = 70))).

Definition TurtleState (commands : list Z) (position direction : Z) : Prop :=
  exists states,
    Zlength states = Zlength commands + 1 /\
    Znth 0 states (0, 1) = (0, 1) /\
    (forall i, 0 <= i < Zlength commands ->
      let '(p, d) := Znth i states (0, 1) in
      Znth (i + 1) states (0, 1) =
        if Z.eqb (Znth i commands 0) 84
        then (p, -d)
        else (p + d, d)) /\
    Znth (Zlength commands) states (0, 1) = (position, direction).

Definition PrefixReachable
    (commands : list Z) (prefix_len flips direction slot : Z) : Prop :=
  exists modified position final_direction,
    PrefixChangedByFlips commands modified prefix_len flips /\
    TurtleState modified position final_direction /\
    position = slot - Zlength commands /\
    ((direction = 0 /\ final_direction = 1) \/
     (direction = 1 /\ final_direction = -1)).

Definition TurtleWidth (commands : list Z) : Z :=
  2 * Zlength commands + 1.

Definition TurtleCellIndex
    (commands : list Z) (flips direction slot : Z) : Z :=
  (flips * 2 + direction) * TurtleWidth commands + slot.

Definition TurtleLayerMeaning
    (commands : list Z) (prefix_len change_limit : Z)
    (table : list Z) : Prop :=
  forall flips direction slot,
    0 <= flips <= change_limit ->
    0 <= direction < 2 ->
    0 <= slot < TurtleWidth commands ->
    let value := Znth (TurtleCellIndex commands flips direction slot) table 0 in
    (value = 0 \/ value = 1) /\
    (value = 1 <->
       PrefixReachable commands prefix_len flips direction slot).

Definition FlippedCommand (command flip effective : Z) : Prop :=
  (flip = 0 /\ effective = command) \/
  (flip = 1 /\
    ((command = 70 /\ effective = 84) \/
     (command = 84 /\ effective = 70))).

Definition TurtleEncodedStep
    (direction slot command next_direction next_slot : Z) : Prop :=
  (command = 84 /\ next_direction = 1 - direction /\ next_slot = slot) \/
  (command = 70 /\ next_direction = direction /\
    ((direction = 0 /\ next_slot = slot + 1) \/
     (direction = 1 /\ next_slot = slot - 1))).

Definition TurtleTransitionRank
    (commands : list Z) (flips direction slot flip : Z) : Z :=
  2 * TurtleCellIndex commands flips direction slot + flip.

Definition TurtleNextReachable
    (commands : list Z) (prefix_len change_limit done : Z)
    (next_flips next_direction next_slot : Z) : Prop :=
  exists flips direction slot flip effective,
    0 <= flips <= change_limit /\
    0 <= direction < 2 /\
    0 <= slot < TurtleWidth commands /\
    0 <= flip < 2 /\
    TurtleTransitionRank commands flips direction slot flip < done /\
    PrefixReachable commands prefix_len flips direction slot /\
    next_flips = flips + flip /\
    next_flips <= change_limit /\
    FlippedCommand (Znth prefix_len commands 0) flip effective /\
    TurtleEncodedStep direction slot effective next_direction next_slot.

Definition TurtleNextPrefix
    (commands : list Z) (prefix_len change_limit done : Z)
    (next_table : list Z) : Prop :=
  forall flips direction slot,
    0 <= flips <= change_limit ->
    0 <= direction < 2 ->
    0 <= slot < TurtleWidth commands ->
    let value := Znth (TurtleCellIndex commands flips direction slot) next_table 0 in
    (value = 0 \/ value = 1) /\
    (value = 1 <->
       TurtleNextReachable commands prefix_len change_limit done
         flips direction slot).

Definition TurtleTerminalEligible
    (commands : list Z) (change_limit flips direction slot : Z) : Prop :=
  0 <= flips <= change_limit /\
  0 <= direction < 2 /\
  0 <= slot < TurtleWidth commands /\
  Z.even (change_limit - flips) = true /\
  PrefixReachable commands (Zlength commands) flips direction slot.

Definition TurtleAnswerPrefix
    (commands : list Z) (change_limit done answer : Z) : Prop :=
  0 <= answer /\
  (forall flips direction slot,
    TurtleTerminalEligible commands change_limit flips direction slot ->
    TurtleCellIndex commands flips direction slot < done ->
    Z.abs (slot - Zlength commands) <= answer) /\
  (answer = 0 \/
   exists flips direction slot,
     TurtleTerminalEligible commands change_limit flips direction slot /\
     TurtleCellIndex commands flips direction slot < done /\
     answer = Z.abs (slot - Zlength commands)).
