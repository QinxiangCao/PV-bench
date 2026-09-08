Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic ArrayLib.
Require Import Logic.LogicGenerator.demo932.Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Import naive_C_Rules.
Local Open Scope sac.

(**
  [sll] is the abstract, singly-linked-list-shaped sequence used to describe
  stack contents.  It is deliberately independent of the concrete memory
  representation: this case stores the sequence in a contiguous C array.
  The head of an [sll] is the logical top of the stack.
 *)
Definition sll : Type := list Z.

Definition sll_empty : sll := [].

Definition sll_cons (x : Z) (contents : sll) : sll :=
  x :: contents.

Definition sll_from_array (concrete : list Z) : sll :=
  rev concrete.

Definition stack_capacity : Z := 100000.

(**
  Physical array index 0 is the bottom of the stack, so the concrete array is
  the reverse of the abstract [sll].  Keeping the size in the relation makes
  every public stack state carry the capacity and exact-length invariants.
 *)
Definition stack_representation
    (contents : sll) (concrete : list Z) (size : Z) : Prop :=
  0 <= size /\
  size <= stack_capacity /\
  Zlength contents = size /\
  Zlength concrete = size /\
  concrete = rev contents.

Definition store_stack
    (p : Z) (contents : sll) (size : Z) : Assertion :=
  EX concrete : list Z,
    “ stack_representation contents concrete size ” &&
    IntArray.full p size concrete.

(**
  Mathematical state shared by the incremental [build] annotations.  The C
  invariant owns the loop bounds and the array resources; this predicate owns
  only the abstract meaning of the already processed input prefix.
 *)
Definition BuildStackPrefix
    (contents : sll) (input : list Z) (processed : Z) : Prop :=
  contents = sll_from_array (sublist 0 processed input).

(**
  Body-facing view of the frozen public representation relation.  Keeping a
  separate internal root preserves the frozen [store_stack] dependency
  surface while allowing QCP assertions to open its concrete array facts.
 *)
Definition StackConcreteView
    (contents : sll) (concrete : list Z) (size : Z) : Prop :=
  stack_representation contents concrete size.

