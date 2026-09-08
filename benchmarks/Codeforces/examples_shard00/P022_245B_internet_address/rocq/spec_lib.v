Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Import ListNotations.

Local Open Scope Z_scope.

Definition LowercaseNonempty (s : list Z) : Prop :=
  0 < Zlength s /\ Forall (fun c => 97 <= c <= 122) s.

Definition RestoredInternetAddress (plain address : list Z) : Prop :=
  exists protocol domain context,
    (protocol = [104; 116; 116; 112] \/ protocol = [102; 116; 112]) /\
    LowercaseNonempty domain /\
    (context = [] \/ LowercaseNonempty context) /\
    plain = protocol ++ domain ++ [114; 117] ++ context /\
    address = protocol ++ [58; 47; 47] ++ domain ++ [46; 114; 117] ++
              (match context with [] => [] | _ => [47] ++ context end).

Definition Pre (plain : list Z) : Prop :=
  1 <= Zlength plain <= 50 /\
  Forall (fun c => 97 <= c <= 122) plain /\
  exists address, RestoredInternetAddress plain address.

Definition Spec (plain address : list Z) : Prop :=
  RestoredInternetAddress plain address.
