Require Import Monads List ZArith.

Open Scope monad_scope.

Import ListNotations.

Set Implicit Arguments.

Section Test.

Definition nth1 := 5.

Definition init_val1 := 0.

Definition init_S1 : nat := init_val1.

Definition add_s (i : nat) : Monads.State nat unit :=
  Monads.modify (fun s => s + i).

Definition minus_s (i : nat) : Monads.State nat unit :=
  Monads.modify (fun s => s - i).

Goal runState (for i = 0 to nth1 {{ add_s i }} ) init_S1 = (tt, 10).
Proof.
  unfold runState.
  Admitted.

Compute runState (
  for i = 0 to 5 {{
    add_s i 
  }} ;; 
  for j = 0 to 5 
  {{ 
    add_s j 
  }} ) init_S1.

Definition getVal : State nat nat:= return_ 10.

Compute runState (
  for i = 0 to 5 {{
    add_s i 
  }} ;; 
  perf x <- getVal ;
  add_s x ;;
  for j = 0 to 5 
  {{ 
    add_s j 
  }} ) init_S1.

Open Scope list_scope.

Definition nth2 := 4.

Definition init_S2 : list nat := [].

Definition addElement (val : nat) : State (list nat) unit :=
  modify (fun s => val :: s).

Compute runState (for i = 0 to nth2 {{ for j = 0 to nth2 {{addElement (i+j) }} }} ) init_S2.

(* if/else *)

Compute (Nat.eqb (Nat.modulo 9 2) 0).

Open Scope Z_scope.

Definition add_z (i : nat) : Monads.State Z unit :=
  Monads.modify (fun s => s + Z.of_nat i).

Definition minus_z (i : nat) : Monads.State Z unit :=
  Monads.modify (fun s => s - Z.of_nat i).

Definition init_Z1 : Z := 0.

Compute runState (
  for i = 0 to 6 {{
    if (Z.eqb (Z.modulo (Z.of_nat i) 2) 0) then
      add_z i 
    else 
      minus_z i
  }}
  ) init_Z1.

End Test.
