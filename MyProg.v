Require Import Monads List.

Open Scope monad_scope.

Import ListNotations.

Set Implicit Arguments.

Section Test.

Definition nth1 := 5.

Definition init_val1 := 0.

Definition init_S1 : nat := init_val1.

Definition add_s (i : nat) : Monads.State nat unit :=
  Monads.modify (fun s => s + i).

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

End Test.
