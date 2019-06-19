Require Import Monads ProofMonads List ZArith Program.

Open Scope monad_scope.

Import ListNotations.

Set Implicit Arguments.

Module M := Monads.
Module PM := ProofMonads.

Section Test.

Definition init_val1 := 0.

Definition init_S1 : nat := init_val1.

Print modify.

Definition add_s (i : nat) : M.State nat unit :=
  M.modify (fun s => s + i).

Definition minus_s (i : nat) : M.State nat unit :=
  M.modify (fun s => s - i).

Definition get10 : State nat nat:= return_ 10.

Compute runState (
  for i = 5 to 0 {{
    add_s 1
  }}) init_S1.

Compute runState (
  for2 i = 5 to 0 {{
    add_s 1
  }}) init_S1.

Compute runState (
  for i = 5 to 0 {{
    add_s i
  }}) init_S1.
(* 4 + 3 + 2 + 1 + 0 = 10 *)

Compute runState (
  for2 i = 5 to 0 {{
    add_s i
  }}) init_S1.

Compute runState (
  for i = 5 to 0 {{
    add_s i
  }} ;;
  for j = 5 to 0
  {{
    add_s j
  }} ) init_S1.

Compute runState (
  for2 i = 5 to 0 {{
    add_s i
  }} ;;
  for2 j = 5 to 0
  {{
    add_s j
  }} ) init_S1.

Compute runState (
  for i = 5 to 0 {{
    add_s i
  }} ;;
  perf x <- get10 ;
  add_s x ;;
  for j = 5 to 0
  {{
    add_s j
  }} ) init_S1.

Compute runState (
  for2 i = 5 to 0 {{
    add_s i
  }} ;;
  perf x <- get10 ;
  add_s x ;;
  for2 j = 5 to 0
  {{
    add_s j
  }} ) init_S1.

Compute runState (
   for_e i = 20 to 0 {{
    if (i =? 15) then exit
    else (loopT_liftT (add_s i))
  }} ) init_S1.
(* 19 + 18 + 17 + 16 = 70 *)

Open Scope list_scope.

Definition init_S2 : list nat := [].

Definition addElement (val : nat) : State (list nat) unit :=
  M.modify (fun s => val :: s).

Compute runState (
  for i = 5 to 0 {{
    for j = 3 to 0 {{
      addElement (i + j)
    }}
  }}) init_S2.

Compute runState (
  for2 i = 5 to 0 {{
    for2 j = 3 to 0 {{
      addElement (i + j)
    }}
  }}) init_S2.

Open Scope Z_scope.

(* if/else *)

Definition add_z (i : nat) : M.State Z unit :=
  M.modify (fun s => s + Z.of_nat i).

Definition minus_z (i : nat) : M.State Z unit :=
  M.modify (fun s => s - Z.of_nat i).

Definition init_Z1 : Z := 0.

Compute runState (
  for i = 6 to 0 {{
    if (Z.eqb (Z.modulo (Z.of_nat i) 2) 0) then
      add_z i
    else
      minus_z i
  }}
  ) init_Z1.

End Test.
