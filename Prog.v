Require Import Monads List ZArith Program.

Open Scope monad_scope.

Import ListNotations.

Set Implicit Arguments.

Section Test.

Definition init_val1 := 0.

Definition init_S1 : nat := init_val1.

Print modify.

Definition add_s (i : nat) : Monads.State nat unit :=
  Monads.modify (fun s => s + i).

Definition minus_s (i : nat) : Monads.State nat unit :=
  Monads.modify (fun s => s - i).

Definition get10 : State nat nat:= return_ 10.

Definition count15 : State nat unit :=
 add_s 1;;
 add_s 2;;
 add_s 3;;
 add_s 4;;
 add_s 5;;
 return_ tt.

Notation "{{ P }} m {{ Q }}" := (hoareTripleS P m Q)
  (at level 90, format "'[' '[' {{  P  }}  ']' '/  ' '[' m ']' '['  {{  Q  }} ']' ']'") : monad_scope.

Lemma l_add_s :
 forall (n i : nat), {{fun (s : nat) => s = n}} add_s i {{fun (_ : unit) (s : nat) => s = n + i}}.
  Proof.
  intros n i s H.
  unfold add_s.
  apply l_modify.
  auto.
  Qed.

Lemma l_count15 : {{fun s : nat => s = init_S1}} count15 {{fun (_ : unit ) (s : nat) => s = 15}}.
  Proof.
  apply bindRev with (Q := (fun (_ : unit ) (s : nat) => s = 1)); try apply l_add_s.
  + intros; apply bindRev with (Q := (fun (_ : unit ) (s : nat) => s = 3)) ; try apply l_add_s.
  - intros; apply bindRev with (Q := (fun (_ : unit ) (s : nat) => s = 6)) ; try apply l_add_s.
  * intros; apply bindRev with (Q := (fun (_ : unit ) (s : nat) => s = 10)) ; try apply l_add_s.
    intros; apply bindRev with (Q := (fun (_ : unit ) (s : nat) => s = 15)) ; try apply l_add_s.
    intros. intros S H. trivial.
  Qed.

Definition count42 : State nat unit
 := for i = 0 to 3 {{ 
    add_s i ;;
    add_s i ;;
    perf x <- get10;
    add_s x ;;
    add_s i ;;
    add_s i
  }} .

Lemma l_count42 : hoareTripleS (fun s : nat => s = init_S1) count42 (fun (_ : unit ) (s : nat) => s = 42).
  Proof.
  eapply bindRev.
  unfold count42.
  unfold loopT_liftT.
  eapply bindRev.
  Qed.

Check count42.

Compute runState (
  count42
  ) init_S1.

Compute runState (
  for i = 0 to 5 {{
    add_s i 
  }} ;; 
  for j = 0 to 5 
  {{ 
    add_s j 
  }} ) init_S1.

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

(* exit *)

Compute runState (
  fore i = 0 to 20 {{
    if (i =? 5) then exit
    else (loopT_liftT (add_s i))
  }}
  ) init_S1.

Open Scope Z_scope.

(* if/else *)

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
