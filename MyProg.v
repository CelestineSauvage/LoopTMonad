Require Import Monads.

Open Scope monad_scope.

Section Test1.

Definition nth := 5.

Definition init_val := 0.

Definition init_S : nat := init_val.

Definition add_s (i : nat) : Monads.State nat unit :=
  Monads.modify (fun s => s + i).

Compute Monads.runState (foreach i = 0 to nth {{ add_s i }} ) init_S.

End Test1.

(* Open Scope list_scope.

Notation "'foreach' i '=' min 'to' max '{{' body }}" := (foreach' min max (fun i => (liftT body))) (at level 60, i ident, min at level 60, 
max at level 60, body at level 60, right associativity).

Definition nth := 4.

Definition init_S := {| my_list := [] |}.

Definition addElement (val : nat) : State unit :=
  modify (fun s => {| my_list := val :: s.(my_list)|}).

Compute runState (foreach i = 0 to nth {{ foreach j = 0 to nth {{addElement (i+j) }} }} ) init_S.

 *)
(* End Monad. *)
(* Definition init_val := 0.

Definition init_S := {| myval := init_val|}.

Definition changeState (i : nat) : State unit :=
  modify (fun s => {| myval := s.(myval) + i |}).

Check runState (foreach' 0 5 (fun i => (liftT (changeState i)))) init_S.

(* Voir pour plus tard *)
Notation "'foreach i '=' min 'to' max '{{' body }}" := (foreach' min max (fun i => (body))) (at level 60, i ident, min at level 60, 
max at level 60, body at level 60, right associativity).

(*  format "'[v' '[' 'foreach'  i  '='  min  'to'  max ']' '/' '[' '{{' body '}}' ']' ']'")  *)

(* Compute runState (foreach i = 0 bip 5 {{liftT (changeState i)}} init_S. *)

Compute runState (foreach' 0 5 (fun i => (liftT (changeState i)))) init_S.
 *)
