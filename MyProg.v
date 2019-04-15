(* Require Import Monad. *)
Load loop_monad.

Record S := {
  myval : nat
}.

Definition init_val := 0.

Definition init_S := {| myval := init_val|}.

Definition changeState (i : nat) : loop_monad.State unit :=
  modify (fun s => {| myval := s.(myval) + i |}).