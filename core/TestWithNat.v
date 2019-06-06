Require Import LoopV2 Program List ZArith Arith Coq.Logic.Classical_Prop.


Definition init_state : nat := 1.

Definition add_s (i : nat) : State nat unit :=
  modify (fun s => s + i).

Definition slow_add (m : nat) : State nat unit :=
  for i = m to 0 {{
    add_s 1
  }}.

Lemma l_slow_add (m : nat) : 
 {{(fun s : nat => s = 0)}} slow_add m {{(fun (_ : unit ) (s : nat) => s >= m)}}.
  Proof.
  unfold slow_add.
  eapply weaken.
  
(*   eapply strengthen. *)
  apply foreach_rule.
  unfold add_s.
  intros.
  eapply weaken.
  apply l_modify.
  simpl.
  intros.
  auto.
  simpl.
  intros.
  auto.