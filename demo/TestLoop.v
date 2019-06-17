Require Import LoopV2 Program List ZArith Arith Coq.Logic.Classical_Prop.

Set Implicit Arguments.

Section ResTab.

(* Axiom tableSize : nat.
Axiom maxTimeOut : nat. *)
Axiom defaultValue : nat.

(* Axiom tableSizeNotZero : tableSize > 0.
Axiom timeOutNotZero : maxTimeOut > 0.
Axiom timeOutBiggerTableSize : tableSize < maxTimeOut. *)

Definition tab : Type := list nat.

Definition addElement (n : nat) : State tab unit :=
  modify (fun s => n :: s).

Lemma LaddElement (n : nat) (P : unit -> tab -> Prop) :
{{fun  s => P tt (n :: s) }} addElement n {{P}}.
Proof.
unfold addElement.
eapply weaken.
eapply l_modify.
intros.
simpl.
assumption.
Qed.


Definition readTabEntry (idx : nat) (ltab : tab) : nat :=
  nth idx ltab defaultValue.


Fixpoint changeElement (i n : nat) (l: tab) : tab :=
 match (l,i) with
  | ([], _) => []
  | (a :: l', 0) => n :: l'
  | (a :: l', S i') => a :: changeElement i' n l'
  end.

SearchAbout nil.

Lemma LchangeElement_size1 (l : tab)  :
  forall (i n : nat), length l = length (changeElement i n l).
  Admitted.

Lemma LchangeElement_size2 (l : tab)  :
  forall (i n : nat), length (changeElement i n l) = length l.
  Admitted.

Lemma LchangeElement_in (i : nat) (n : nat) :
  forall (l : tab)  , i < length l -> In n (changeElement i n l).
  Proof.
  intro l.
  generalize i.
  induction l.
  - intros.
    simpl in H.
    omega.
  - simpl in *.
    induction i0.
    + intros. simpl. auto.
    + intros.
      apply lt_S_n in H.
      simpl.
      right.
      apply IHl.
      apply H.
  Qed.

Lemma LchangeElement_nth (i : nat) (n : nat) :
  forall (l : tab)  , i < length l -> readTabEntry i (changeElement i n l) = n.
  Proof.
(*   Admitted. *)
  intro l.
  generalize i.
  induction l.
  - intros.
    simpl in H.
    omega.
  - simpl in *.
    induction i0.
    + intros. simpl. auto.
    + intros.
      apply lt_S_n in H.
      simpl.
      apply IHl.
      apply H.
  Qed.

Lemma LchangeElement_inf (i : nat) (n : nat) :
  forall (l : tab) (j : nat) , j < i < length l -> readTabEntry j (changeElement i n l) = readTabEntry j l.
  Admitted.

Definition changeTab (i n: nat) : State tab unit :=
  modify (fun s => changeElement i n s).

Lemma LchangeTab (i : nat) (n : nat) (P : unit -> tab -> Prop) :
  {{fun  s => P tt (changeElement i n s) }} changeTab i n {{P}}.
  Proof.
  unfold addElement.
  eapply weaken.
  eapply l_modify.
  intros.
  simpl.
  assumption.
  Qed.

Definition getSize : State tab nat :=
  perf s <- (@get tab);
  state_pure (length s).

Lemma LgetSizeWp (P : nat -> tab -> Prop) :
{{wp P getSize}} getSize {{P}}.
  Proof.
  eapply wpIsPrecondition.
  Qed.

Lemma LgetSize P : 
{{ fun s => P s }} getSize 
{{ fun size s => P s /\ size = length s }}.
  Proof.
    eapply weaken.
    eapply LgetSizeWp.
    cbn.
    intros.
    intuition.
  Qed.

Definition init_tablei3 : State tab unit :=
  perf size <- getSize ;
  for2 i = 0 to size {{
    changeTab i (i + 1)
  }}.

Compute runState (init_tablei3) [0;0;0;0;0;0;0;0;0;0].


Definition initPgoodi_inv (curidx : nat) (l : tab) : Prop :=
  forall i : nat, i < curidx < length l -> readTabEntry i l = i+1.

Definition initPgoodEndI (l : tab) : Prop :=
  forall i : nat, i < length l -> readTabEntry i l = i + 1.

Definition Prop2 (n : nat) (st : tab) : Prop :=
  (length st > n) /\ initPgoodi_inv n st.

Lemma initPEntryI3 :
  {{fun (s : tab) => Prop2 0 s }} init_tablei3 
  {{fun _ (s : tab) => initPgoodEndI s}}.
  Proof.
  unfold init_tablei3.
  eapply sequence_rule.
  + apply LgetSize.
  + intros.
  eapply strengthen.
  eapply foreach2_rule3. unfold Prop2 in *.
  - intros.
    eapply weaken.
    eapply l_modify.
    intros.
    destruct H.
    unfold initPgoodi_inv in *.
    intuition.
    assert (length (changeElement it (it + 1) s) = length s).
    apply LchangeElement_size2.
    omega. 
    pose proof LchangeElement_nth.
    intuition.
    assert (i < length (changeElement it (it + 1) s)) by omega.
    generalize (H3 it (it + 1) s).
    intros.
    assert (readTabEntry it (changeElement it (it + 1) s) = it + 1).
    apply H8.
    omega.
    pose proof LchangeElement_inf.
    generalize (H10 it (it + 1) s i).
    intros.
    assert (readTabEntry i s = i + 1).
    auto.
    rewrite <- H12.
    apply H10.
    omega.
    assert (length (changeElement it (it + 1) s) = length s).
    apply LchangeElement_size2.
    omega.
  - simpl.
    intros s [] H.
    destruct H.
    unfold Prop2 in *.
    destruct H.
    unfold initPgoodi_inv .
    omega.
Qed.

End ResTab.