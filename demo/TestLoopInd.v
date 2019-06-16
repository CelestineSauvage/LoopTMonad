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
  forall (l : tab) (j : nat) , j <= i < length l -> readTabEntry j (changeElement i n l) = readTabEntry j l.
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

Definition init_table (size : nat) : State tab unit :=
  for i = size to 0 {{
    addElement (i)
  }}.

Definition init_tablei (size : nat) : State tab unit :=
  for i = size to 0 {{
    changeTab (i - 1) i
  }}.

Definition init_tablei2 (size : nat) : State tab unit :=
  for2 i = 0 to size {{
    changeTab i (i + 1)
  }}.

Compute runState (init_tablei2 10) [0;0;0;0;0;0;0;0;0;0].

Definition init_table0 (size : nat) : State tab unit :=
  for i = size to 0 {{
    addElement 0
  }}.

Definition initPgoodi (curidx : nat) (l : tab) : Prop :=
  forall i : nat, curidx < i < length l -> readTabEntry i l = i+1.

Definition initPgoodi_inv (curidx : nat) (l : tab) : Prop :=
  forall i : nat, i <= curidx < length l -> readTabEntry i l = i+1.

(* Definition init_table2 (size : nat) : State tab unit :=
  for_e i = maxTimeOut to 0 {{$
    if (
    addElement (size - i + 1)
  }}. *)

Definition initPgoodEnd0 (l : tab) : Prop :=
  forall i : nat, i < length l -> readTabEntry i l = 0.

Definition initPgoodEndI (l : tab) : Prop :=
  forall i : nat, i < length l -> readTabEntry i l = i + 1.

Definition Prop1 (n : nat) (st : tab) : Prop :=
  (length st = n) /\ initPgoodi n st.

Definition Prop2 (n : nat) (st : tab) : Prop :=
  (length st > n) /\ initPgoodi_inv n st.

Definition getSize : State tab nat :=
  perf s <- (@get tab);
  state_pure (length s).

Definition init_tablei3 : State tab unit :=
  perf size <- getSize ;
  for2 i = 0 to size {{
    changeTab i (i + 1)
  }}.

Definition Prop3 (n : nat) (st : tab) : Prop :=
  initPgoodi_inv n st.

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

Lemma initPEntryI3 :
  {{fun (s : tab) => Prop2 0 s }} init_tablei3 
  {{fun _ (s : tab) => initPgoodEndI s}}.
  Proof.
  unfold init_tablei3.
  eapply bindRev.
  + apply LgetSize.
  + intros.
    induction a; unfold foreach2; simpl.
    - intros s HSt.
      destruct HSt.
      unfold Prop2 in H.
      omega.
   - eapply bindRev.
     unfold runLoopT.
     unfold loopT_liftT.
     unfold state_liftM.
     eapply bindRev.
     * intros.
       eapply weaken.
       eapply l_modify.
       intros.
       unfold Prop2 in *.
       intuition.
   Admitted.

End ResTab.