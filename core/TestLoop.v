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

Definition init_tableT (size : nat) : State tab unit :=
  foreach size 0 (fun i => loopT_liftT (changeTab i (i + 1))).

Compute runState (init_tablei2 10) [0;0;0;0;0;0;0;0;0;0].

Compute runState (init_tableT 10) [0;0;0;0;0;0;0;0;0;0].

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

Compute runState (init_tablei 10) [0;0;0;0;0;0;0;0;0;0].

Lemma initPEntry (size : nat)  :
  {{fun (s : tab) => initPgoodi size s /\ (length s > size)}} init_tablei size 
  {{fun _ (s : tab) => initPgoodEndI s}}.
  Proof.
  unfold init_tablei.
  apply strengthen with (fun _ (s : tab) => initPgoodi size s /\ length s > size).
  induction size.
  + cbn.
    intros s H; trivial.
  + unfold foreach.
    cbn.
    eapply bindRev.
    - unfold runLoopT.
      unfold loopT_liftT.
      unfold state_liftM.
      eapply bindRev.
      eapply weaken.
      eapply LchangeTab.
      cbn.
      intros.
      pattern s in H.
       match type of H with
      | ?HT s => instantiate (1 := fun tt s => HT s )
      end.
      simpl.
      destruct H as (Hinit & Hlen).
(*       
    unfold initPgoodi in H.
    intuition.
    cbn.
    eapply *)
  Admitted.  
 
Definition Prop1 (n : nat) (st : tab) : Prop :=
  (length st = n) /\ initPgoodi n st.

Definition Prop2 (n : nat) (st : tab) : Prop :=
  (length st > n) /\ initPgoodi_inv n st.

Lemma initPEntryI2 (size : nat) :
  {{fun (s : tab) => Prop2 0 s }} init_tablei2 size 
  {{fun _ (s : tab) => initPgoodEndI s}}.
  Proof.
  unfold init_tablei.
  eapply strengthen.
  eapply foreach2_rule2; unfold Prop2 in *.
  + intros.
    unfold Prop2.
    eapply weaken.
    eapply l_modify.
    intros.
    destruct H.
    destruct H.
    unfold initPgoodi_inv in *.
    split.
    intuition.
    assert (length (changeElement it (it + 1) s) = length s).
(*     rewrite <- H at 3. *)
    apply LchangeElement_size2.
    omega.
    intros.
    pose proof LchangeElement_nth.
    intuition.
    assert (i < length (changeElement it (it + 1) s)) by omega.
    generalize (H3 it (it + 1) s).
    intros.
    assert (readTabEntry it (changeElement it (it + 1) s) = it + 1).
    apply H7.
    omega.
    pose proof LchangeElement_inf.
    generalize (H9 it (it + 1) s i).
    intros.
    assert (readTabEntry i s = i + 1).
    auto.
    rewrite <- H11.
    apply H10.
    omega.
  + unfold Prop2.
    intros s [] HP.
    destruct HP.
(*     unfold initPgoodEndI. *)
    (* intros. *)
    unfold initPgoodi_inv in H0.
    unfold initPgoodEndI.
    Admitted.
(*     replace (i <= size < length s) with (i < length s) in H0.
    intros.
    apply H0.
    split.
    
 Qed. *)
  
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

(* Lemma LgetSize (P : nat -> tab -> Prop) :
{{ fun s : tab => P (length s)  s }} 
  getSize {{ fun s => P s}}.
  Proof.
  unfold getSize.
  eapply bindRev.
  + apply l_get. *)

Lemma initPEntryI3 :
  {{fun (s : tab) => Prop2 0 s }} init_tablei3 
  {{fun _ (s : tab) => initPgoodEndI s}}.
  Proof.
  unfold init_tablei3.
  eapply bindRev.
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
    omega. (* 
    intros. *)
    pose proof LchangeElement_nth.
(*     intuition. *)
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

(* Lemma initPEntryI (size : nat)  :
  {{fun (s : tab) => Prop1 size s }} init_tablei size 
  {{fun _ (s : tab) => initPgoodEndI s}}.
  Proof.
  unfold init_table0.
  eapply strengthen.
  eapply foreach_rule2; unfold Prop1.
  + intros.
    unfold changeTab.
    eapply weaken.
    eapply l_modify.
    intros.
    destruct H.
    simpl.
    split.
    intuition.
    rewrite <- H1 at 3.
    apply LchangeElement_size2.
    unfold initPgoodi in *.
    intros.
    unfold readTabEntry in *.
    destruct H.
    SearchAbout nth.
    pose proof LchangeElement_nth.
    generalize (H3 (it - 1) (it)).
    intros.
    apply H2.
    apply nth_in_or_default
    generalize (H (i + 1)).
    intros.
    assert (i + 1 > size).
    omega.
    apply H4 in H5.
    SearchAbout nth.
    pose proof app_nth2.
    generalize (H6 nat [0] s 2 (i+2)).
    intros.
    assert ( i + 2 >= length [0] ).
    cbn.
    omega.
    apply H7 in H8.
    rewrite <- H5 at 2.
    cbn.
    case_eq i.
    intros.
    omega.
    intros.
    subst.
    simpl in H8.
    simpl in H7.
    replace (i + 1 - 1) with i in * by omega.
    case_eq (i + 1).
    intros.
    omega.
    intros.
    rewrite H9 in H8.
    cbn.
    cbn in H7.
    pattern s in H.
     match type of H with
    | ?HT s => instantiate (1 := fun tt s => HT s /\ 
                 readTabEntry 0 s = (size - it + 1 ) )
    end.
    simpl.
    split.
    assumption.
    unfold readTabEntry.
    cbn.
    omega.
    cbn.
    intros.
    trivial.
  Qed. *)

End ResTab.