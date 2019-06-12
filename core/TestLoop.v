Require Import LoopV2 Program List ZArith Arith Coq.Logic.Classical_Prop.

Set Implicit Arguments.

Section ResNat.

Record MySt : Type:= {
  r : nat;
}. 

Definition init_state : MySt := {|r := 1|}.

Definition add_s (i : nat) : State MySt unit :=
  modify (fun s => {| r := s.(r) + i |}).

Definition min_s (i : nat) : State MySt unit :=
modify (fun s => {| r := s.(r) - i |}).

Definition mul_s (i : nat) : State MySt unit :=
  modify (fun s => {| r := s.(r) * i |}).

(* Definition fac5 : State unit :=
  for i = 5 to 0 {{
    mul_s i
  }}.
 *)
(* Compute runState fac5 init_state.  *)

(* Definition test_exit : State () :=
   for_e i = 0 to 20 {{
    if (i =? 5) then break
    else (loopT_liftT (add_s 1))
  }}.
 *)
(* Compute runState test_exit init_state.  *)

(* in_seq: forall len start n : nat, In n (seq start len) <-> start <= n < start + len *)


(* Lemma foreach_break_rule_2 (min max : nat) (P : () -> St -> Prop) (body : nat -> State ()) (compare : State bool)
  : forall (cond : bool), (forall (it : nat), {{fun s => P tt s /\ (min <= it <= max) /\ (cond s = true) }} body it {{P}}) -> 
    {{P tt}} foreach max min (fun it0 => perf cond <- compare;  if (fun s => cond s) then break else loopT_liftT (body it0))
    {{fun _ s => P tt s /\ (cond s) = false}}.
  Admitted. *)

Definition slow_add (m : nat) : State MySt unit :=
  for i = m to 0 {{
    add_s m
  }}.

(* Definition fast_add : State unit :=
  for i = 5 to 0 {{
    add_s i
  }}. *)

Definition compare : State MySt bool :=
  perf s <- (@get MySt) ;
  state_pure (Nat.leb (r s) 2).

(* Definition parity_x : State unit :=
  for_e i = 500 to 0 {{
    perf cond <- compare;
    if (cond) then break
    else loopT_liftT(min_s 2)
  }}.
 *)
(* Compute runState parity_x {| r := 10 |}. *)

(* Lemma l_parity_x :
  {{(fun s : St => r s = 10)}} parity_x {{(fun (_ : unit ) (s : St) => r s = 2)}}.
  Admitted. *)
(* Lemma foreach_rule (min max : nat) (P : () -> St -> Prop) (body : nat -> State ())
  : (forall (it : nat), {{fun s => P tt s /\ (min <= it <= max)}} body it {{P}}) -> 
    {{P tt}} foreach max min (fun it0 => loopT_liftT (body it0)) {{fun _ s => P tt s}}. *)
Lemma l_slow_add (m : nat) : 
 {{(fun s : MySt => True)}} slow_add m{{(fun (_ : unit ) (s : MySt) => r s >= m)}}.
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
  Admitted.

Fixpoint sumsum (n : nat): nat :=
  match n with
    | 0 => 0
    | S n' => n + (sumsum n')
  end.
  
(* Lemma l_fast_add (n : nat):
  {{(fun s : St => r s = n)}} fast_add {{(fun (_ : unit ) (s : St) => r s < (Nat.add (sumsum 5) n))}}.
  Proof.
  apply weaken with (fun s => r s <= 42).
  eapply strengthen.
  apply foreach_rule. *)

End ResNat.

Section ResTab.

Axiom tableSize : nat.
Axiom maxTimeOut : nat.
Axiom defaultValue : nat.

Axiom tableSizeNotZero : tableSize > 0.
Axiom timeOutNotZero : maxTimeOut > 0.
Axiom timeOutBiggerTableSize : tableSize < maxTimeOut.

(* Definition tableSize := 10. *)

(* Record index := {
  i :> nat ;
  Hi : i < tableSize }. *)

(* Record tab : Type := {
  mytab : list nat
}. *)

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

Definition initT0 : State tab unit :=
  for i = tableSize to 0 {{
    addElement 0
  }}.

Definition readTabEntry (idx : nat) (ltab : tab) : nat :=
  nth idx ltab defaultValue.

(* Definition goodInitT0 (l : tab) :=
  exists i : nat, length (mytab l) = i /\ (readTabEntry i l = 0). *)

(* Lemma LAddElement (i : length) (P : unit -> tab -> Prop) :
  {{fun s => P tt s /\ }} addElement 0 *)

(* Lemma LinitT0 (P : unit -> tab -> Prop) :
  {{fun s => P tt s /\ goodInitT0 s}} initT0 {{fun _ s => P tt s /\ goodInitT0 s}}.
  Proof.
  unfold initT0.
  apply foreach_rule.
  + intros it s H.
    apply LaddElement.
    intuition.
    -  
  Qed. *)

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

(* Lemma LchangeElement_read (i : nat) (n : nat) :
  forall (l : tab)  , i < length l -> readTabEntry i (changeElement i n l) = n.
  Admitted. *)

Lemma LchangeElement_inf (i : nat) (n : nat) :
  forall (l : tab) (j : nat) , j <= i < length l -> readTabEntry j (changeElement i n l) = readTabEntry j l.
  Admitted.

(* Lemma LchangeElement (i n : nat) :
  forall l : list nat, i < length l -> nth i (changeElement i n l) n = n.
  Proof.
  induction l.
  + intros.
    simpl in H.
    inversion H. 
  + intros.
    
 *)
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

(* Definition Prop1 (n : nat) (st : tab) : Prop :=
  (length st = n) /\ initPgoodi n st. *)

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

Lemma LgetSize P : 
{{ fun s => P s }} getSize 
{{ fun size s => P s /\ size = length s }}.
(*   Proof.
  unfold getSize.
  eapply bindRev.
  + apply l_get.
  + intros.
    simpl.
    split.
    assumption.
    reflexi
 *)
  

Lemma initPEntryI3 (size : nat) :
  {{fun (s : tab) => Prop3 0 s }} init_tablei3 
  {{fun _ (s : tab) => initPgoodEndI s}}.
  Proof.
  unfold init_tablei3.
  eapply bindRev.
  
  eapply strengthen.
  eapply foreach2_rule2; unfold Prop3 in *.
  + intros.
    eapply weaken.
    eapply l_modify.
    intros.
    destruct H.
    unfold initPgoodi_inv in *.
    intuition.
(*     assert (length (changeElement it (it + 1) s) = length s). *)
(*     rewrite <- H at 3. *)
(*     apply LchangeElement_size2. *)
(*     omega. *)
(*     intros. *)
    pose proof LchangeElement_nth.
(*     intuition. *)
    assert (i < length (changeElement it (it + 1) s)) by omega.
    generalize (H0 it (it + 1) s).
    intros.
    assert (readTabEntry it (changeElement it (it + 1) s) = it + 1).
    apply H6.
    omega.
    pose proof LchangeElement_inf.
    generalize (H9 it (it + 1) s i).
    intros.
    assert (readTabEntry i s = i + 1).
    auto.
    rewrite <- H11.
    apply H10.
    omega.

Lemma initPEntryI (size : nat)  :
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
  Qed.


(* Definition goodInitTable (curidx : nat) (l : tab) : Prop :=
  (forall i : nat, 0 <= i < curidx /\ (readTabEntry i l = (curidx - i) + 1 )). *)

Definition initPgood (size curidx : nat) (l : tab) : Prop :=
  readTabEntry curidx l = (curidx - i) + 1 ))

Lemma initPEntry2 (size : nat)  :
  {{fun (s : tab) => goodInitTable 0 s}} init_table size {{fun _ s => goodInitTable size s}}.
  Proof.
  unfold init_table.
  eapply strengthen.
  eapply weaken.
  eapply foreach_rule.
  2: { 
  intros.
  eapply H.
  }
  1: {
  + intros.
    unfold addElement.
    eapply weaken.
    eapply l_modify.
    intros.
    simpl.
    pattern s in H.
     match type of H with
    | ?HT s => instantiate (1 := fun tt s => HT s /\ 
                 readTabEntry 0 s = (size - it + 1 ) )
    end.

Definition init_table2 (size : nat) : State tab unit :=
  for i = size to 0 {{
    addElement (size - i + 1)
  }}.

(* Definition goodInitT0 (size : nat) (l : tab) : Prop := 
  length l = size /\ (forall i : nat, 0 <= i < size /\ (readTabEntry i l = 0)).

Definition goodInitTable (size : nat) (l : tab) : Prop :=
  length l = size /\ (forall i : nat, 0 <= i < size /\ (readTabEntry i l = i + 1 )).

Definition goodInitITable (size i_max : nat) (l : tab) : Prop :=
  length l = size /\ (forall i : nat, 0 <= i < i_max /\ (readTabEntry i l = i + 1 )).
 *)
(* Definition invariantTable (i :  (l : tab) : Prop *)

(* Lemma initPEntry (size : nat)  :
  {{fun (_ : tab) => True}} init_table size {{fun _ _ => True}}.
  Proof.
  (* revert size. *)
  unfold init_table.
  unfold foreach.
  induction size.
  (* induction size. *)
  + cbn.
    eapply weaken.
    apply ret.
    trivial.
  + cbn.
    eapply bindRev.
    - unfold runLoopT. unfold loopT_liftT. unfold state_liftM.
      eapply bindRev.
      * eapply weaken.
        apply LaddElement.
        intros.
        simpl.
        pattern s in H.
        match type of H with
        | ?HT s => instantiate (1 := fun tt s => HT s /\ 
                     readTabEntry 0 s = 1 )
        end.
        simpl.
        split.
        trivial.
        unfold readTabEntry.
        cbn.
        omega.
     *  intros [].
        intros s H.
        cbn. *)
        
(* Lemma initPEntry (size : nat)  :
  {{fun (s : tab) => goodInitT0 size s}} init_table size {{fun _ s => goodInitTable size s}}.
  Proof.
  unfold init_table.
(*   unfold foreach. *)
  apply weaken with (fun s => goodInitITable size size s).
  (* 2 : intros. *)
  induction size.
  +  intros s_init Hinit.
      cbn.
      unfold goodInitITable in Hinit.
      unfold goodInitTable.
      assumption.
  + unfold foreach. 
    case_eq (S size <=? 0).
    - intros s.
      unfold goodInitTable.
      intros s0 H2.
      unfold goodInitITable in H2.
      simpl.
      apply H2.
    - intros.
      simpl in H.
      eapply bindRev.
      unfold runLoopT.
      unfold loopT_liftT.
      unfold state_liftM.
      eapply bindRev.
      (* eapply weaken. *)
      eapply LchangeTab.
      * simpl.
        intros. *)