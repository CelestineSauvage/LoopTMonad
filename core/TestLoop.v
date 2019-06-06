Require Import LoopV2 Program List ZArith Arith Coq.Logic.Classical_Prop.

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
  nth idx ltab idx.

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
  forall (l : tab)  , i < length l -> nth i (changeElement i n l) n = n.
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
      apply IHl.
      apply H.
  Qed.


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
    changeTab (i-1) i 
  }}.

(* Definition init_table (size : nat) : State tab unit :=
(*   initT0 ;; *)
  init_table_aux size. *)

(* Compute runState init_table {| mytab := [] |}. *)

Definition goodInitT0 (size : nat) (l : tab) : Prop := 
  length l = size /\ (forall i : nat, 0 <= i < size /\ (readTabEntry i l = 0)).

Definition goodInitTable (size : nat) (l : tab) : Prop :=
  length l = size /\ (forall i : nat, 0 <= i < size /\ (readTabEntry i l = i + 1 )).

Definition goodInitITable (size i_max : nat) (l : tab) : Prop :=
  length l = size /\ (forall i : nat, 0 <= i < i_max /\ (readTabEntry i l = i + 1 )).

(* Definition invariantTable (i :  (l : tab) : Prop *)


Lemma initPEntry (size : nat)  :
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
        intros.