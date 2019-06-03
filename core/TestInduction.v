Require Import LoopV2 Program List ZArith Arith.
Require Import Coq.Logic.ProofIrrelevance Omega Setoid.

(* Begin simulation *)
(*   Definition tableSize := 10.
  Definition maxTimeOut := 20. *)
(* End simulation *)

Axiom tableSize : nat.
Axiom maxTimeOut : nat.


Axiom tableSizeNotZero : tableSize > 0.
Axiom timeOutNotZero : maxTimeOut > 0.
Axiom timeOutBiggerTableSize : tableSize < maxTimeOut.

Record index := {
  i :> nat ;
  Hi : i < tableSize }.

Record tab : Type := {
  mytab : list nat
}.

Program Definition defaultIndex : State tab index :=
  state_pure (Build_index 0 _).
  Next Obligation.
  apply tableSizeNotZero.
  Qed.

Definition sltb (a b : index) : bool := a <? b.

(* Definition geb (a b : index) : State tab bool := state_pure (b <=? a). *)
(* Definition leb (a b : index) : State tab bool := state_pure (a <=? b). *)
Definition ltb (a b : index) : State tab bool := state_pure (a <? b).
(* Definition gtb (a b : index) : State tab bool := state_pure (b <? a).
Definition eqb (a b : index) : State tab bool := state_pure (a =? b).  *)

Lemma Lsltb  index1 index2 (P : bool -> tab -> Prop):
{{ fun s : tab => P (sltb index1 index2)  s }} 
  ltb index1 index2 {{ fun s => P s}}.
Proof.
unfold ltb, sltb.
eapply weaken.
eapply ret .
trivial.
Qed.


Program Definition CIndex  (p : nat) : index := 
  if (lt_dec p tableSize) then 
    Build_index p _ 
  else (Build_index 0 _).
  Next Obligation.
  apply tableSizeNotZero.
  Qed.

Program Definition Idxsucc (n : index) : State tab index :=
  let isucc := n+1 in
  if (lt_dec isucc tableSize)
  then
    state_pure (Build_index isucc _)
  else defaultIndex.

Definition Sidxsucc (n : index): option index:=
  let isucc := n + 1 in
  match lt_dec isucc tableSize with
  | left x =>
      Some {| i := isucc; Hi := Idxsucc_obligation_1 n x |}
  | right _ => None
  end.

Lemma Inv_ltb index1 index2 (P : tab -> Prop):
{{ fun s : tab => P s }} ltb index1 index2 
{{ fun b s => P s /\ b = sltb index1 index2}}.
Proof.
eapply weaken.
eapply Lsltb.
intros. simpl. split;trivial.
Qed.

Program Definition getMaxIndex : State tab index:=
state_pure (Build_index (tableSize - 1) _).
  Next Obligation.
  assert (tableSize > 0).
  + apply tableSizeNotZero.
  + intuition.
  Qed.

Lemma LgetMaxIndex P : 
{{ fun s => P s }} getMaxIndex 
{{ fun idx s => P s /\ idx = CIndex (tableSize -1) }}.
Proof.
unfold getMaxIndex.
eapply weaken.
+ eapply ret. 
+ intros.
  simpl. split. assumption.
unfold CIndex.
case_eq ( lt_dec (tableSize - 1) tableSize ).
  - intros.     
    f_equal. apply proof_irrelevance.
  - assert (tableSize > 0).
    apply tableSizeNotZero.
    intuition.
Qed.

(* compare 2 listes *)
Fixpoint eqList {A : Type} (l1 l2 : list A) (eq : A -> A -> bool) : bool := 
 match l1, l2 with 
 |nil,nil => true
 |a::l1' , b::l2' => if  eq a b then eqList l1' l2' eq else false
 |_ , _ => false
end.

(* Taille du tableau *)
Definition getTableSize : State tab nat:=
  state_pure tableSize.

(* ajoute un element dans la liste *)
Definition addElement (n : nat) : State tab unit :=
  modify (fun s => {| mytab := n :: (mytab s)|}).

(* An assignment is locally consistent if its precondition is the appropriate 
substitution of its postcondition:
 *)
Lemma LaddElement (n : nat) (P : unit -> tab -> Prop) :
{{fun  s => P tt {| mytab := n :: (mytab s) |} }} addElement n {{P}}.
Proof.
unfold addElement.
eapply weaken.
eapply l_modify.
intros.
simpl.
assumption.
Qed.

(* initialise le tableau avec size 0 *)
Fixpoint initT0aux (size : nat) : State tab unit :=
  match size with
    | 0 => state_pure tt
    | S size1 => addElement 0 ;;
                 initT0aux size1
  end.

Definition initT0 : State tab unit :=
  initT0aux tableSize.

(* change un element dans une liste *)
Fixpoint changeElement (i n : nat) (l: list nat) : list nat :=
 match (l,i) with
  | ([], _) => []
  | (a :: l', 0) => n :: l'
  | (a :: l', S i') => a :: changeElement i' n l'
  end.

(* change un élement dans notre tableau *)
Definition changeTab (i n: nat) : State tab unit :=
  modify (fun s => {| mytab := changeElement i n (mytab s)|}).

(* (* regarde qu'un element est bien placé dans le tableau *)
Definition readTabEntry (idx : index) : State tab nat :=
  perf ltab <- @get tab ;
  state_pure (nth idx (mytab ltab) 0). *)

Definition readTabEntry (idx : index) (ltab : tab) : nat :=
  nth idx (mytab ltab) 0.

(* Compute Nat.ltb 3 1. *)

Fixpoint init_table_aux (timeout : nat) (idx : index) : State tab unit :=
  match timeout with
    | 0 => state_pure tt
    | S ti' => perf maxindex <- getMaxIndex ;
               perf res <- ltb idx maxindex ;
               if (res) then
                  addElement idx ;;
                  perf nextIdx <- Idxsucc idx ;
                  init_table_aux ti' nextIdx
               else
                  state_pure tt
   end.

Definition init_table (idx : index) : State tab unit :=
  init_table_aux tableSize idx.

(* montrer que ∀ idx < currentidx, tab[idx] = idx *)
Lemma initPEntry (idx : index) :
  {{fun (s : tab)=> True}} init_table idx {{fun _ s => True}}.
  Proof.
  unfold init_table.
  unfold init_table_aux.
  assert(Hsize : tableSize + idx >= tableSize) by omega.
  revert Hsize.
  revert idx.
  generalize tableSize at 1 3.
  induction n.
  + intros.
    eapply weaken.
    eapply ret.
    simpl.
    auto.
  + intros.
    simpl.
    (* getMaxIndex *)
    eapply bindRev.
    - eapply weaken.
      eapply LgetMaxIndex.
      intros.
      simpl.
      apply H.
(*       pattern s in H.
      eassumption. *)
    - intros maxidx. simpl. 
      (* Index leb *)
      eapply bindRev.
      eapply weaken.
      eapply Inv_ltb.
      intros. simpl.
      pattern s in H.
      eapply H.
      intros ltbindex.
      simpl.
  (* last entry *)
  case_eq ltbindex ; intros HnotlastEntry.
  eapply bindRev.
  eapply weaken.
  eapply LaddElement.
  simpl.
  intros.
  try repeat rewrite and_assoc in H.
  pattern s in H.
  match type of H with
  | ?HT s => instantiate (1 := fun tt s => HT s /\ 
               readTabEntry idx s = idx )
  end.
  simpl.
  destruct H as (Hreadlt & Hmax & Hlt).
  split. split.
  trivial.
  repeat split ; assumption.
  unfold readTabEntry.
  cbn.
  