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

Definition sleb (a b : index) : bool := a <=? b.

(* Definition geb (a b : index) : State tab bool := state_pure (b <=? a). *)
Definition leb (a b : index) : State tab bool := state_pure (a <=? b).
(* Definition ltb (a b : index) : State tab bool := state_pure (a <? b).
Definition gtb (a b : index) : State tab bool := state_pure (b <? a).
Definition eqb (a b : index) : State tab bool := state_pure (a =? b).  *)

(* Lemma ltb  index1 index2 (P : bool -> tab -> Prop):
{{ fun s : tab => P (sltb index1 index2)  s }} 
  MALInternal.Index.ltb index1 index2 {{ fun s => P s}}.
Proof.
unfold MALInternal.Index.ltb, StateLib.Index.ltb.
eapply weaken.
eapply ret .
trivial.
Qed. *)

(* Lemma eqb  index1 index2 (P : bool -> tab -> Prop):
{{ fun s : tab => P (StateLib.Index.eqb index1 index2)  s }} 
  MALInternal.Index.eqb index1 index2 {{ fun s => P s}}.
Proof.
unfold MALInternal.Index.eqb, StateLib.Index.eqb.
eapply weaken.
eapply ret .
trivial.
Qed. *)

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

(* initialise le tableau avec size 0 *)
(* Fixpoint initT0aux (size : nat) : State tab unit :=
  match size with
    | 0 => state_pure tt
    | S size1 => addElement 0 ;;
                 initT0aux size1
  end.

Definition initT0 : State tab unit :=
  initT0aux tableSize. *)

(* change un element dans une liste *)
(* Fixpoint changeElement (i n : nat) (l: list nat) : list nat :=
 match (l,i) with
  | ([], _) => []
  | (a :: l', 0) => n :: l'
  | (a :: l', S i') => a :: changeElement i' n l'
  end.

(* change un élement dans notre tableau *)
Definition changeTab (i n: nat) : State tab unit :=
  modify (fun s => {| mytab := changeElement i n (mytab s)|}). *)

(* Compute Nat.ltb 3 1. *)

Fixpoint init_table_aux (timeout : nat) (idx : index) : State tab unit :=
  match timeout with
    | 0 => state_pure tt
    | S ti' => perf maxindex <- getMaxIndex ;
               perf res <- leb idx maxindex ;
               if (res) then
                  changeTab idx idx ;;
                  perf nextIdx <- Idxsucc idx ;
                  init_table_aux ti' nextIdx
               else
                  state_pure tt
   end.

Definition init_table (idx : index) : State tab unit :=
  initT0 ;;
  init_table_aux maxTimeOut idx.

Lemma initPEntry (idx : index) :
  {{fun (s : tab)=> True}} init_table idx {{fun _ s => True}}.
  Proof.
  unfold init_table.
  unfold init_table_aux.
  assert (Hsize : tm + m >= tm) by omega.
  revert Hsize.
  revert m.
  generalize tm.
  induction tm0.
  + intros.
    eapply weaken.
    eapply ret.
    simpl.
    auto.
  + intros.
    