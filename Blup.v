Require Import List Bool Arith Omega. 
Import List.ListNotations.


(* Definition maxVint := 5.
Definition nbLevel := 2.
Definition tableSize := 12.
Definition nbPage := 100.
Definition contextSize := 5.
Lemma nbLevelNotZero: nbLevel > 0.
Proof. unfold nbLevel; auto. Qed.
Lemma tableSizeNotZero : tableSize <> 0.
Proof. unfold tableSize; auto. Qed. *)

Axiom tableSize nbLevel nbPage maxVint contextSize : nat.
Axiom nbLevelNotZero: nbLevel > 0.
Axiom nbPageNotZero: nbPage > 0.
Axiom maxVintNotZero: maxVint > 0.
Axiom contextSizeNotZero: contextSize > 0.
Axiom contextSizeLessThanTableSize: contextSize < tableSize.

Axiom tableSizeIsEven : Nat.Even tableSize.
(* END NOT SIMULATION *)
Definition tableSizeLowerBound := 14.
Axiom tableSizeBigEnough : tableSize > tableSizeLowerBound. (* to be fixed on count **) 
Record index := {
  i :> nat ;
  Hi : i < tableSize }.

Record page := { 
  p :> nat;
  Hp : p < nbPage }.

Definition paddr := (page * index)%type.

Record vaddr := {
  va :> list index ;
  Hva : length va = nbLevel + 1}.

Record level := {
  l :> nat ;
  Hl : l < nbLevel }.

Record count := {
  c :> nat ;
  Hnb : c <= (3*nbLevel) + 1  ;
}.

Record boolvaddr := {
success : bool;
FFvaddr : vaddr;
}.

Definition userValue := nat.
Definition vint := nat.
Definition contextAddr := nat.

Record interruptMask := {
 m :> list bool;
 Hm : length m = maxVint+1;
}.

Parameter index_d : index.
Parameter page_d : page.
Parameter level_d : level.
Parameter count_d : count.
Parameter int_mask_d : interruptMask.

Require Import Coq.Program.Tactics.

Program Definition CIndex  (p : nat) : index := 
if (lt_dec p tableSize) then 
Build_index p _ else index_d.


Program Definition CPage (p : nat) : page := 
if (lt_dec p nbPage) then Build_page p _ else  page_d.

Program Definition CVaddr (l: list index) : vaddr := 
if ( Nat.eq_dec (length l)  (nbLevel+1))  
  then Build_vaddr l _
  else Build_vaddr (repeat (CIndex 0) (nbLevel+1)) _.


(* BEGIN NOT SIMULATION *)

Next Obligation.
apply repeat_length.
Qed. 

(* END NOT SIMULATION *)


Program Definition CLevel ( a :nat) : level := 
if lt_dec a nbLevel then Build_level a _ 
else level_d .

Program Definition CCount ( a :nat) : count := 
if le_dec a ((3*nbLevel) + 1) then  Build_count a _ 
else count_d .

Program Definition CIntMask (m : list bool) : interruptMask :=
if Nat.eq_dec (length m) (maxVint+1) then Build_interruptMask m _
else int_mask_d.

Record Pentry : Type:=
{read :bool;
 write : bool ;
 exec : bool;
 present : bool;
 user    : bool;
 pa      : page
}.