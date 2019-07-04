Require Import Program Monads Omega Peano Sorted.

Set Implicit Arguments.

Import Notations.

Module M := Monads.

Open Scope monad_scope.
Arguments Monad m : assert.

Lemma bind_eq : forall {A B m} `{Monad m} (a a' : m A) (f f' : A -> m B),
  a = a' ->
  (forall x, f x = f' x) ->
  bind a f = bind a' f'.
  Proof.
    intros. subst.
    f_equal.
    apply functional_extensionality.
    auto.
  Qed.

Section state_proof.

Variable St : Type.

Definition State := M.State St.

Check State.

Definition hoareTripleS {A} (P : St -> Prop) (m : State A) (Q : A -> St -> Prop) : Prop :=
  forall (s : St), P s -> let (a, s') := m s in Q a s'.

Notation "{{ P }} m {{ Q }}" := (hoareTripleS P m Q)
  (at level 90, format "'[' '[' {{  P  }}  ']' '/  ' '[' m ']' '['  {{  Q  }} ']' ']'") : monad_scope.

Lemma ret (A : Type) `{State A} (a : A) (P : A -> St -> Prop) : {{ P a }} return_ a {{ P }}.
Proof.
intros s H; trivial.
Qed.

Lemma unit_ret `{State unit} (P : St -> Prop) : {{ P }} return_ tt {{fun _ => P }}.
Proof.
intros s H; trivial.
Qed.

Lemma bind (A B : Type) (m : State A) (f : A -> State B) (P : St -> Prop)( Q : A -> St -> Prop) (R : B -> St -> Prop) :
  (forall a, {{ Q a }} f a {{ R }}) -> {{ P }} m {{ Q }} -> {{ P }} perf x <- m ; f x {{ R }}.
Proof.
intros H1 H2 s Hs.
unfold bind.
simpl.
apply H2 in Hs.
unfold M.state_bind.
case_eq (m s).
intros a s' H4.
rewrite H4 in Hs.
apply H1 in Hs.
case_eq (f a s').
intros b s'' H5.
rewrite H5 in Hs.
trivial.
Qed.

Definition wp {A : Type} (P : A -> St -> Prop) (m : State A) :=
  fun s => let (a,s') := m s in P a s'.

Lemma wpIsPrecondition {A : Type} (P : A -> St -> Prop) (m : State A) :
  {{ wp P m }} m {{ P }}.
  Proof.
  unfold wp.
  congruence.
  Qed.

Lemma wpIsWeakestPrecondition
  (A : Type) (P : A -> St -> Prop) (Q : St -> Prop) (m : State A) :
  {{ Q }} m {{ P }} -> forall s, Q s -> (wp P m) s.
  Proof.
  trivial.
  Qed.

Lemma assoc (A B C : Type)(m : State A)(f : A -> State B)(g : B -> State C) :
  perf y <-
    perf x <- m ;
    f x ;
  g y =
  perf x <- m ;
  perf y <- f x ;
  g y.
  Proof.
  extensionality s.
  unfold M.bind.
  case (m s).
  simpl.
  intros.
  unfold state_bind.
  case (m s).
  intros.
  reflexivity.
  Qed.

Lemma put (s : St) (P : unit -> St -> Prop) : {{ fun _ => P tt s }} putS s {{ P }}.
Proof.
intros s0 H;trivial.
Qed.

Lemma get (P : St -> St -> Prop) : {{ fun s => P s s }} @getS St {{ P }}.
Proof.
intros s H; trivial.
Qed.

Lemma sequence_rule (A B : Type) (m : State A) (f : A -> State B) (P : St -> Prop)( Q : A -> St -> Prop) (R : B -> St -> Prop) :
  {{ P }} m {{ Q }} -> (forall a, {{ Q a }} f a {{ R }}) -> {{ P }} perf x <- m ; f x {{ R }}.
Proof.
intros; eapply bind ; eassumption.
Qed.

Lemma weaken (A : Type) (m : State A) (P Q : St -> Prop) (R : A -> St -> Prop) :
  {{ Q }} m {{ R }} -> (forall s, P s -> Q s) -> {{ P }} m {{ R }}.
Proof.
intros H1 H2 s H3.
apply H2 in H3.
apply H1 in H3.
assumption.
Qed.

Lemma strengthen (A : Type) (m : State A) (P: St -> Prop) (Q R: A -> St -> Prop) :
  {{ P }} m {{ R }} -> (forall s a, R a s -> Q a s) -> {{ P }} m {{ Q }}.
Proof.
intros H1 H2 s H3.
apply H1 in H3.
Admitted.

Lemma modify f (P : () -> St -> Prop) : {{ fun s => P tt (f s) }} modify f {{ P }}.
Proof.
unfold modify.
eapply bind.
intros.
eapply put.
simpl.
eapply weaken.
eapply get.
intros. simpl.
assumption.
Qed.

Lemma act_ret  (A : Type) (a : A) (P : St -> Prop) : {{P}} state_pure (Atom a) 
{{fun (_ : Action A) =>  P }}.
Proof.
intros s H; trivial.
Qed.

Lemma foreach_rule (min max : nat) (P : nat -> St -> Prop) (body : nat -> State () ):
  (forall (it : nat), {{fun s => P it s /\ (min < it <= max)}} body it {{fun _ => P (it - 1)}}) /\  min <= max ->
    {{P max}} M.foreach2_st max min (fun it0 => loopeT_liftT (body it0)) {{fun _ => P min}}.
    Proof.
    intros [Hleq Hmaxmin].
    induction max.
     + assert (min = 0) by omega.
      replace min with 0.
      intros s Hs.
      simpl.
      auto.
    + unfold M.foreach2_st.
      unfold M.foreach2.
      case_eq (S max <=? min);intros Hm.
      - intros s HP.
        cbn.
        rewrite Nat.leb_le in Hm.
        assert (S max = min) by omega.
        rewrite H in HP.
        auto.
      - eapply sequence_rule.
        unfold runLoopeT.
        unfold loopeT_liftT.
        unfold liftM.
        eapply sequence_rule.
        intros st H2.
        generalize (Hleq (S max)).
        intros Hmax.
        eapply Hmax;split; auto.
        rewrite Nat.leb_nle in Hm. omega.
        intros [].
        apply act_ret.
      * intros. cbn.
        replace (max - 0) with (max) by omega.
        apply IHmax.
         ++ intros it s'.
            intros [H1 [H2 H3]].
            apply Hleq.
            split;auto.
        ++ rewrite Nat.leb_nle in Hm.
           omega.
       Qed.

Lemma foreach_no_it (body : nat -> State () ) :
  forall min max : nat, min >= max -> M.foreach2_st max min (fun it0 => loopeT_liftT (body it0)) = return_ tt.
  Proof.
  intros.
  induction max; auto.
  apply functional_extensionality.
  intro x.
  unfold M.foreach2_st.
  unfold M.foreach2.
  case_eq (S max <=? min).
  + intros.
    auto.
  + intros.
    rewrite Nat.leb_nle in H0.
    omega.
 Qed.

Open Scope list_scope.

Lemma foreach_plus_no_it (body : nat -> State () ) :
  forall min max : nat, min >= max -> M.foreach3 min max (fun it0 => loopeT_liftT (body it0)) = return_ tt.
  Proof.
  intros.
  unfold foreach3.
  assert (max - min = 0).
  omega.
  assert (List.seq min (max - min) = nil).
  + pose proof List.seq_length.
    rewrite H0.
    generalize (H1 0 min).
    intros.
    cbn in *.
    auto. 
  + rewrite H1.
    cbn.
    auto.
  Qed.

Lemma foreach'_plus_no_it (body : nat -> State () ) :
  forall max : nat, M.foreach3' [] (fun it0 => loopeT_liftT (body it0)) = return_ tt.
  Proof.
  intros.
  cbn.
  auto.
  Qed.

Lemma foreach_rule_noit  (P : nat -> St -> Prop) (body : nat -> State () ):
    forall min max : nat, min >= max ->
    {{P max}} M.foreach2_st max min (fun it => loopeT_liftT (body it)) {{fun _ => P max}}.
    Proof.
    intros min max Hm.
    rewrite foreach_no_it; auto.
    intros s H.
    trivial.
    Qed.

Lemma foreach_rule_plus_no_it (P : nat -> St -> Prop) (body : nat -> State () ) :
  forall min max : nat, min >= max -> {{P max}} M.foreach3 min max 
    (fun it0 => loopeT_liftT (body it0)) {{fun _ => P max}}.
  Proof.
  intros min max Hm.
  rewrite foreach_plus_no_it; auto.
  intros s H; trivial.
  Qed.

Lemma foreach'_rule_plus_no_it (P : nat -> St -> Prop) (body : nat -> State () ) :
  forall max : nat, {{P max}} M.foreach3' [] 
    (fun it0 => loopeT_liftT (body it0)) {{fun _ => P max}}.
  Proof.
  intros min max Hm.
  rewrite foreach'_plus_no_it; auto.
  Qed.

Definition is_succ (a b : nat) : Prop :=
  S a = b.

Check HdRel.

Definition HdSel := HdRel (is_succ).
(* Inductive HdSel (a : nat) : list nat -> Prop :=
  | HdSel_nil : HdSel a []
  | HdSel_cons b l: is_succ a b -> HdSel a (b :: l). *)

Lemma HdSel_inv :
  forall a b l, HdSel a (b :: l) -> is_succ a b.
  Proof.
  intros a b l Hs.
  inversion Hs; auto.
  Qed.

Lemma HdSel_forall_l :
  forall a b l, is_succ a b -> HdSel a (b :: l).
  Proof.
  intros.
  constructor.
  auto.
  Qed.

(* Inductive Ordered_list : list nat -> Prop :=
    | Ordered_list_nil : Ordered_list []
    | Ordered_list_cons a l : Ordered_list l -> HdSel a l -> Ordered_list (a :: l). *)
Definition Ordered_list := @Sorted nat is_succ.

(* Effective computation for ordered_list *)
Fixpoint ordered_list (l : list nat) : bool :=
  match l with
    | [] => true
    | [a] => true
    | a ::((b::_) as l') =>  if (S a =? b) then ordered_list l' else false
  end.

Definition startmin_list (min: nat) (l : list nat) : Prop :=
  match l with 
    | [] => False
    | a :: l' => (a = min)
  end.

(* Inductive Endmax_list : nat -> list nat -> Prop :=
  | Endmax_one a : Endmax_list a [a]
  | Endmax_cons a l: forall b, Endmax_list a l -> Endmax_list a (b :: l) *)

Fixpoint endmax_list (max : nat) (l : list nat) : Prop :=
   match l with 
    | [] => False
    | a :: [] => (a = max)
    | a :: l' => endmax_list max l'
  end.

SearchAbout List.NoDup.

Lemma Sorted_inv :
    forall a l, Ordered_list (a :: l) -> Ordered_list l /\ HdSel a l.
    Proof.
    intros a l Hord.
    inversion Hord;auto.
    Qed.

Lemma hdsel_to_trans :
  forall a b, is_succ a b -> a < b.
  Proof.
  intros a b.
  induction b; intros; unfold is_succ in H; omega.
  Qed.

Lemma sortedone_to_sorted :
  forall l, Ordered_list l -> @Sorted nat lt l.
  Proof.
  induction 1 as [|? ? ? ? HForall]; constructor; trivial.
  destruct HForall; constructor; trivial.
  unfold is_succ in H0.
  omega.
  Qed.

Lemma nextmin_ord_list (min : nat):
  forall l, length l > 0 -> Ordered_list (min :: l) -> startmin_list (S min) l.
  Proof.
  induction l; intros Hlen Hord.
  + cbn in *; intuition.
  + intuition.
    eapply Sorted_inv in Hord; auto.
    destruct Hord.
    eapply HdSel_inv in H0.
    assert (a = S min).
    unfold is_succ in H0.
    auto.
    rewrite H1.
    unfold startmin_list; auto.
  Qed.

(* Lemma Smin_ord_list (min : nat):
  forall l, Ordered_list ((S min) :: l) -> Ordered_list (min :: (S min :: l)).
  Proof.
  intros.
  constructor.
  apply H.
  apply HdRel_cons.
  unfold is_succ.
  auto.
  Qed. *)

(* Lemma Smin_ord_list_inv (min : nat):
  forall l, Ordered_list (min :: (S min :: l)) -> Ordered_list ((S min) :: l).
  Proof.
  intros.
  apply Sorted_inv in H.
  destruct H.
  auto.
  Qed.
 *)
Lemma Sorted_list_no_empty :
  forall min max l, S min < max -> 
    (startmin_list min (min :: l) /\ endmax_list (max - 1) (min :: l) /\ Ordered_list (min :: l) )
    -> length l > 0.
  Proof.
  intros min max l Hminmax [Hst [Hend Hord]].
  induction l.
  + unfold endmax_list in Hend.
    omega.
  + cbn.
    omega.
  Qed.

(* Lemma sorted_add_el :
  forall val > 0,
   *)

Lemma startmin_noempty (l : list nat) :
  forall min, startmin_list min (l) -> length l > 0.
  Proof.
  intros.
  induction l.
  + intuition.
  + cbn.
    omega.
  Qed.

Lemma a_startmin_list (min : nat) (l : list nat) :
  forall (a : nat), startmin_list min (a :: l) -> a = min.
  Proof.
  cbn.
  intros.
  auto.
  Qed.

Lemma a_endmin_list (max: nat) (l : list nat) :
  forall (a : nat), length l > 0 -> endmax_list max (a :: l) -> endmax_list max l.
  Proof.
  intros a H1 H2.
  induction l.
  + cbn in H1.
    intuition.
  + cbn.
    auto.
  Qed. 

Lemma end_in_list :
  forall a l, endmax_list a l -> List.In a l.
  Proof.
  intros.
  induction l.
  cbn in H.
  destruct H.
  cbn in *.
  case_eq l.
  + intros. 
    rewrite H0 in H.
    left.
    trivial.
  + intros.
    subst.
    right.
    apply IHl.
    trivial.
  Qed.

Lemma a_endmax_list_inv :
  forall a l, Ordered_list (a :: l) /\ endmax_list a (a :: l) ->  l = [].
  Proof.
  intros a l [Hord Hlen].
  apply sortedone_to_sorted in Hord.
  apply Sorted_extends in Hord.
  + rewrite List.Forall_forall in Hord.
    cbn in Hlen.
    case_eq l;trivial.
    intros.
    subst.
    apply end_in_list in Hlen.
    generalize (Hord a).
    intros.
    apply H in Hlen.
    omega.
  + unfold Relations_1.Transitive.
    apply lt_trans.
  Qed.

Lemma a_endmax_nth :
  forall a l , length l > 0 -> 
    endmax_list (a - 1) l <-> forall d, List.nth (length l - 1) l d = (a - 1).
  Proof.
  intros;split.
(*   intros. *)
  + induction l;intros.
    - subst.
      cbn in *.
      omega.
    - case_eq l; intros.
      * subst.
        cbn in H0.
        auto.
      * subst.
        apply a_endmin_list in H0.
        2 : { cbn; omega.
        }
        pose proof List.app_nth2.
        generalize (H1 nat [a0] (n :: l0) d (length (a0 :: n :: l0) -1));intros.
        replace (a0 :: n :: l0) with ([a0] ++ (n :: l0)) at 2.
        assert (length (a0 :: n :: l0) - 1 - length [a0] = length (n :: l0) - 1).
        cbn;auto.
        rewrite H3 in H2.
        rewrite H2.
        apply IHl;auto.
        cbn; omega.
        cbn; omega.
        cbn; auto.
  + induction l;intros.
    - subst.
      cbn in *.
      omega.
    - admit.
  Admitted.
(*   Qed. *)

Open Scope list_scope.

(* Open Scope nat_scope. *)

Lemma foreach_rule_plus (P : nat -> St -> Prop) (body : nat -> State () ):
  forall (l: list nat) (min max : nat), min < max -> 
  (forall (it : nat), {{fun s => P it s /\ (min <= it < max)}} body it {{fun _ => P (S it)}})
  -> Ordered_list l -> (startmin_list min l) /\ (endmax_list (max - 1) l) 
     ->
    {{P min}} foreach3' l (fun it0 => loopeT_liftT (body it0)) {{fun _ => P max}} .
    Proof.
    intros l.
    induction l; intros min max Hminmax Hit Hord [Hsmin Hsmax].
    + unfold startmin_list in Hsmin.
      contradict Hsmin.
    + assert (Hamin : a = min).
      apply a_startmin_list in Hsmin.
      auto.
      unfold M.foreach3'.
      eapply sequence_rule.
      - unfold runLoopeT.
        unfold loopeT_liftT.
        unfold liftM.
        cbn.
        eapply sequence_rule. 
        * intros st H2.
          generalize (Hit a).
          intros Ha.
          eapply Ha;split; try rewrite Hamin; auto.
        * intros [].
          apply act_ret.
      - intros.
        rewrite Hamin in *.
        case_eq (S min <? max); intros.
        * rewrite Nat.ltb_lt in H.
          assert (length l > 0).
           apply Sorted_list_no_empty with min max;auto.
          assert (startmin_list (S min) l).
          apply nextmin_ord_list; auto. 
          apply a_endmin_list in Hsmax; auto.
(*           case_eq (S min <? (max - 1)).
          2 : {
            intros.
            rewrite Nat.ltb_nlt in H0.
            assert (S min = max - 1) by omega.
            cbn in H1. *)
           apply IHl.
          ++ omega.
          ++ intro.
             apply weaken with (fun s : St => P it s /\ min <= it < max).
             apply Hit.
             intros s [Hb Hc];split; auto; try omega.
          ++ apply Sorted_inv with min; auto.
          ++ split; auto.
        * rewrite Nat.ltb_nlt in H.
          assert (min = max - 1) by omega.
          rewrite <- H0 in Hsmax.
          assert (S min = max) by omega.
          rewrite H1.
          assert (l = []).
          apply a_endmax_list_inv with min;auto.
          rewrite H2.
          intros s Hs.
          auto.
Qed.

Lemma seq_min :
  forall min max, min < max -> 
   startmin_list min (List.seq min (max - min)).
   Proof.
   intros.
(*    assert ((max - min) > 0) by omega. *)
   case_eq (max - min).
   + intros.
     omega.
   + intros.
     cbn.
     trivial.
   Qed.

(* Compute List.seq 0 (5 - 0). *)

Open Scope nat.

Lemma seq_max :
  forall min max, min < max -> 
   endmax_list (max - 1) (List.seq min (max - min)).
   Proof.
   intros.
   case_eq (max - min).
   + intros. 
     omega.
   + intros.
     pose proof List.seq_nth.
     pose proof List.seq_length.
     generalize (H2 (S n) min).
     intros.
     rewrite a_endmax_nth; try omega.
     rewrite H3.
     assert (max - 1 = min + (S n - 1)) by omega.
     rewrite H4. 
     generalize (H1 (S n) min (S n - 1)).
     intros.
     apply H5.
     omega.
Qed.

Lemma seq_ord :
  forall min max,
    Ordered_list (List.seq min (max - min)).
  Proof.
  intros min max.
  revert min.
  induction max.
  + intros.
    cbn.
    constructor.
  + intros.
    case_eq (max - min).
    - intros.
      assert (S max - min = 0 \/ S max - min = 1) by omega.
      destruct H0; rewrite H0; cbn; repeat constructor.
    - intros.
      assert (S max - min = S (S n)) by omega.
      rewrite H0.
      replace (List.seq min (S (S n))) with (min :: List.seq (S min) (S n)).
      2 : { cbn;auto.
          }
      constructor.
      * rewrite <- H.
        assert (forall len start, Ordered_list (List.seq (start) len) -> Ordered_list (List.seq (S start) len)).
        ++ intros len.
           induction len;intros.
           -- cbn;auto.
           -- inversion H1.
              cbn.
              constructor.
              apply IHlen.
              apply H4.
              case_eq (len);intros;cbn;auto.
              constructor.
              unfold is_succ.
              reflexivity.
        ++ apply H1.
           apply IHmax.
      * assert (is_succ min (S min)).
        unfold is_succ.
        auto.
        eapply HdSel_forall_l in H1.
        cbn.
        eapply H1.
  Qed.
(* 
Lemma foreach_rule_plus2 (P : nat -> St -> Prop) (body : nat -> State () ):
  forall (min max : nat) (l: list nat) , 
  (forall (it : nat), {{fun s => P it s /\ (min <= it < max)}} body it {{fun _ => P (S it)}})
  -> length l > 0 -> Ordered_list l -> (startmin_list min l = true) -> (endmax_list max l = true) 
     ->
    {{P min}} foreach3' l (fun it0 => loopeT_liftT (body it0)) {{fun _ => P max}} .
    Proof.
 *)
 
(* Lemma foreach3_rule (min max : Z) (P : Z -> St -> Prop) (body : Z -> State ())
  : (forall (it : Z), 
    {{fun s => P it s /\ (min < it <= max)}} 
      body it 
      {{fun _ => P (it - 1)}}) /\  min <= max ->
    {{P min}} M.foreach3 min max (fun it0 => loopT_liftT (body it0)) {{fun _ => P max}}. *)
