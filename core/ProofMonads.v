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

Inductive HdSel (a : nat) : list nat -> Prop :=
  | HdSel_nil : HdSel a [S a]
  | HdSel_cons b l: is_succ a b -> HdSel a (b :: l).

Inductive ordered_list : list nat -> Prop :=
    | ordered_list_one a : ordered_list [a]
    | ordered_list_cons a l : ordered_list l -> HdSel a l -> ordered_list (a :: l).

Definition startmin_list (min: nat) (l : list nat) : Prop :=
  match l with 
    | [] => False
    | a :: l' => (a = min)
  end.

Fixpoint endmax_list (max : nat) (l : list nat) : Prop :=
   match l with 
    | [] => False
    | a :: [] => True
    | a :: l' => endmax_list max l'
  end.

Lemma nextmin_ord_list (min : nat):
  forall l, (length l) > 0 /\ ordered_list (min :: l) -> startmin_list (S min) l.
  Proof.
  induction min.
  intros l [Hlen Hord].
  + assert (forall l',  HdSel 0 (1 :: l')).
    - constructor.
      unfold is_succ.
      omega.
    -

Lemma ordered_noempty (l : list nat) :
  ordered_list l -> length l > 0.
  Proof.
  intros.
  induction H.
  + constructor.
  + cbn.
    auto.
  Qed.

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
  forall (a : nat), length l > 0 /\ endmax_list max (a :: l) -> endmax_list max l.
  Proof.
  intros a [H1 H2].
  induction l.
  + cbn in H1.
    intuition.
  + cbn.
    auto.
  Qed.

(* Definition prop_startmin_list (min : nat) (l : list nat) : Prop :=
   match l with 
    | [] => False
    | a :: l' => if (a =? min) then True else False
  end.
 *)

(* Fixpoint prop_endmax_list (max : nat) (l : list nat) : Prop :=
   match l with 
    | [] => False
    | a :: [] => True
    | a :: l' => prop_endmax_list max l'
  end. *)
Close Scope list_scope.

Open Scope nat_scope.

Lemma foreach_rule_plus (P : nat -> St -> Prop) (body : nat -> State () ):
  forall (l: list nat) (min max : nat), min < max -> 
  (forall (it : nat), {{fun s => P it s /\ (min <= it < max)}} body it {{fun _ => P (S it)}})
  -> ordered_list l -> (startmin_list min l) /\ (endmax_list (max - 1) l) 
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
          ++  
             assert (startmin_list (S min) l) by admit.
          -- eapply a_ord_list.
            apply Hord.
          ++ split.
             assert (startmin_list (S a) l = true).
               admit.
               assert (length l > 0).
               apply startmin_noempty with (S a).
               auto.
               cbn.
        * rewrite Nat.ltb_nlt in H.
          assert (S min = max) by omega.
          rewrite H0.
          assert (l = nil) by admit.
          rewrite H1.
          intros s Hs.
          auto.
Qed.

Lemma foreach_rule_plus2 (P : nat -> St -> Prop) (body : nat -> State () ):
  forall (min max : nat) (l: list nat) , 
  (forall (it : nat), {{fun s => P it s /\ (min <= it < max)}} body it {{fun _ => P (S it)}})
  -> length l > 0 -> ordered_list l -> (startmin_list min l = true) -> (endmax_list max l = true) 
     ->
    {{P min}} foreach3' l (fun it0 => loopeT_liftT (body it0)) {{fun _ => P max}} .
    Proof.

 
(* Lemma foreach3_rule (min max : Z) (P : Z -> St -> Prop) (body : Z -> State ())
  : (forall (it : Z), 
    {{fun s => P it s /\ (min < it <= max)}} 
      body it 
      {{fun _ => P (it - 1)}}) /\  min <= max ->
    {{P min}} M.foreach3 min max (fun it0 => loopT_liftT (body it0)) {{fun _ => P max}}. *)
