Require Import Program Monads.

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

Variable S : Type.

Definition State := M.State S.

Check State.

Definition hoareTripleS {A} (P : S -> Prop) (m : State A) (Q : A -> S -> Prop) : Prop :=
  forall (s : S), P s -> let (a, s') := m s in Q a s'.

Notation "{{ P }} m {{ Q }}" := (hoareTripleS P m Q)
  (at level 90, format "'[' '[' {{  P  }}  ']' '/  ' '[' m ']' '['  {{  Q  }} ']' ']'") : monad_scope.

Lemma ret (A : Type) `{State A} (a : A) (P : A -> S -> Prop) : {{ P a }} return_ a {{ P }}.
Proof.
intros s H; trivial.
Qed.

Lemma bind (A B : Type) (m : State A) (f : A -> State B) (P : S -> Prop)( Q : A -> S -> Prop) (R : B -> S -> Prop) :
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

Definition wp {A : Type} (P : A -> S -> Prop) (m : State A) :=
  fun s => let (a,s') := m s in P a s'.

Lemma wpIsPrecondition {A : Type} (P : A -> S -> Prop) (m : State A) :
  {{ wp P m }} m {{ P }}.
  Proof.
  unfold wp.
  congruence.
  Qed.

Lemma wpIsWeakestPrecondition
  (A : Type) (P : A -> S -> Prop) (Q : S -> Prop) (m : State A) :
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

Lemma put (s : S) (P : unit -> S -> Prop) : {{ fun _ => P tt s }} putS s {{ P }}.
Proof.
intros s0 H;trivial.
Qed.

Lemma get (P : S -> S -> Prop) : {{ fun s => P s s }} @getS S {{ P }}.
Proof.
intros s H; trivial.
Qed.

Lemma sequence_rule (A B : Type) (m : State A) (f : A -> State B) (P : S -> Prop)( Q : A -> S -> Prop) (R : B -> S -> Prop) :
  {{ P }} m {{ Q }} -> (forall a, {{ Q a }} f a {{ R }}) -> {{ P }} perf x <- m ; f x {{ R }}.
Proof.
intros; eapply bind ; eassumption.
Qed.

Lemma weaken (A : Type) (m : State A) (P Q : S -> Prop) (R : A -> S -> Prop) :
  {{ Q }} m {{ R }} -> (forall s, P s -> Q s) -> {{ P }} m {{ R }}.
Proof.
intros H1 H2 s H3.
apply H2 in H3.
apply H1 in H3.
assumption.
Qed.

Lemma modify f (P : () -> S -> Prop) : {{ fun s => P tt (f s) }} modify f {{ P }}.
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

End state_proof.

Notation "{{ P }} m {{ Q }}" := (hoareTripleS P m Q)
  (at level 90, format "'[' '[' {{  P  }}  ']' '/  ' '[' m ']' '['  {{  Q  }} ']' ']'") : monad_scope.
