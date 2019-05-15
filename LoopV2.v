Require Import Program List ZArith.

Set Implicit Arguments.

Import Notations.

Local Notation "f ∘ g" := (fun x => f (g x)) (at level 40, left associativity).

(* State Monad *)

Record S : Type:= {
  r : nat
}.

Definition State (A : Type) := S -> A * S.

(* Arguments State [ A ]. *)

(* forall {A}, A -> m A; *)
Definition state_pure A (a : A) : State A := 
  fun s => (a,s).

(* state_bind = 
fun (A : Type) (st_a : State A) (B : Type) (f : A -> State B) (s : S) => let (a, s0) := st_a s in f a s0
     : forall A : Type, State A -> forall B : Type, (A -> State B) -> S -> B * S *)
Definition state_bind {A B} (st_a : State A) (f : A -> State B)  : State B :=
  fun s => let (a, s0) := st_a s in f a s0.


(*    bind: forall {A}, m A -> forall {B}, (A -> m B) -> m B;
  bind_right_unit: forall A (a: m A), a = bind a return_;
  bind_left_unit: forall A (a: A) B (f: A -> m B),
             f a = bind (return_ a) f;
  bind_associativity: forall A (ma: m A) B f C (g: B -> m C),
                 bind ma (fun  x=> bind (f x) g) = bind (bind ma f) g *)
(* Lemma bind_right_unit *)

Lemma state_bind_right_unit : 
  forall (A : Type) (a: State A), a = state_bind a (@ state_pure A).
  Proof.
  intros.
  unfold state_bind.
  apply functional_extensionality.
  intros.
  destruct (a x).
  reflexivity.
  Qed.

Lemma state_bind_left_unit :
   forall A (a: A) B (f: A -> State B),
             f a = state_bind (state_pure a) f.
   Proof.
   auto.
   Qed.

Lemma state_bind_associativity :
  forall A (ma: State A) B f C (g: B -> State C),
                 state_bind ma (fun x => state_bind (f x) g) = state_bind (state_bind ma f) g.
  Proof.
  intros.
  unfold state_bind.
  apply functional_extensionality.
  intros.
  destruct (ma x).
  reflexivity.
  Qed.

Definition put (x : S) : State () :=
  fun _ => (tt,x).

Definition get : State S :=
  fun x => (x,x).

Definition runState  {A} (op : State A) : S -> A * S := op.
Definition evalState {A} (op : State A) : S -> A := fst ∘ op.
Definition execState {A} (op : State A) : S -> S := snd ∘ op.

Notation "m1 ;; m2" := (state_bind m1 (fun _ => m2))  (at level 60, right associativity) : monad_scope.
Notation "'perf' x '<-' m ';' e" := (state_bind m (fun x => e))
  (at level 60, x ident, m at level 200, e at level 60) : monad_scope.

Open Scope monad_scope.

(* modify = 
fun (S : Type) (f : S -> S) => perf s <- getS (S:=S); putS (f s)
     : forall S : Type, (S -> S) -> State S () *)
Definition modify (f : S -> S) : State () :=
  perf s <- get; put (f s).

Definition Assertion := S -> Prop.

Definition hoareTripleS {A} (P : S -> Prop) (m : State A) (Q : A -> S -> Prop) : Prop :=
  forall (s : S), P s -> let (a, s') := m s in Q a s'.

Notation "{{ P }} m {{ Q }}" := (hoareTripleS P m Q)
  (at level 90, format "'[' '[' {{  P  }}  ']' '/  ' '[' m ']' '['  {{  Q  }} ']' ']'") : monad_scope.

Lemma ret  (A : Type) (a : A) (P : A -> Assertion) : {{ P a }} state_pure a {{ P }}.
Proof.
intros s H; trivial.
Qed.

(* Triplet de hoare sur la séquence *)
Lemma bind  (A B : Type) (m : State A) (f : A -> State B) (P : Assertion)( Q : A -> Assertion) (R : B -> Assertion) :
  (forall a, {{ Q a }} f a {{ R }}) -> {{ P }} m {{ Q }} -> {{ P }} perf x <- m ; f x {{ R }}.
Proof. 
intros H1 H2 s H3.
unfold state_bind.
case_eq (m s).
intros.
apply H2 in H3.
case_eq (f a s0).
intros b s'' H5.
Admitted.

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
  extensionality s; unfold state_bind; case (m s); trivial; tauto.
  Qed.

Lemma l_put (s : S) (P : unit -> Assertion) : {{ fun _ => P tt s }} put s {{ P }}.
Proof.
intros s0 H;trivial.
Qed.

Lemma l_get (P : S -> Assertion) : {{ fun s => P s s }} get {{ P }}.
Proof.
intros s H; trivial.
Qed.

Lemma bindRev (A B : Type) (m : State A) (f : A -> State B) (P : Assertion)( Q : A -> Assertion) (R : B -> Assertion) :
  {{ P }} m {{ Q }} -> (forall a, {{ Q a }} f a {{ R }}) -> {{ P }} perf x <- m ; f x {{ R }}.
Proof.
intros; eapply bind ; eassumption.
Qed.

Lemma weaken (A : Type) (m : State A) (P Q : Assertion) (R : A -> Assertion) :
  {{ Q }} m {{ R }} -> (forall s, P s -> Q s) -> {{ P }} m {{ R }}.
Proof.
intros H1 H2 s H3.
apply H2 in H3. 
apply H1 in H3.
assumption. 
Qed.

Lemma strengthen (A : Type) (m : State A) (P: Assertion) (Q R: A -> Assertion) :
  {{ P }} m {{ R }} -> (forall s a, R a s -> Q a s) -> {{ P }} m {{ Q }}.
Proof.
intros H1 H2 s H3.
apply H1 in H3.
Admitted.


Lemma l_modify f (P : () -> Assertion) : {{ fun s => P tt (f s) }} modify f {{ P }}.
Proof.
unfold modify.
eapply bind.
intros.
eapply l_put.
simpl.
eapply weaken.
eapply l_get.
intros. simpl.
assumption.
Qed.

(* Section Continuation. *)

Inductive Action : Type :=
  | Atom : State Action -> Action
  | Stop : Action.

Definition LoopT a : Type := (a -> Action) -> Action.

Definition loopT_pure {A} (a : A) : LoopT A :=
  fun (c : A -> Action) => c a.

Definition loopT_bind {A} (x : LoopT A) {B} (k : A -> LoopT B) : LoopT B :=
  fun (c : B -> Action) => x (fun a => (k a) c).

Definition action {A} (x : LoopT A) : Action :=
  x (fun (_ : A) => Stop).

(* lift *)
Definition atom {A} (x : State A) : LoopT A := 
  fun c => Atom ( perf a <- x ; state_pure (c a)).

Open Scope list_scope.

Fixpoint round (lst : list Action) : State () :=
  match lst with
    | nil => state_pure tt
    | (a::ax) => match a with 
                  | Atom am => am ;; round ax
                  | Stop => round ax
                  end
    end.

Definition run {A} (x : LoopT A) : State () :=
  round [action x].

Definition stop {A} : LoopT A :=
  fun c => Stop.

(* Definition foreach''{v} (values : list v) {a} (body : v -> LoopT a) : State () :=
  fold_right
    (fun x next => stepLoopT (body x) (fun _ => next))
    (state_pure tt)
    values. *)

Definition foreach (values : list nat) {a} (body : nat -> LoopT a) : list Action :=
   match values with
    | nil => 
    | (v : vs) => action 