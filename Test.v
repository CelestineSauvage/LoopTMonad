Require Import Program ZArith.

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

(* End state_monad.

Section loop_monad. *)

Definition LoopT a : Type := (forall (r : Type), (a -> State r) -> State r).

Definition runLoopT {a r} (loop : LoopT a) (next : a -> State r) :  State r :=
  loop r next.
(* next : (a -> LoopT r) *)

(* Arguments runLoopT {_} {_} {_} {_}. *)

Definition loopT_pure {A} (a : A) : LoopT A :=
  fun _ next => next a.

(* >>= for Loop *)
Definition loopT_bind {A} (x : LoopT A) {B} (k : A -> LoopT B) : LoopT B :=
  (fun _ next =>
    let f' := (fun a => runLoopT (k a) next) in
    runLoopT x f').

(* Variable m : Type -> Type. *)
(* Variable e: Type. *)

(* forall {A}, m A -> t m A; *)

Definition loopT_liftT {A} (x : State A) : LoopT A :=
(fun _ cont => state_bind x cont).

(* Variable S : Type.

Definition stepLoopT {e a}  (body : LoopT e (State S) a) (next : a -> (State S) e) : (State S) e :=
  runLoopT body (return_) next. *)

Definition stepLoopT {a} (body : LoopT a) (next : a -> State ()) : State () :=
  runLoopT body next.

(* exit = 
fun (m : Type -> Type) (a : Type) (_ : Monad m) (r : Type) (fin : () -> m r)
  (_ : a -> m r) => fin tt
     : forall (m : Type -> Type) (a : Type), Monad m -> LoopT () m a *)
(* 
Definition exit {a}: LoopT () a :=
  fun _ fin _ => fin tt. *)

Import List.

Definition foreach''{v} (values : list v) {a} (body : v -> LoopT a) : State () :=
  fold_right
    (fun x next => stepLoopT (body x) (fun _ => next))
    (state_pure tt)
    values.

Definition foreach'(min max : nat) (body : nat -> LoopT ()) : State () :=
  foreach'' (seq min (max-min)) body.

Notation "'for' i '=' min 'to' max '{{' body }}" := (foreach' min max (fun i => (loopT_liftT body))) (at level 60, i ident, min at level 60,
max at level 60, body at level 60, right associativity) : monad_scope.

(* Definition LoopT a : Type := (forall (r : Type), (a -> State r) -> State r). *)

(* Definition hoareTripleS {A} (P : S -> Prop) (m : State A) (Q : A -> S -> Prop) : Prop :=
  forall (s : S), P s -> let (a, s') := m s in Q a s'. *)

(* Au dessus de ma fonction foreach *)

Definition hoareTripleL {A B} (P : Assertion) (m : LoopT A) (Q : B -> Assertion) : Prop := 
  forall (s : S) (next : A -> State B), P s -> let m' := (runLoopT m next) in let (b,s') := m' s in Q b s'.

(* Lie une monade d'état à sa monade loop associée *)
(* Inductive match_monad {A} : LoopT A -> State A -> Prop :=
  |mklift : forall (mL : LoopT A) (mS : State A), loopT_liftT mS = mL -> match_monad mL mS.

Lemma match_monad_spec {A} (mL : LoopT A) (mS : State A): 
  loopT_liftT mS = mL -> match_monad mL mS.
  Proof.
  constructor.
  assumption.
  Qed. *)

(* Inductive foreach_L {A B} (P : Assertion) (m : LoopT A) (Q : B -> Assertion) : Prop :=
  | For_E :
  | For_N : forall A', HoareTriple_L P m Q ->  foreach_L P m Q -> foreach_L *)

Notation "{[ P ]} m {[ Q ]}" := (hoareTripleL P m Q)
  (at level 90, format "'[' '[' {[  P  ]}  ']' '/  ' '[' m ']' '['  {[  Q  ]} ']' ']'") : monad_scope.

Lemma foreach_rule (min max : nat) (P : S -> Prop) (m : nat -> State ())
  : forall (it:nat), {{fun s => P s /\ (Nat.le min it) /\ (it < max)}} m it {{fun _ => P}}
    -> {{P}} foreach' min max (fun it => loopT_liftT (m it)) {{fun _ => P}}.
  Proof.
  Admitted.

Definition init_state : S := {|r := 1|}.

Definition add_s (i : nat) : State unit :=
  modify (fun s => {| r := s.(r) + i |}).

Definition mul_s (i : nat) : State unit :=
  modify (fun s => {| r := s.(r) * i |}).

Definition fac5 : State unit :=
  for i = 1 to 6 {{
    mul_s i
  }}.

Definition slow_add : State unit :=
  for i = 0 to 6 {{
    add_s 1
  }}.

Compute runState slow_add init_state.

Lemma l_slow_add : 
 {{(fun s : S => r s = 1)}} slow_add {{(fun (_ : unit ) (s : S) => r s = 7)}}.
Proof.
eapply strengthen.
eapply foreach_rule.
+ eapply weaken.
  - 
Admitted.

Compute runState fac5 init_state.

Lemma l_fac5 : 
 {{(fun s : S => r s = 1)}} fac5 {{(fun (_ : unit ) (s : S) => r s = 120)}}.
Proof.
eapply strengthen.
eapply foreach_rule.
+ intros.
  
  - eapply weaken.
unfold l.
intros s H.
eapply foreach_rule.

+ admit.
+ admit.

(* Lemma l_add_s :
 forall (n i : nat), {{fun (s : S) => val s = n}} add_s i {{fun (_ : unit) (s : S) => val s = (n + i)}}.
  Proof.
  intros n i s H.
  unfold add_s.
  apply l_modify.
  auto.
  Qed. *)