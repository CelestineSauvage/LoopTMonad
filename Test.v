Require Import Program ZArith.

Set Implicit Arguments.

Import Notations.

Local Notation "f ∘ g" := (fun x => f (g x)) (at level 40, left associativity).

(* State Monad *)

Record S : Type:= {
  val : nat
}.

Definition State (A : Type) := S -> A * S.

(* Arguments State [ A ]. *)

(* forall {A}, A -> m A; *)
Definition state_pure A (a : A) : State A := 
  fun s => (a,s).

(* state_bind = 
fun (A : Type) (st_a : State A) (B : Type) (f : A -> State B) (s : S) => let (a, s0) := st_a s in f a s0
     : forall A : Type, State A -> forall B : Type, (A -> State B) -> S -> B * S *)
Definition state_bind (A : Type) (st_a : State A) (B : Type) (f : A -> State B)  : State B :=
  fun s => let (a, s0) := st_a s in f a s0.

(* Definition state_bind A (st_a : State A) B (f : A -> State B) : State B :=
  fun  s => let (a,s) := st_a s in
            f a s. *)

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

Definition HoareTriple_L {A B} (P : Assertion) (m : LoopT A) (Q : B -> Assertion) : Prop :=
  forall (s : S) (next : A -> State B), P s -> let m' := (runLoopT m next) in let (b,s') := m' s in Q b s'.

Notation "{[ P ]} m {[ Q ]}" := (HoareTriple_L P m Q)
  (at level 90, format "'[' '[' {[  P  ]}  ']' '/  ' '[' m ']' '['  {[  Q  ]} ']' ']'") : monad_scope.

Check loopT_liftT.

Lemma foreach_rule (min max : nat) (P : S -> Prop) (body : nat -> LoopT ())
  : forall (it:nat), {[fun s => P s /\ (Nat.le min it) /\ (it < max)]} 
  body it {[fun (_: unit) => P]} -> 
  {{P}} foreach' min max (body) {{fun _ => P}} .
  Proof.
  Admitted.

(* Set Implicit Arguments. *)

(* Section Test. *)

Definition init_val1 := 0.

Definition init_S1 : nat := init_val1.

(* modify = 
fun (S : Type) (f : S -> S) => perf s <- getS (S:=S); putS (f s)
     : forall S : Type, (S -> S) -> State S ()
 *)
Print modify.

Definition add_s (i : nat) : State unit :=
  modify (fun s => {| val := s.(val) + i |}).

Definition count15 : State unit :=
 add_s 1;;
 add_s 2;;
 add_s 3;;
 add_s 4;;
 add_s 5;;
 state_pure tt.

Check (fun (s : S) => s.(val)).

Lemma l_count15 : {{fun s : S => val s = init_S1}} count15 {{fun (_ : unit ) (s : S) => val s = 15}}.
Admitted.

Definition get10 : State nat:= state_pure 10.

Definition count42 : State unit
 := for i = 0 to 3 {{ 
    add_s i ;;
    add_s i ;;
    perf x <- get10;
    add_s x ;;
    add_s i ;;
    add_s i
  }} .

Lemma l_count42 : 
 {{(fun s : S => val s <= 42)}} count42 {{(fun (u : unit ) (s : S) => val s <= 42)}}.
Proof.
unfold count42.
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