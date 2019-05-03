Require Import Program.

Set Implicit Arguments.

Import Notations.

Local Notation "f ∘ g" := (fun x => f (g x)) (at level 40, left associativity).

(* State Monad *)

Section monads.

Variable S : Type.

Definition State (A : Type) := S -> A * S.

(* Arguments State [ A ]. *)

(* forall {A}, A -> m A; *)
Definition state_pure A (a : A) : State A := 
  fun s => (a,s).

Definition state_bind A (st_a : State A) B  (f : A -> State B) :=
  fun  s => let (a,s) := st_a s in
            f a s.

Definition put (x : S) : State unit :=
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

Definition hoareTripleS {A} (P : S -> Prop) (m : State A) (Q : A -> S -> Prop) : Prop :=
  forall (s : S), P s -> let (a, s') := m s in Q a s'.

Notation "{{ P }} m {{ Q }}" := (hoareTripleS P m Q)
  (at level 90, format "'[' '[' {{  P  }}  ']' '/  ' '[' m ']' '['  {{  Q  }} ']' ']'") : monad_scope.

Lemma conjProp (A : Type ) (P R : S -> Prop) (Q : A -> S -> Prop) m :
  {{ P }} m {{ Q}} -> {{R}} m {{fun _ => R}} -> {{fun s => P s/\ R s}} m {{fun a s => Q a s/\ R s}}.
  Proof.
  intros H1 H2 s [H3 H4].
  apply H1 in H3.
  apply H2 in H4.
  destruct (m s).
  tauto.
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
  extensionality s; unfold state_bind; case (m s); trivial; tauto.
  Qed.


Definition modify (f : S -> S) : State unit :=
  perf s <- get ; put (f s).

(* End state_monad.

Section loop_monad. *)

Definition LoopT a : Type := (forall (r : Type), (a -> State r) -> State r).

Definition runLoopT {a r} (loop : LoopT a) : (a -> State r) -> State r :=
  fun next => loop r next.

(* Arguments runLoopT {_} {_} {_} {_}. *)

Definition loopT_pure {A} (a : A) : LoopT A :=
  fun _ cont => cont a.

(* >>= for Loop *)
Definition loopT_bind {A} (x : LoopT A) {B} (k : A -> LoopT B) : LoopT B :=
  (fun _ cont =>
    let f' := (fun a => runLoopT (k a) cont) in
    runLoopT x f').

(* Variable m : Type -> Type. *)
(* Variable e: Type. *)

(* forall {A}, m A -> t m A; *)

Definition loopT_liftT {A} (x : State A) : LoopT A :=
(fun _ cont => state_bind x cont).

(* Variable S : Type.

Definition stepLoopT {e a}  (body : LoopT e (State S) a) (next : a -> (State S) e) : (State S) e :=
  runLoopT body (return_) next. *)

Definition stepLoopT {a} (body : LoopT a) (next : a -> State unit) : State unit :=
  runLoopT body next.

(* exit = 
fun (m : Type -> Type) (a : Type) (_ : Monad m) (r : Type) (fin : () -> m r)
  (_ : a -> m r) => fin tt
     : forall (m : Type -> Type) (a : Type), Monad m -> LoopT () m a *)
(* 
Definition exit {a}: LoopT unit a :=
  fun _ fin _ => fin tt. *)

Import List.

Definition foreach''{a} (values : list a) {c} (body : a -> LoopT c) : State unit :=
  fold_right
    (fun x next => stepLoopT (body x) (fun _ => next))
    (state_pure tt)
    values.

Definition foreach'(min max : nat) {a} (body : nat -> LoopT a) : State unit :=
  foreach'' (seq min (max-min)) body.

Notation "'for' i '=' min 'to' max '{{' body }}" := (foreach' min max (fun i => (loopT_liftT body))) (at level 60, i ident, min at level 60,
max at level 60, body at level 60, right associativity) : monad_scope.

Definition HoareTriple_L {A} (P : S -> Prop) (m : LoopT A) (B : A -> S -> Prop) : Prop :=
  forall (s : S), P s -> fun a let (a, s') := m in Q a s'.

End monads.

Set Implicit Arguments.

Section Test.

Definition init_val1 := 0.

Definition init_S1 : nat := init_val1.

(* modify = 
fun (S : Type) (f : S -> S) => getS (S:=S) >>= putS (S:=S) ∘ f
     : forall S : Type, (S -> S) -> State S () *)

Definition add_s (i : nat) : State nat unit :=
  modify (fun s => s + i).
