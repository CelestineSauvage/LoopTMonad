Set Implicit Arguments.

Require Import Program.

Module Monad.
(** * The Monad Type Class *)
Class Monad (m: Type -> Type): Type :=
{ return_: forall A, A -> m A;
  bind: forall A, m A -> forall B, (A -> m B) -> m B;
  right_unit: forall A (a: m A), a = bind a (@return_ A);
  left_unit: forall A (a: A) B (f: A -> m B),
             f a = bind (return_ a) f;
  associativity: forall A (ma: m A) B f C (g: B -> m C),
                 bind ma (fun x => bind (f x) g) = bind (bind ma f) g
}.
Notation "a >>= f" := (bind a _ f) (at level 50, left associativity).
Section monadic_functions.
 Variable m: Type -> Type.
 Variable M: Monad m.
 Definition wbind {A: Type} (ma: m A) {B: Type} (mb: m B) :=
 ma >>= fun _ =>mb.
 Definition liftM {A B: Type} (f: A->B) (ma: m A): m B :=
 ma >>= (fun  a => return_ (f a)).
 Definition join {A: Type} (mma: m (m A)): m A :=
 mma >>= (fun  ma => ma).
End monadic_functions.
Notation "a >> f" := (wbind _ a f) (at level 50, left associativity).
Notation "'do' a <- e ; c" := (e >>= (fun  a => c)) (at level 60, right associativity).

Class MonadTrans (t : (Type -> Type) -> (Type -> Type)) :=
  { liftT : forall {m} `{Monad m} {A}, m A -> t m A }.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive LoopT m c : Type
  := MkLoopT : (forall (r : Type), (c -> m r) -> m r) -> LoopT m c.

Arguments MkLoopT {_} {_} _.

Definition runLoopT {m c r} : LoopT m c -> (c -> m r) -> m r :=
  fun loop next =>
    match loop with
    | MkLoopT body => body r next
    end.

Arguments runLoopT {_} {_} {_}.

Definition loopT_return_ m A (a : A) : LoopT m A :=
MkLoopT (fun _ cont => cont a).

Definition loopT_bind {m A} (x : LoopT m A) {B} (k : A -> LoopT m B) : LoopT m B :=
  MkLoopT (fun _ cont => 
    let f' := (fun a => runLoopT (k a) cont) in 
    runLoopT x f').

(* Axiom Ext: forall A (B: A->Type) (f g: forall a, B a), (forall a, f a = g a) -> f = g. *)
(* Axiom Eta: forall A (B: A -> Type) (f: forall a, B a), f = fun a => f a. *)

Instance loopT_M {m} : Monad (LoopT m) :=
  {|return_ := @loopT_return_ m;
    bind := @loopT_bind m|}.
(* unit_right *)
Admitted.
  

Definition loopT_liftT {m} `{Monad m} {A} (x : m A) : LoopT m A :=
 MkLoopT (fun _ cont => x >>= cont). 

Instance LoopT_T  : MonadTrans LoopT := 
{ liftT := @loopT_liftT}.

Definition stepLoopT {m} `{Monad m} {c} (body : LoopT m c) {r} (next : c -> m r) : m r :=
  runLoopT body next.

Import List.

Definition foreach' {m} `{Monad m} {a} (values : list a) {c} (body : a -> LoopT m c) : m unit :=
  fold_right
    (fun x next => stepLoopT (body x) (fun _ => next))
    (return_ tt)
    values.

(* Boucle avec un min et max qui appelle foreach' *)
Definition foreach {m} `{Monad m} (min max : nat) {c} (body : nat -> LoopT m c) : m unit :=
  foreach' (seq min (max-min)) body.

Record S := {
  myval : nat
}.

Definition State (A : Type) := S -> A * S.

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

Instance stateM : Monad (State) :=
    {|return_ := fun A a s=> (a,s) ;
      bind := @state_bind|}.
Admitted.

Definition modify (f : S -> S) : State unit :=
  get >>= (fun s => put (f s)).

Definition init_val := 0.

Definition init_S := {| myval := init_val|}.

Definition changeState (i : nat) : State unit :=
  modify (fun s => {| myval := s.(myval) + i |}).

Check runState (foreach 0 5 (fun i => (liftT (changeState i)))) init_S.

Compute runState (foreach 0 5 (fun i => (liftT (changeState i)))) init_S.

