Require Import Arith.
Require Import List.
Require Import Program.

Module MonadLoop.

Set Implicit Arguments.

Import Notations.
Import Arith.
Import List.

Local Notation "f ∘ g" := (fun x => f (g x)) (at level 40, left associativity).

(* Classe Functor *)
Class Functor (f : Type -> Type) : Type :=
{ fmap         : forall {A B}, (A -> B) -> f A -> f B }. 

(* Lois des Fonctor *)
Class Functor_Correct (f : Type -> Type) `{F : Functor f} :=
{ fmap_id      : forall A, fmap (fun (x:A)=> x) = (fun x => x);
  fmap_compose : forall A B C (g : A -> B) (f : B -> C), 
                 fmap (f ∘ g) = fmap f ∘ fmap g
}.

Class Applicative (f : Type -> Type) `{F : Functor f} : Type :=
{ pure : forall {A}, A -> f A;
  liftA : forall {A B}, f (A -> B) -> f A -> f B
}.

Notation "f <*> a" := (liftA f a) (left associativity, at level 25).

Class Applicative_Correct (f : Type -> Type) `{Applicative f} :=
{ applicative_id : forall A, liftA (pure (fun  (x:A) => x)) = (fun  x => x);
  applicative_composition : forall {A B C} (u : f (B -> C)) (v : f (A -> B)) (w : f A),
    pure (fun  x => fun  y => x ∘ y) <*> u <*> v <*> w = u <*> (v <*> w);
  applicative_homomorphism : forall {A B} (f : A -> B) (x : A),
    pure f <*> pure x = pure (f x);
  applicative_interchange : forall {A B} (u : f (A -> B)) (y : A),
    u <*> pure y = pure (fun x => x y) <*> u
}.

Class Monad (m: Type -> Type) `{M : Applicative m} : Type :=
{ bind: forall {A}, m A -> forall {B}, (A -> m B) -> m B
}.

Definition return_ {m : Type -> Type} `{M : Monad m} {A : Type} : A -> m A := pure.
Notation "a >>= f" := (bind a f) (at level 50, left associativity).

Hint Unfold bind return_ : monad_db.

Class Monad_Correct (m : Type -> Type) `{M : Monad m} := {
  bind_right_unit: forall A (a: m A), a = a >>= return_;
  bind_left_unit: forall A (a: A) B (f: A -> m B),
             f a = return_ a >>= f;
  bind_associativity: forall A (ma: m A) B f C (g: B -> m C),
                 bind ma (fun  x=> f x >>= g) = (ma >>= f) >>= g
}.

Arguments Functor f : assert.
Arguments Functor_Correct f {F}.
Arguments Applicative f [F]. 
Arguments Applicative_Correct f {F} {A} : rename.
Arguments Monad m [F] [M].
Arguments Monad_Correct m [F] [A] [M] : rename.

Section monadic_functions.
 Variable m : Type -> Type. 
 Variable Fu : Functor m.
 Variable AP : Applicative m.
 Variable Mo : Monad m.

 Definition wbind {A: Type} (ma: m A) {B: Type} (mb: m B) :=
 ma >>= fun  _=>mb.

 Definition liftM {A B: Type} (f: A->B) (ma: m A): m B :=
 ma >>= (fun  a => return_ (f a)).

 Definition join {A: Type} (mma: m (m A)): m A :=
 mma >>= (fun  ma => ma).

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

(* Monad Transformer *)
Class MonadTrans (t : (Type -> Type) -> (Type -> Type)) :=
  { liftT : forall {m} `{Monad m} {A}, m A -> t m A }.


Notation "a >> f" := (wbind _ a f) (at level 50, left associativity).
Notation "'do' a <- e ; c" := (e >>= (fun  a => c)) (at level 60, right associativity).

End monadic_functions.

Section monadic_loop.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Axiom Eta: forall A (B: A -> Type) (f: forall a, B a), f = fun  a=>f a.

(* Generalizable All Variables.
(* Unset Implicit Arguments. *) *)
(* Set Maximal Implicit Insertion.
Unset Strict Implicit. *)
(*newtype LoopT c e m a = LoopT
    { runLoopT :: forall r.     -- This universal quantification forces the
                                -- LoopT computation to call one of the
                                -- following continuations.
                  (c -> m r)    -- continue
               -> (e -> m r)    -- exit
               -> (a -> m r)    -- return a value
               -> m r
    } *)

(* pas convaincue *)
(* Variable r : Type. *)



Inductive LoopT m c : Type
  := MkLoopT : (forall {r : Type}, (c -> m r) -> m r) -> LoopT m c.

Arguments MkLoopT {_} {_} _.

Definition runLoopT {m c r} : LoopT m c -> (c -> m r) -> m r :=
  fun loop next =>
    match loop with
    | MkLoopT body => body r next
    end.

Arguments runLoopT {_} {_} {_}.

Check runLoopT.

(* fmap for Loop *)
Definition loopT_fmap {m A B} (f : A -> B) (x : LoopT m A) : LoopT m B :=
  MkLoopT (fun _ cont => runLoopT x (cont ∘ f)).

(* Functor instance *)
Instance loopT_F {m} : Functor (LoopT m) :=
    { fmap := @loopT_fmap m}.

(* Functor proof *)
Instance loopT_Fcorrect {m} : Functor_Correct (LoopT m).
  Proof.
  Admitted.

(* pure for Loop *)
Definition loopT_pure {m A} (a : A) : LoopT m A :=
MkLoopT (fun _ cont => cont a).

(* <*> for Loop *)
Definition loopT_liftA {m A B} (f1 : LoopT m (A -> B)) (f2 : LoopT m A) : LoopT m B :=
  MkLoopT (fun _ cont => 
    let f' := (fun f => runLoopT f2 (cont ∘ f)) in 
    runLoopT f1 f').

(* Applicative instance *)
Instance loopT_A {m} : Applicative (LoopT m) :=
    { pure := @loopT_pure  m
      ; liftA := @loopT_liftA m}.

(* Applicative *)
Instance loopT_Acorrect {m} : Applicative_Correct (LoopT m).
  Proof.
  Admitted.

(* >>= for Loop *)
Definition loopT_bind {m A} (x : LoopT m A) {B} (k : A -> LoopT m B) : LoopT m B :=
  MkLoopT (fun _ cont => 
    let f' := (fun a => runLoopT (k a) cont) in 
    runLoopT x f').

(* Monad instance *)
Instance loopT_M {m} : Monad (LoopT m) :=
  {bind := @loopT_bind m}.

Instance loopT_Mcorrect {m} : Monad_Correct (LoopT m).
  Proof.
  Admitted.

Definition loopT_liftT {m} `{Monad m} {A} (x : m A) : LoopT m A :=
 MkLoopT (fun _ cont => bind x cont). 

Instance LoopT_T  : MonadTrans LoopT := 
{ liftT := @loopT_liftT}.



