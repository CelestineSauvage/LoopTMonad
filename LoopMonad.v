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
(*newtype LoopT c e m a = LoopT
    { runLoopT :: forall r.     -- This universal quantification forces the
                                -- LoopT computation to call one of the
                                -- following continuations.
                  (c -> m r)    -- continue
               -> (e -> m r)    -- exit
               -> (a -> m r)    -- return a value
               -> m r
    } *)

(* Variable R : Type. *)

Inductive list (A : Type) :=| nil : list A| cons : A -> list A -> list A.

Inductive option (A : Type) : Type :=Some : A -> option A | None : option A.

(* Constructeur qui prend une valeur a (a -> m r) et renvoie le résultat dans la monade (m r) *)
Inductive LoopT (m : Type -> Type) (A : Type) := 
|C_LoopT : (forall R, (A -> m R) -> m R) -> LoopT m A.
Check LoopT.
Check C_LoopT.

Variable R : Type.

(* Il y a souvent une fonction runX pour une monade X. par exemple, pour State, runState :: State s a -> s -> (a, s)
Tu lui donnes une _action_ (une valeur monadique), les arguments nécessaires (l’état initial pour une monade d’état) et ça « déclenche » le calcul
Bref, pour une boucle, on va vouloir effectuer la boucle et obtenir le résultat dans la monade sous-jacente (celle d’état de Pip), par exemple *)
Definition runLoopT A m (op : LoopT m A) (next : A -> m R) : m R := 
match op with 
| C_LoopT  p => loop next
end.
Check runLoopT.

Generalizable Variables A B C.

Definition loop_fmap {m} `{Monad m}  {A B} (f : A -> B) (x : LoopT m A) : LoopT m B :=
CLoopT (fun cont => runLoop (cont ∘ f)).


(* Definition loop_pure {A} (x : A) : LoopT m A := *)

(* Definition loop_liftA {A B} (loop_f : LoopT m (A -> B)) (loop_a : LoopT m A) := *)

(* Definition loop_bind {A B} (loop_A : LoopT m A) (f : A -> LoopT m B) := *)

(* Definition loop

Definition 

Check LoopT.



(* Definition loopA_pure {A} (a : A) : LoopT A :=
(fun _ _ cont => LoopT _ _ (cont a)). *)


(* Instance loopT_pure {f} : `{Applicative f}
                    {A} : (a : A) : LoopT f A := @pure f _ _ _ (pure a). *)


Instance Loop_F : Functor option := { fmap := @option_fmap}.
