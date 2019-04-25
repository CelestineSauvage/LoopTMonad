Require Import Program.

Module Monad.

Set Implicit Arguments.

Import Notations.

Local Notation "f ∘ g" := (fun x => f (g x)) (at level 40, left associativity).

Class Monad (m: Type -> Type) :=
{ return_ : forall {A}, A -> m A;
  bind: forall {A}, m A -> forall {B}, (A -> m B) -> m B;
  bind_right_unit: forall A (a: m A), a = bind a return_;
  bind_left_unit: forall A (a: A) B (f: A -> m B),
             f a = bind (return_ a) f;
  bind_associativity: forall A (ma: m A) B f C (g: B -> m C),
                 bind ma (fun  x=> bind (f x) g) = bind (bind ma f) g
}.

Notation "a >>= f" := (bind a f) (at level 50, left associativity).

Hint Unfold bind return_ : monad_db.

(* Monad Transformer *)
Class MonadTrans {m} `{Monad m} (t : (Type -> Type) -> (Type -> Type)) `{Monad (t m)}  := {
  liftT : forall {A}, m A -> t m A;
  lifT_id : forall {A : Type} (a : A), (liftT ∘ return_) a = return_ a;
  lifT_bind : forall A B (ma : m A) (k : A -> m B), liftT (ma >>= k) = (liftT ma) >>= (liftT ∘ k)
}.

Arguments Monad m : assert.

Section monadic_functions.
 Variable m : Type -> Type.
 Context `{Monad m}.

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

(* Ltac simplify_monad_LHS :=
  repeat match goal with
  | [ |- bind (return_ _) _ = _ ] => rewrite <- bind_left_unit
  | [ |- bind (bind _ _) _ = _ ]  => rewrite <- bind_associativity
  | [ |- _ = _ ]                  => reflexivity
  | [ |- bind ?a ?f = _ ]         => erewrite bind_eq; intros; 
                                     [ | simplify_monad_LHS | simplify_monad_LHS ]
  end.

Ltac simplify_monad :=
  simplify_monad_LHS;
  apply eq_sym;
  simplify_monad_LHS;
  apply eq_sym.

Ltac simpl_m :=
  repeat (try match goal with
  [ |- bind ?a _ = bind ?a _ ] => apply bind_eq; [ reflexivity | intros ]
  end; simplify_monad).
 *)

Notation "a >> f" := (wbind _ a f) (at level 50, left associativity).
Notation "'perf' a <- e ; c" := (e >>= (fun  a => c)) (at level 60, right associativity).

End monadic_functions.

Section monadic_loop.

Definition LoopT m a : Type := (forall (r : Type), (a -> m r) -> m r).

Definition runLoopT {m c r} : LoopT m c -> (c -> m r) -> m r :=
  fun loop next => loop r next.

Arguments runLoopT {_} {_} {_}.

(* pure for Loop *)
Definition loopT_pure {m A} (a : A) : LoopT m A :=
(fun _ cont => cont a).

(* >>= for Loop *)
Definition loopT_bind {m A} (x : LoopT m A) {B} (k : A -> LoopT m B) : LoopT m B :=
  (fun _ cont =>
    let f' := (fun a => runLoopT (k a) cont) in
    runLoopT x f').

(* Monad instance *)
Global Program Instance loopT_M {m} : Monad (LoopT m) :=
  { return_ := @loopT_pure m;
    bind := @loopT_bind m}.

Variable m : Type -> Type.
Context `{Monad m}.

Definition loopT_liftT {A} (x : m A) : LoopT m A :=
(fun _ cont => x >>= cont).

Global Program Instance LoopT_T  : MonadTrans LoopT :=
{ liftT := @loopT_liftT}.
  Next Obligation.
  intros;simpl.
  unfold loopT_liftT.
  unfold loopT_pure.
  extensionality r.
  extensionality cont.
  rewrite <- bind_left_unit.
  reflexivity.
  Qed.
  Next Obligation.
  
  Admitted.

Import List.

Definition stepLoopT {m} `{Monad m} {c} (body : LoopT m c) {r} (next : c -> m r) : m r :=
  runLoopT body next.

(* Boucle qui prend une liste en paramètres et applique le corps de boucle pour chaque élement de la liste *)
Definition foreach'' {m} `{Monad m} {a} (values : list a) {c} (body : a -> LoopT m c) : m unit :=
  fold_right
    (fun x next => stepLoopT (body x) (fun _ => next))
    (return_ tt)
    values.

(* Boucle avec un min et max qui appelle foreach' *)
Definition foreach' {m} `{Monad m} (min max : nat) {c} (body : nat -> LoopT m c) : m unit :=
  foreach'' (seq min (max-min)) body.

(* Fonction qui appelle une fois le corps de la boucle *)
Definition once {m} `{Monad m} {c} (body : LoopT m c) : m unit :=
stepLoopT body (fun _ => return_ tt).

Record S := {
  mylist : list nat
}.

Definition State (A : Type) := S -> A * S.

(* Arguments State [S]. *)

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

Program Instance stateM : Monad (State) :=
    { return_ := fun A a s=> (a,s);
      bind := @state_bind}.
  Next Obligation.
  Proof.
  intros.
  unfold state_bind.
  apply functional_extensionality.
  intros.
  destruct (a x).
  reflexivity.
  Qed.
  
  Next Obligation.
  intros.
  unfold state_bind.
  apply functional_extensionality.
  intros.
  destruct (ma x).
  reflexivity.
  Qed.


Definition modify (f : S -> S) : State unit :=
  get >>= (fun s => put (f s)).

Definition addElement (val : nat) : State unit :=
  modify (fun s => {| mylist := val :: s.(mylist)|}).

End monadic_loop.

Open Scope list_scope.

Notation "'foreach' i '=' min 'to' max '{{' body }}" := (foreach' min max (fun i => (loopT_liftT body))) (at level 60, i ident, min at level 60,
max at level 60, body at level 60, right associativity).

Definition nth := 4.

Definition init_S := {| mylist := [] |}.

Compute runState (foreach i = 0 to nth {{ foreach j = 0 to nth {{addElement (i+j) }} }} ) init_S.
