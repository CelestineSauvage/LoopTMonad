Require Import Program.

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

Notation "a >>= f" := (bind a f) (at level 50, left associativity) : monad_scope.

Open Scope monad_scope.

(* Hint Unfold bind return_ : monad_db. *)

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

(* Ltac cbnify_monad_LHS :=
  repeat match goal with
  | [ |- bind (return_ _) _ = _ ] => rewrite <- bind_left_unit
  | [ |- bind (bind _ _) _ = _ ]  => rewrite <- bind_associativity
  | [ |- _ = _ ]                  => reflexivity
  | [ |- bind ?a ?f = _ ]         => erewrite bind_eq; intros; 
                                     [ | cbnify_monad_LHS | cbnify_monad_LHS ]
  end.

Ltac cbnify_monad :=
  cbnify_monad_LHS;
  apply eq_sym;
  cbnify_monad_LHS;
  apply eq_sym.

Ltac cbn_m :=
  repeat (try match goal with
  [ |- bind ?a _ = bind ?a _ ] => apply bind_eq; [ reflexivity | intros ]
  end; cbnify_monad). *)


(* Notation "a ;; f" := (wbind _ a f) (at level 60, right associativity) : monad_scope.
Notation "'perf' a <- e ; c" := (e >>= (fun  a => c)) (at level 60, right associativity) : monad_scope. *)

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
  intros;cbn.
  unfold loopT_liftT.
  unfold loopT_pure.
  extensionality r.
  extensionality cont.
  rewrite <- bind_left_unit.
  reflexivity.
  Qed.
  
  Next Obligation.
  intros;cbn.
  unfold loopT_liftT.
  unfold loopT_bind.
  unfold runLoopT.
  extensionality r.
  extensionality cont.
  rewrite bind_associativity.
  reflexivity.
  Qed.

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

(* Notation "'foreach i '=' min 'to' max '{{' body }}" := (foreach' min max (fun i => (body))) (at level 60, i ident, min at level 60, 
max at level 60, body at level 60, right associativity) : monad_scope. *)

(* Fonction qui appelle une fois le corps de la boucle *)
Definition once {m} `{Monad m} {c} (body : LoopT m c) : m unit :=
stepLoopT body (fun _ => return_ tt).

End monadic_loop.

Section monadic_state.

Variable S : Type.

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

Global Program Instance stateM : Monad (State) :=
    { return_ := fun A a s=> (a,s);
      bind := @state_bind}.
  Next Obligation.
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

End monadic_state.

Notation "m1 ;; m2" := (bind m1 (fun _ => m2))  (at level 60, right associativity) : monad_scope.
Notation "'perf' x '<-' m ';' e" := (bind m (fun x => e))
  (at level 60, x ident, m at level 200, e at level 60) : monad_scope.
Notation "'for' i '=' min 'to' max '{{' body }}" := (foreach' min max (fun i => (loopT_liftT body))) (at level 60, i ident, min at level 60,
max at level 60, body at level 60, right associativity) : monad_scope.