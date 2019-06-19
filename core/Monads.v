Require Import Program List ZArith Arith Coq.Logic.Classical_Prop.

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

(* Monad Transformer *)
Class MonadTrans {m} `{Monad m} (t : (Type -> Type) -> (Type -> Type)) `{Monad (t m)}  := {
  (* Lift fonction and monade transformers laws *)
  liftT : forall {A}, m A -> t m A;
  lifT_id : forall {A : Type} (a : A), (liftT ∘ return_) a = return_ a;
  lifT_bind : forall A B (ma : m A) (k : A -> m B), liftT (ma >>= k) = (liftT ma) >>= (liftT ∘ k);
}.

Notation "m1 ;; m2" := (bind m1 (fun _ => m2))  (at level 60, right associativity) : monad_scope.
Notation "'perf' x '<-' m ';' e" := (bind m (fun x => e))
  (at level 60, x ident, m at level 200, e at level 60) : monad_scope.


Open Scope monad_scope.
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

End monadic_functions.

Section monadic_state.

Variable S : Type.

Definition State (A : Type) := S -> A * S.

(* Arguments State [S]. *)

Definition state_bind A (st_a : State A) B  (f : A -> State B) :=
  fun  s => let (a,s) := st_a s in
            f a s.

Definition putS (x : S) : State unit :=
  fun _ => (tt,x).

Definition getS : State S :=
  fun x => (x,x).

Arguments getS _ : assert.

Definition runState  {A} (op : State A) : S -> A * S := op.

(* Definition evalState {A} (op : State A) : S -> A := fst ∘ op. *)
(* Definition execState {A} (op : State A) : S -> S := snd ∘ op. *)

Global Program Instance stateM : Monad (State) :=
    { return_ := fun A a s => (a,s);
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

Definition modify (f : S -> S) : State () :=
  getS >>= (fun s => putS (f s)).

End monadic_state.

Section monadic_loop.

Definition LoopT e m a : Type := (forall (r : Type), (e -> m r) -> (a -> m r) -> m r).

Definition runLoopT {m e a r} (loop : LoopT e m a) : (e -> m r) -> (a -> m r) -> m r :=
  fun exit next => loop r exit next.
(*
Check runLoopT. *)

Arguments runLoopT {_} {_} {_} {_}.

(* pure for Loop *)
Definition loopT_pure {m e A} (a : A) : LoopT e m A :=
  fun _ _ cont => cont a.

(* >>= for Loop *)
Definition loopT_bind {m e A} (x : LoopT e m A) {B} (k : A -> LoopT e m B) : LoopT e m B :=
  (fun _ exit cont =>
    let f' := (fun a => runLoopT (k a) exit cont) in
    runLoopT x exit f').
(* f' : continuation for the first loopT, cont : continuation for the scd loopT *)

(* Monad instance *)
Global Program Instance loopT_M {e m} : Monad (LoopT e m) :=
  { return_ := @loopT_pure m e;
    bind := @loopT_bind m e}.

Variable m : Type -> Type.
Variable e: Type.
Context `{Mo : Monad m}.

Definition loopT_liftT {A} (x : m A) : LoopT e m A :=
(fun _ _ cont => bind x cont).
(* bind from sub monad *)

Global Program Instance LoopT_T  : MonadTrans (LoopT e):=
{ liftT := @loopT_liftT}.
  Next Obligation.
  intros;cbn.
  unfold loopT_liftT.
  unfold loopT_pure.
  extensionality r.
  extensionality exit.
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
  extensionality exit.
  extensionality cont.
  rewrite bind_associativity.
  reflexivity.
  Qed.

Import List.

Definition stepLoopT {e m a} `{Mo : Monad m} (body : LoopT e m a) (next : a -> m e) : m e :=
  runLoopT body (return_) next.
  (* return_ of submonad *)

Definition exit {m a} : LoopT unit m a :=
  fun _ fin _ => fin tt.

Arguments exit {_} {_}.

Fixpoint foreach {m} `{Monad m}  (it min : nat) (body : nat -> LoopT unit m unit) : m unit :=
  if (it <=? min) then return_ tt
  else match it with
      | S it' => stepLoopT (body it') (fun _ => foreach it' min body)
      | 0 => return_ tt
    end.

(* Fonction qui appelle une fois le corps de la boucle *)
Definition once {m} `{Monad m} {a} (body : LoopT unit m a) : m unit :=
stepLoopT body (fun _ => return_ tt).

End monadic_loop.

Section monadic_loop2.

Variable m : Type -> Type.
Context `{Monad m}.

Inductive Action (A : Type) : Type :=
  | Break : Action A
  | Atom : A -> Action A.

Arguments Atom [A] _.
Arguments Break [A].

Definition LoopeT m a : Type := m (Action a).

Definition runLoopeT {A} (loop : LoopeT m A) : m (Action A) :=
  loop.

Definition loopeT_pure {A} (a : A) : LoopeT m A :=
  return_ (Atom a).

Definition loopeT_bind  {A} (x : LoopeT m A) {B} (k : A -> LoopeT m B) : LoopeT m B :=
    perf o <- runLoopeT x;
    match o with
      | Break => return_ Break
      | Atom y => runLoopeT (k y)
    end.

Definition loopeT_liftT {A} (a : m A) : LoopeT m A :=
  liftM (@Atom A) a.

Definition break {A} : LoopeT m A :=
  return_ Break.

Fixpoint foreach2 (it min : nat) (body : nat -> LoopeT m unit) : m unit :=
  if (it <=? min) then return_ tt
  else match it with
        | S it' => perf out <- runLoopeT (body it');
                                match out with
                                  | Break => return_ tt
                                  | _ => foreach2 it' min body
                                end
        | 0 => return_ tt
       end.

(* Program Fixpoint range (from to : Z) {measure (Z.abs_nat (to - from))} : list Z :=
  if Z_lt_dec from to
  then from :: range (from + 1) to
  else [].
Next Obligation. apply Zabs_nat_lt; auto with zarith. Qed. *)

Program Fixpoint foreach3 (from to : Z) (body : Z -> LoopeT m unit) {measure (Z.abs_nat (to - from))} : m unit :=
  if Z_lt_dec from to
  then perf out <- runLoopeT (body from);
                                match out with
                                  | Break => return_ tt
                                  | _ => foreach3 (from + 1) to body
                                end
  else return_ tt.
Next Obligation. 
apply Zabs_nat_lt; auto with zarith. Qed.

End monadic_loop2.

Notation "'for' i '=' max 'to' min '{{' body }}" := (foreach max min (fun i => (loopT_liftT body))) (at level 60, i ident, min at level 60,
max at level 60, body at level 60, right associativity) : monad_scope.

Notation "'for_e' i '=' max 'to' min '{{' body }}" := (foreach max min (fun i => (body))) (at level 60, i ident, min at level 60,
max at level 60, body at level 60, right associativity) : monad_scope.

Notation "'for2' i '=' max 'to' min '{{' body }}" := (foreach2 max min (fun i => (loopeT_liftT body))) (at level 60, i ident, min at level 60,
max at level 60, body at level 60, right associativity) : monad_scope.

Notation "'for2_e' i '=' max 'to' min '{{' body }}" := (foreach2 min max (fun i => (body))) (at level 60, i ident, min at level 60,
max at level 60, body at level 60, right associativity) : monad_scope.
