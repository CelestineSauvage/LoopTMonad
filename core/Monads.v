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

Ltac cbnify_monad_LHS :=
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
  end; cbnify_monad).

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

(* Program Fixpoint foreach3 (from to : Z) (body : Z -> LoopeT m unit) {measure (Z.abs_nat (to - from))} : m unit :=
  if Z_lt_dec from to
  then perf out <- runLoopeT (body from);
                                match out with
                                  | Break => return_ tt
                                  | _ => foreach3 (from + 1) to body
                                end
  else return_ tt.
Next Obligation. 
apply Zabs_nat_lt; auto with zarith. Qed. *)

(* Program Fixpoint foreach42 (from to : Z) (body : Z -> LoopT unit m unit) {measure (Z.abs_nat (to - from))} : m unit :=
  if Z_lt_dec from to
  then (stepLoopT (body (from + 1)) (fun _ => foreach42 (from + 1) to body))
  else return_ tt.
Next Obligation. 
apply Zabs_nat_lt; auto with zarith. Qed. *)

(* Fonction qui appelle une fois le corps de la boucle *)
Definition once {m} `{Monad m} {a} (body : LoopT unit m a) : m unit :=
stepLoopT body (fun _ => return_ tt).

End monadic_loop.

Section monadic_loop2.

Section monad_option.

Inductive Action (A : Type) : Type :=
  | Break : Action A
  | Continue : Action A
  | Atom : A -> Action A.

Arguments Atom [A] _.
Arguments Break [A].
Arguments Continue [A].

Global Program Instance actionM : Monad Action :=
  { return_ := @Atom;
    bind := fun A m B f => match m with Break => Break | Continue => Continue | Atom a => f a end
  }.
  Next Obligation.
  destruct a ; auto.
  Qed.
  
  Next Obligation.
  destruct ma ; auto.
  Qed.

Definition LoopeT m (a : Type) : Type := m (Action a).

Definition loopeT_liftT {m A} `{Monad m} (a : m A) : LoopeT m A.
Proof.
unfold LoopeT.
refine (perf x <- a; return_ (Atom x)).
Defined.

Definition runLoopeT {m A} (loop : LoopeT m A) : m (Action A) :=
  loop.

Definition loopeT_pure {m} `{Monad m} {A} (a : A) : LoopeT m A :=
  return_ (Atom a).
(*   @return_ m _ _ (return_ a). *)

(* Definition loopeT_bind {m} `{Monad m} {A} (ma : LoopeT m A) {B} (f : A -> LoopeT m B)
                        : LoopeT m B.
Proof.
unfold LoopeT in *.
exact (perf oa <- ma; 
         match oa with
         | Break => return_ Break
         | Continue => return_ Continue
         | Atom a => f a
         end
  ).
Defined. *)

Definition loopeT_bind {m} `{Monad m} {A} (x : LoopeT m A) {B} (k : A -> LoopeT m B) : LoopeT m B :=
    perf o <- runLoopeT x;
    match o with
      | Break => return_ Break
      | Continue => return_ Continue
      | Atom y => runLoopeT (k y)
    end.

Arguments Monad m : assert.

(* Class Monad (m: Type -> Type) :=
{ return_ : forall {A}, A -> m A;
  bind: forall {A}, m A -> forall {B}, (A -> m B) -> m B;
  bind_right_unit: forall A (a: m A), a = bind a return_;
  bind_left_unit: forall A (a: A) B (f: A -> m B),
             f a = bind (return_ a) f;
  bind_associativity: forall A (ma: m A) B f C (g: B -> m C),
                 bind ma (fun  x=> bind (f x) g) = bind (bind ma f) g
}. *)

Print bind.

Close Scope monad_scope.

Global Program Instance loopeT_M  {m} `{Monad m} : Monad (LoopeT m) :=
  { return_ := @loopeT_pure m _;
    bind := @loopeT_bind m _  }.
  Next Obligation.
  unfold loopeT_pure.
  unfold loopeT_bind.
  unfold runLoopeT.
  generalize (bind_right_unit (Action A) a).
  intros.
  rewrite H0 at 1.
(*   assert (forall o : Action A, match o with
          | Break => return_ Break
          | Continue => return_ Continue
          | Atom y => return_ (Atom y)
          end = return_ o).
  intros.
  case o ; auto. *)
  f_equal.
  apply functional_extensionality.
  intros.
  case x ; auto.
  Qed.

  Next Obligation.
  unfold loopeT_pure.
  unfold loopeT_bind.
  unfold runLoopeT.
  unfold LoopeT in f.
  pose proof bind_left_unit.
  generalize (H0 A a (Action B) f).
  intros.
  pose proof bind_right_unit.
(*   rewrite H1 at 1. *)
  pose proof bind_associativity.
  pose proof actionM_obligation_2.
  assert (bind (return_ a) f = bind (return_ (Atom a)) (fun _ => f a)).
  + cbn.
  rewrite equal_f .
(*   case_eq (f (return_ a)). *)
  rewrite H2 at 1.
  refine 
  case o ; auto.
  apply f_equal.
  apply functional_extensionality.
  auto.
  Qed.


(* Definition loopeT_bind  {A} (x : LoopeT m A) {B} (k : A -> LoopeT m B) : LoopeT m B :=
    perf o <- runLoopeT x;
    match o with
      | Break => return_ Break
      | Atom y => runLoopeT (k y)
    end. *)

(* Class Monad (m: Type -> Type) :=
{ return_ : forall {A}, A -> m A;
  bind: forall {A}, m A -> forall {B}, (A -> m B) -> m B;
  bind_right_unit: forall A (a: m A), a = bind a return_;
  bind_left_unit: forall A (a: A) B (f: A -> m B),
             f a = bind (return_ a) f;
  bind_associativity: forall A (ma: m A) B f C (g: B -> m C),
                 bind ma (fun  x=> bind (f x) g) = bind (bind ma f) g
}. *)

(* Notation "'perf' x '<-' m ';' e" := (bind m (fun x => e)) *)


(*                         
  Proof.
  + intros.
    unfold runLoopeT.
    cbv.
    case H.
    intros.
    generalize (bind_right_unit0 (Action A) a).
    intros.
    unfold LoopeT in *.
    rewrite H0 at 1.
    symmetry. *)
    
   
(* Definition loopeT_liftT {m A} `{Monad m} (a : m A) : LoopeT m A :=
  liftM (@Atom A) a. *)

Definition break {m A} `{Monad m} : LoopeT m A :=
  return_ Break.

Fixpoint foreach2 {m} `{Monad m}(it min : nat) (body : nat -> LoopeT m unit) : m unit :=
  if (it <=? min) then return_ tt
  else match it with
        | S it' => perf out <- (body it');
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

Notation "'for3' i '=' max 'to' min '{{' body }}" := (foreach2 min max (fun i => (body))) (at level 60, i ident, min at level 60,
max at level 60, body at level 60, right associativity) : monad_scope.