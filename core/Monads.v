Require Import Program.

Set Implicit Arguments.

Import Notations.

Local Notation "f ∘ g" := (fun x => f (g x)) (at level 40, left associativity).

(* Section definition. *)

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

(* Class MonadState (m: Type -> Type) `{Monad m} := {
  get : forall S, m S;
  put : forall S, S -> m unit;
  run : forall {S A}, m A -> S -> (A * S); *)
(*   hoareTriple : forall {A} (P : S -> Prop) (ma : m A) (Q : A -> S -> Prop) (s : S), P s -> let (a, s') := (run ma s) in Q a s' *)

(* Monad Transformer *)
Class MonadTrans {m} `{Monad m} (t : (Type -> Type) -> (Type -> Type)) `{Monad (t m)}  := {
  (* Lift fonction and monade transformers laws *)
  liftT : forall {A}, m A -> t m A;
  lifT_id : forall {A : Type} (a : A), (liftT ∘ return_) a = return_ a;
  lifT_bind : forall A B (ma : m A) (k : A -> m B), liftT (ma >>= k) = (liftT ma) >>= (liftT ∘ k);
  
  (* hoare triple *)
 (*  getT : get *)
}.

Notation "m1 ;; m2" := (bind m1 (fun _ => m2))  (at level 60, right associativity) : monad_scope.
Notation "'perf' x '<-' m ';' e" := (bind m (fun x => e))
  (at level 60, x ident, m at level 200, e at level 60) : monad_scope.

(* End definition. *)


(* Notation "a >>= f" := (bind a f) (at level 50, left associativity) : monad_scope. *)
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

Definition Assertion := S -> Prop.

Definition hoareTripleS {A} (P : S -> Prop) (m : State A) (Q : A -> S -> Prop) : Prop :=
  forall (s : S), P s -> let (a, s') := m s in Q a s'.

Notation "{{ P }} m {{ Q }}" := (hoareTripleS P m Q)
  (at level 90, format "'[' '[' {{  P  }}  ']' '/  ' '[' m ']' '['  {{  Q  }} ']' ']'") : monad_scope.

Lemma l_ret (A : Type) `{State A} (a : A) (P : A -> Assertion) : {{ P a }} return_ a {{ P }}.
Proof.
intros s H; trivial.
Qed.

(* Triplet de hoare sur la séquence *)
Lemma l_bind  (A B : Type) (m : State A) (f : A -> State B) (P : Assertion)( Q : A -> Assertion) (R : B -> Assertion) :
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
  extensionality s.
  unfold bind.
  case (m s).
  simpl.
  intros.
  unfold state_bind.
  case (m s).
  intros.
  reflexivity.
  Qed.

Lemma l_put (s : S) (P : unit -> Assertion) : {{ fun _ => P tt s }} putS s {{ P }}.
Proof.
intros s0 H;trivial.
Qed.

Lemma l_get (P : S -> Assertion) : {{ fun s => P s s }} getS {{ P }}.
Proof.
intros s H; trivial.
Qed.

Lemma bindRev (A B : Type) (m : State A) (f : A -> State B) (P : Assertion)( Q : A -> Assertion) (R : B -> Assertion) :
  {{ P }} m {{ Q }} -> (forall a, {{ Q a }} f a {{ R }}) -> {{ P }} perf x <- m ; f x {{ R }}.
Proof.
intros; eapply l_bind ; eassumption.
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
eapply l_bind.
intros.
eapply l_put.
simpl.
eapply weaken.
eapply l_get.
intros. simpl.
assumption.
Qed.

(* Global Instance stateS : MonadState (State) :=
  {  get := @getS;
    put := @putS;
    run := @runState;
  }. *)
(*     hoareTriple : @ *)

End monadic_state.

Section monadic_loop.

Definition LoopT e m a : Type := (forall (r : Type), (e -> m r) -> (a -> m r) -> m r).

Definition runLoopT {m e a r} (loop : LoopT e m a) : (e -> m r) -> (a -> m r) -> m r :=
  fun exit next => loop r exit next.

Check runLoopT.

Arguments runLoopT {_} {_} {_} {_}.

(* pure for Loop *)
Definition loopT_pure {m e A} (a : A) : LoopT e m A :=
  fun _ _ cont => cont a.

(* >>= for Loop *)
Definition loopT_bind {m e A} (x : LoopT e m A) {B} (k : A -> LoopT e m B) : LoopT e m B :=
  (fun _ exit cont =>
    let f' := (fun a => runLoopT (k a) exit cont) in
    runLoopT x exit f').

(* Variable m : Type -> Type.
Variable e : Type. *)

Check loopT_pure.
Check loopT_bind.

(* Monad instance *)
Global Program Instance loopT_M {e m} : Monad (LoopT e m) :=
  { return_ := @loopT_pure m e;
    bind := @loopT_bind m e}.

Variable m : Type -> Type.
Variable e: Type.
Context `{Mo : Monad m}.

Definition loopT_liftT {A} (x : m A) : LoopT e m A :=
(fun _ _ cont => bind x cont).

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

Definition HoareTriple_L {A S E} (P : S -> Prop) (m : LoopT E (State S) A) (Q : (E -> S -> Prop)) : Prop :=
  forall (s : S) (next : A -> State S E), P s -> let m' := (stepLoopT m next) in let (b,s') := m' s in Q b s'.

(* Lemma foreach_rule {S} (P : S -> Prop) (m : LoopT E (State S) A) (Q : (E -> S -> Prop)
  : forall (it:nat) (s : S), (Nat.le min it) /\ (it < max) ->  *)

(*   fun loop exit next => loop r exit next. *)
(* Definition exitWith {m E a} (e : E): LoopT E m a :=
  fun _ fin _ => fin e. *)
  
Definition exit {m a} : LoopT unit m a :=
  fun _ fin _ => fin tt.

Arguments exit {_} {_}.

Definition when {m} `{Monad m} : bool -> m unit -> m unit :=
  fun p s => if p then s else return_ tt. 

(* Boucle qui prend une liste en paramètres et applique le corps de boucle pour chaque élement de la liste *)
Definition foreach'' {m} `{Monad m} {a} (values : list a) {c} (body : a -> LoopT unit m c) : m unit :=
  fold_right
    (fun x next => stepLoopT (body x) (fun _ => next))
    (return_ tt)
    values.

(* Boucle avec un min et max qui appelle foreach' *)
Definition foreach' {m} `{Monad m} (min max : nat) {a} (body : nat -> LoopT unit m a) : m unit :=
  foreach'' (seq min (max-min)) body.

(* Notation "'foreach i '=' min 'to' max '{{' body }}" := (foreach' min max (fun i => (body))) (at level 60, i ident, min at level 60, 
max at level 60, body at level 60, right associativity) : monad_scope. *)

(* Fonction qui appelle une fois le corps de la boucle *)
Definition once {m} `{Monad m} {a} (body : LoopT unit m a) : m unit :=
stepLoopT body (fun _ => return_ tt).

End monadic_loop.

Notation "'for' i '=' min 'to' max '{{' body }}" := (foreach' min max (fun i => (loopT_liftT body))) (at level 60, i ident, min at level 60,
max at level 60, body at level 60, right associativity) : monad_scope.

Notation "'for_e' i '=' min 'to' max '{{' body }}" := (foreach' min max (fun i => (body))) (at level 60, i ident, min at level 60,
max at level 60, body at level 60, right associativity) : monad_scope.