Require Import Program List ZArith Arith.

Set Implicit Arguments.

Import Notations.

Local Notation "f ∘ g" := (fun x => f (g x)) (at level 40, left associativity).

(* State Monad *)

Record St : Type:= {
  r : nat
}.

Definition State (A : Type) := St -> A * St.

(* Arguments State [ A ]. *)

(* forall {A}, A -> m A; *)
Definition state_pure A (a : A) : State A := 
  fun s => (a,s).

(* state_bind = 
fun (A : Type) (st_a : State A) (B : Type) (f : A -> State B) (s : S) => let (a, s0) := st_a s in f a s0
     : forall A : Type, State A -> forall B : Type, (A -> State B) -> S -> B * S *)
Definition state_bind {A B} (st_a : State A) (f : A -> State B)  : State B :=
  fun s => let (a, s0) := st_a s in f a s0.


(*    bind: forall {A}, m A -> forall {B}, (A -> m B) -> m B;
  bind_right_unit: forall A (a: m A), a = bind a return_;
  bind_left_unit: forall A (a: A) B (f: A -> m B),
             f a = bind (return_ a) f;
  bind_associativity: forall A (ma: m A) B f C (g: B -> m C),
                 bind ma (fun  x=> bind (f x) g) = bind (bind ma f) g *)
(* Lemma bind_right_unit *)

Lemma state_bind_right_unit : 
  forall (A : Type) (a: State A), a = state_bind a (@ state_pure A).
  Proof.
  intros.
  unfold state_bind.
  apply functional_extensionality.
  intros.
  destruct (a x).
  reflexivity.
  Qed.

Lemma state_bind_left_unit :
   forall A (a: A) B (f: A -> State B),
             f a = state_bind (state_pure a) f.
   Proof.
   auto.
   Qed.

Lemma state_bind_associativity :
  forall A (ma: State A) B f C (g: B -> State C),
                 state_bind ma (fun x => state_bind (f x) g) = state_bind (state_bind ma f) g.
  Proof.
  intros.
  unfold state_bind.
  apply functional_extensionality.
  intros.
  destruct (ma x).
  reflexivity.
  Qed.

Definition put (x : St) : State () :=
  fun _ => (tt,x).

Definition get : State St :=
  fun x => (x,x).

Definition runState  {A} (op : State A) : St -> A * St := op.
Definition evalState {A} (op : State A) : St -> A := fst ∘ op.
Definition execState {A} (op : State A) : St -> St := snd ∘ op.

Notation "m1 ;; m2" := (state_bind m1 (fun _ => m2))  (at level 60, right associativity) : monad_scope.
Notation "'perf' x '<-' m ';' e" := (state_bind m (fun x => e))
  (at level 60, x ident, m at level 200, e at level 60) : monad_scope.

Open Scope monad_scope.

(* modify = 
fun (S : Type) (f : S -> S) => perf s <- getS (S:=S); putS (f s)
     : forall S : Type, (S -> S) -> State S () *)
Definition modify (f : St -> St) : State () :=
  perf s <- get; put (f s).

Definition Assertion := St -> Prop.

Definition hoareTripleS {A} (P : St -> Prop) (m : State A) (Q : A -> St -> Prop) : Prop :=
  forall (s : St), P s -> let (a, s') := m s in Q a s'.

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
intros a s' H4.
apply H2 in H3.
rewrite H4 in H3.
apply H1.
apply H3.
Qed.

Definition wp {A : Type} (P : A -> St -> Prop) (m : State A) :=
  fun s => let (a,s') := m s in P a s'.

Lemma wpIsPrecondition {A : Type} (P : A -> St -> Prop) (m : State A) :
  {{ wp P m }} m {{ P }}.
  Proof.
  unfold wp.
  congruence.
  Qed.

Lemma wpIsWeakestPrecondition
  (A : Type) (P : A -> St -> Prop) (Q : St -> Prop) (m : State A) :
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

Lemma l_put (s : St) (P : unit -> Assertion) : {{ fun _ => P tt s }} put s {{ P }}.
Proof.
intros s0 H;trivial.
Qed.

Lemma l_get (P : St -> Assertion) : {{ fun s => P s s }} get {{ P }}.
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

Lemma strengthen (A : Type) (m : State A) (P: Assertion) (Q R: A -> Assertion) :
  {{ P }} m {{ R }} -> (forall s a, R a s -> Q a s) -> {{ P }} m {{ Q }}.
Proof.
intros H1 H2 s H3.
apply H1 in H3.
Admitted.


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

Definition state_liftM {A B} (f : A -> B) (ma : State A) : State B :=
  state_bind ma (fun a => state_pure (f a)).
  
(* Section Continuation. *)

(* Inductive Action : Type :=
  | Atom : State Action -> Action
  | Stop : Action.

Definition LoopT a : Type := (a -> Action) -> Action.

Definition loopT_pure {A} (a : A) : LoopT A :=
  fun (c : A -> Action) => c a.

Definition loopT_bind {A} (x : LoopT A) {B} (k : A -> LoopT B) : LoopT B :=
  fun (c : B -> Action) => x (fun a => (k a) c).

Definition action {A} (x : LoopT A) : Action :=
  x (fun (_ : A) => Stop).

(* lift *)
Definition atom {A} (x : State A) : LoopT A := 
  fun c => Atom ( perf a <- x ; state_pure (c a)).

Open Scope list_scope.

Fixpoint round (lst : list Action) : State () :=
  match lst with
    | nil => state_pure tt
    | (a::ax) => match a with 
                  | Atom am => am ;; round ax
                  | Stop => round ax
                  end
    end.

Definition run {A} (x : LoopT A) : State () :=
  round [action x].

Definition stop {A} : LoopT A :=
  fun c => Stop. *)

Inductive Action (A : Type) : Type :=
  | Break : Action A
  | Atom : A -> Action A.

(* Definition hoareTripleS {A} (P : St -> Prop) (m : State A) (Q : A -> St -> Prop) : Prop :=
  forall (s : St), P s -> let (a, s') := m s in Q a s'. *)

Lemma act_ret  (A : Type) (a : A) (P : A -> Assertion) : {{ P a }} state_pure (Atom a) 
{{fun (_ : Action A) =>  P a }}.
Proof.
intros s H; trivial.
Qed.

(* Lemma ret_tt (P : () -> Assertion) : {{ P tt }} state_pure tt {{ P }}.
Proof.
intros s H; trivial.
Qed. *)

Arguments Atom [A] _.
Arguments Break [A].

Definition LoopT a : Type := State (Action a).

Definition runLoopT {A} (loop : LoopT A) : State (Action A) :=
  loop.

Definition loopT_pure {A} (a : A) : LoopT A :=
  (state_pure (Atom a)).

Definition loopT_bind  {A} (x : LoopT A) {B} (k : A -> LoopT B) : LoopT B :=
    perf o <- runLoopT x;
    match o with 
      | Break => state_pure Break
      | Atom y => runLoopT (k y)
    end.

Definition loopT_liftT {A} (a : State A) : LoopT A :=
  state_liftM (@Atom A) a.

Definition break {A} : LoopT A :=
  state_pure Break.

Fixpoint foreach (it : nat) (body : nat -> LoopT ()) : State () :=
  match it with
  | 0 => state_pure tt
  | S it' => perf out <- runLoopT (body it);
                    match out with
                      | Break => state_pure tt
                      | _ => foreach it' body
                    end
 end.

(* Definition foreach (min max : nat) (body : nat -> LoopT ()) : State () :=
  foreach' (seq min (max-min)) body. *)

Notation "'for' i '=' max {{' body }}" := (foreach max (fun i => (loopT_liftT body))) (at level 60, i ident,
max at level 60, body at level 60, right associativity) : monad_scope.

(* Notation "'for_e' i '=' min 'to' max '{{' body }}" := (foreach min max (fun i => (body))) (at level 60, i ident, min at level 60,
max at level 60, body at level 60, right associativity) : monad_scope.
 *)
(* Notation "'for2' i '=' min 'to' max '{{' body }}" := (foreach min max (fun i => (body))) (at level 60, i ident, min at level 60,
max at level 60, body at level 60, right associativity) : monad_scope. *)

Definition init_state : St := {|r := 1|}.

Definition add_s (i : nat) : State unit :=
  modify (fun s => {| r := s.(r) + i |}).

Definition min_s (i : nat) : State unit :=
modify (fun s => {| r := s.(r) - i |}).

Definition mul_s (i : nat) : State unit :=
  modify (fun s => {| r := s.(r) * i |}).

(* Definition fac5 : State unit :=
  for i = 5 to 0 {{
    mul_s i
  }}.
 *)
(* Compute runState fac5 init_state.  *)

(* Definition test_exit : State () :=
   for_e i = 0 to 20 {{
    if (i =? 5) then break
    else (loopT_liftT (add_s 1))
  }}.
 *)
(* Compute runState test_exit init_state.  *)

(* in_seq: forall len start n : nat, In n (seq start len) <-> start <= n < start + len *)
Lemma foreach_rule (max : nat) (P : () -> St -> Prop) (body : nat -> State ())
  : (forall (it : nat), {{fun s => P tt s /\ (0 <= it <= max)}} body it {{P}}) -> 
    {{P tt}} foreach max (fun it0 => loopT_liftT (body it0)) {{fun _ s => P tt s}}.
  Proof.
  intros H.
  induction max.
  + intros st HP. auto.
  + eapply bindRev .
    - unfold runLoopT.
      unfold loopT_liftT.
      unfold state_liftM.
      eapply bindRev.
      * intros st H2.
        eapply H;split;auto.
        split;auto.
        apply Nat.le_0_l.
      * intros [].
        apply act_ret.
   - intros [].
    * intros s HP. 
      apply ret.
      apply HP.
    * apply IHmax.
         ++ intros it s'.
            intros [H1 [H2 H3]].
            apply H.
            split;auto.
     Qed.

Definition slow_add : State unit :=
  foreach 10 (fun _ => loopT_liftT (add_s 1)).

Lemma l_slow_add (n : nat): 
 {{(fun s : St => r s = n)}} slow_add {{(fun (_ : unit ) (s : St) => r s = (Nat.add 10 n))}}.
  Proof.
  eapply weaken.
  eapply strengthen.
  apply foreach_rule.
  + 