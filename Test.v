Require Import Program ZArith.

Set Implicit Arguments.

Import Notations.

Local Notation "f ∘ g" := (fun x => f (g x)) (at level 40, left associativity).

(* State Monad *)

Record S : Type:= {
  r : nat
}.

Definition State (A : Type) := S -> A * S.

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

Definition put (x : S) : State () :=
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

(* modify = 
fun (S : Type) (f : S -> S) => perf s <- getS (S:=S); putS (f s)
     : forall S : Type, (S -> S) -> State S () *)
Definition modify (f : S -> S) : State () :=
  perf s <- get; put (f s).

Definition Assertion := S -> Prop.

Definition hoareTripleS {A} (P : S -> Prop) (m : State A) (Q : A -> S -> Prop) : Prop :=
  forall (s : S), P s -> let (a, s') := m s in Q a s'.

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
  extensionality s; unfold state_bind; case (m s); trivial; tauto.
  Qed.

Lemma l_put (s : S) (P : unit -> Assertion) : {{ fun _ => P tt s }} put s {{ P }}.
Proof.
intros s0 H;trivial.
Qed.

Lemma l_get (P : S -> Assertion) : {{ fun s => P s s }} get {{ P }}.
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

(* End state_monad.

Section loop_monad. *)

Definition LoopT a : Type := (forall (r : Type), (a -> State r) -> State r).

Definition runLoopT {a r} (loop : LoopT a) (next : a -> State r) :  State r :=
  loop r next.
(* next : (a -> LoopT r) *)

(* Arguments runLoopT {_} {_} {_} {_}. *)

Definition loopT_pure {A} (a : A) : LoopT A :=
  fun _ next => next a.

(* >>= for Loop *)
Definition loopT_bind {A} (x : LoopT A) {B} (k : A -> LoopT B) : LoopT B :=
  (fun _ next =>
    let f' := (fun a => runLoopT (k a) next) in
    runLoopT x f').

(*   bind_right_unit: forall A (a: m A), a = bind a return_;
  bind_left_unit: forall A (a: A) B (f: A -> m B),
             f a = bind (return_ a) f;
  bind_associativity: forall A (ma: m A) B f C (g: B -> m C),
                 bind ma (fun  x=> bind (f x) g) = bind (bind ma f) g *)
Lemma loopT_bind_right_unit :
  forall A (a : LoopT A), a = loopT_bind a loopT_pure.
  Proof.
  auto.
  Qed.

Lemma loopT_bind_left_unit :
  forall A (a: A) B (f: A -> LoopT B),
             f a = loopT_bind (loopT_pure a) f.
  Proof.
  auto.
  Qed.

Lemma loopT_bind_associativity :
  forall A (ma: LoopT A) B f C (g: B -> LoopT C),
                 loopT_bind ma (fun  x=> loopT_bind (f x) g) = loopT_bind (loopT_bind ma f) g.
  Proof.
  auto.
  Qed.

(* forall {A}, m A -> t m A; *)
Definition loopT_liftT {A} (x : State A) : LoopT A :=
(fun _ cont => state_bind x cont).

(* Variable S : Type.

Definition stepLoopT {e a}  (body : LoopT e (State S) a) (next : a -> (State S) e) : (State S) e :=
  runLoopT body (return_) next. *)

Definition stepLoopT {a} (body : LoopT a) (next : a -> State ()) : State () :=
  runLoopT body next.

(* lifT_id : forall {A : Type} (a : A), (liftT ∘ return_) a = return_ a;
lifT_bind : forall A B (ma : m A) (k : A -> m B), liftT (ma >>= k) = (liftT ma) >>= (liftT ∘ k); *)

Lemma loopT_liftT_id :
  forall {A : Type} (a : A), (loopT_liftT ∘ (@ state_pure A)) a = loopT_pure a.
  Proof.
  intros;cbn.
  unfold loopT_liftT.
  unfold loopT_pure.
  extensionality r.
  extensionality exit.
  extensionality cont.
  rewrite <- state_bind_left_unit.
  reflexivity.
  Qed.

Lemma loopT_lifT_bind :
  forall A B (ma : State A) (k : A -> State B), 
      loopT_liftT (state_bind ma k) = loopT_bind (loopT_liftT ma) (loopT_liftT ∘ k).
  Proof.
  intros;cbn.
  unfold loopT_liftT.
  unfold loopT_bind.
  unfold runLoopT.
  extensionality r.
  extensionality exit.
  extensionality cont.
  rewrite state_bind_associativity.
  reflexivity.
  Qed.

Import List.

Definition foreach''{v} (values : list v) {a} (body : v -> LoopT a) : State () :=
  fold_right
    (fun x next => stepLoopT (body x) (fun _ => next))
    (state_pure tt)
    values.

Definition foreach'(min max : nat) (body : nat -> LoopT ()) : State () :=
  foreach'' (seq min (max-min)) body.

Notation "'for' i '=' min 'to' max '{{' body }}" := (foreach' min max (fun i => (loopT_liftT body))) (at level 60, i ident, min at level 60,
max at level 60, body at level 60, right associativity) : monad_scope.

Notation "'for2' i '=' min 'to' max '{{' body }}" := (foreach' min max (fun i => (body))) (at level 60, i ident, min at level 60,
max at level 60, body at level 60, right associativity) : monad_scope.

(* Au dessus de ma fonction foreach *)

Definition hoareTripleL {A B} (P : Assertion) (m : LoopT A) (Q : B -> Assertion) : Prop := 
  forall (s : S) (next : A -> State B), P s -> let m' := (runLoopT m next) in
   let (b,s') := m' s in Q b s'.

Notation "{[ P ]} m {[ Q ]}" := (hoareTripleL P m Q)
  (at level 90, format "'[' '[' {[  P  ]}  ']' '/  ' '[' m ']' '['  {[  Q  ]} ']' ']'") : monad_scope.

(* Lie une monade d'état à sa monade loop associée *)
(* Definition match_monad {A} : LoopT A -> State A -> Prop :=
  forall (mL : LoopT A) (mS : State A), loopT_liftT mS = mL. *)

(* Lemma match_monad_spec {A} (mL : LoopT A) (mS : State A): 
  loopT_liftT mS = mL -> match_monad mL mS.
  Proof.
  constructor.
  assumption.
  Qed. *)

(* Inductive foreach_L {A B} (P : Assertion) (m : LoopT A) (Q : B -> Assertion) : Prop :=
  | For_E :
  | For_N : forall A', HoareTriple_L P m Q ->  foreach_L P m Q -> foreach_L *)

Notation "{[ P ]} m {[ Q ]}" := (hoareTripleL P m Q)
  (at level 90, format "'[' '[' {[  P  ]}  ']' '/  ' '[' m ']' '['  {[  Q  ]} ']' ']'") : monad_scope.

Lemma loopT_to_state (P : S -> Prop) (Q : () -> S -> Prop) (mo : State ()) :
  (forall mT : LoopT (), mT = loopT_liftT mo -> {{P}} mo {{Q}} -> 
  {[P]} mT {[Q]}).
  Proof.
  intros.
  rewrite H.
  unfold loopT_liftT.
  unfold state_bind.
  unfold hoareTripleL.
  intros.
  unfold hoareTripleS in H0.
  unfold runLoopT.
  destruct (mo s).
  case (next u s0).
  intros.
  
  Admitted.

Lemma foreach_rule (min max : nat) (P : S -> Prop) (body : nat -> LoopT ())
  : (forall (it:nat), {[fun s => P s /\ (Nat.le min it) /\ (it < max)]} 
  body it {[fun (_: unit) => P]}) -> 
  {{P}} foreach' min max (body) {{fun _ => P}} .
  Admitted.

(* Lemma state_to_loop (P : S -> Prop) (body : nat -> State ()) : 
  forall (it:nat), {{fun s => P s /\ (min <= it) /\ (it < max)}} 
  body it {[fun (_: unit) => P]} -> 	  body it {[fun (_: unit) => P]}) -> 
  {{P}} foreach' min max (body) {{fun _ => P}} . *)

(* Lemma foreach_rule (min max : nat) (P : S -> Prop) (m : nat -> State ())
  : (forall (it:nat), {{fun s => P s /\ (min <= it < max)}} m it {{fun _ => P}}
    -> {{P}}foreach' min max (fun it0 => loopT_liftT (m it0)) {{fun _ => P}}).
  Proof.
  intros it.
  Admitted. *)

Definition init_state : S := {|r := 1|}.

Definition add_s (i : nat) : State unit :=
  modify (fun s => {| r := s.(r) + i |}).

Definition min_s (i : nat) : State unit :=
modify (fun s => {| r := s.(r) - i |}).

Definition mul_s (i : nat) : State unit :=
  modify (fun s => {| r := s.(r) * i |}).

Definition fac5 : State unit :=
  for i = 1 to 6 {{
    mul_s i
  }}.

Compute runState fac5 init_state.

Definition slow_add (m : nat) : State unit :=
  for i = 0 to m {{
    add_s 1
  }}.

Definition slow_add2 (m : nat) : State unit :=
  for i = 0 to m {{
    if ((Nat.modulo i 2) =? 0) then
      add_s 1
    else
      add_s 2
  }}.

Compute runState (slow_add 7) init_state.

(* Lemma l_slow_add (n m : nat): 
 {{(fun s : S => r s = n)}} slow_add m {{(fun (_ : unit ) (s : S) => r s = (Nat.add m n))}}.
Proof.
eapply strengthen.
eapply weaken.
unfold slow_add.
eapply foreach_rule.
2 : { intros.
      assert (H2 : r s <= (n + m)).
      - 
      apply Nat.eq_le_incl in H.
      eapply le_plus_trans.
      trivial.
      - apply H2. }
+ intros. eapply loopT_to_state with (add_s 1).
  - trivial.
  - admit. 
+ cbn.
unfold add_s.
eapply weaken.
apply l_modify.
intros.
simpl.
trivial.
  - intros.
    simpl in H.
    
Admitted. *)

Compute runState fac5 init_state.

Lemma l_fac5 : 
 {{(fun s : S => r s = 1)}} fac5 {{(fun (_ : unit ) (s : S) => r s = 120)}}.
Proof.
eapply strengthen.
unfold fac5.
eapply foreach_rule.
+ intros.
  
  - eapply weaken.
unfold l.
intros s H.
eapply foreach_rule.

+ admit.
+ admit.

(* Lemma l_add_s :
 forall (n i : nat), {{fun (s : S) => val s = n}} add_s i {{fun (_ : unit) (s : S) => val s = (n + i)}}.
  Proof.
  intros n i s H.
  unfold add_s.
  apply l_modify.
  auto.
  Qed. *)