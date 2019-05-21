Require Import Program List ZArith Arith.

Set Implicit Arguments.

Import Notations.

Section monads.

Local Notation "f ∘ g" := (fun x => f (g x)) (at level 40, left associativity).

(* State Monad *)

(* Record St : Type:= {
  r : nat;
}. *)

Variable St : Type.

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

Lemma act_ret  (A : Type) (a : A) (P : Assertion) : {{P}} state_pure (Atom a) 
{{fun (_ : Action A) =>  P }}.
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

Program Fixpoint foreach (it min : nat) (body : nat -> LoopT ()) : State () :=
  if (Nat.leb it min) then state_pure tt
  else match it with
        | S it' => perf out <- runLoopT (body it);
                                match out with
                                  | Break => state_pure tt
                                  | _ => foreach it' min body
                                end
        | 0 => state_pure tt
       end.

Lemma foreach_rule (min max : nat) (P : St -> Prop) (body : nat -> State ())
  : (forall (it : nat), {{fun s => P s /\ (min <= it <= max)}} body it {{fun _ => P}}) -> 
    {{P}} foreach max min (fun it0 => loopT_liftT (body it0)) {{fun _ => P}}.
  Proof.
  intros H.
  induction max.
  + intros st HP. auto.
  + unfold foreach.
    case_eq (S max <=? min);intros Hm.
    - intros s HP. trivial.
    - eapply bindRev .
      unfold runLoopT.
      unfold loopT_liftT.
      unfold state_liftM.
      eapply bindRev.
      * unfold hoareTripleS in H.
        intros st H2.
        eapply H;split;auto.
        split;auto.
        apply Nat.leb_gt in Hm.
        apply Nat.lt_le_incl.
        auto.
      * intros [].
        apply act_ret.
    * intros []. intros s HP. trivial.
      apply IHmax.
         ++ intros it s'.
            intros [H1 [H2 H3]].
            apply H.
            split;auto.
     Qed.

Lemma foreach_break_rule (min max : nat) (P : St -> Prop) (body : nat -> State ())
  : forall (cond : bool), (forall (it : nat), {{fun s => P s /\ (min <= it <= max) /\ (cond = true) }} body it {{fun _ => P}}) -> 
    {{P}} foreach max min (fun it0 => if (cond) then break else loopT_liftT (body it0)) {{fun _ s => P s /\ cond = false}}.
  Admitted.

Notation "'for' i '=' max 'to' min '{{' body }}" := (foreach max min (fun i => (loopT_liftT body))) (at level 60, i ident, min at level 60,
max at level 60, body at level 60, right associativity) : monad_scope.

(* (* Notation "'for_e' i '=' min 'to' max '{{' body }}" := (foreach min max (fun i => (body))) (at level 60, i ident, min at level 60,
max at level 60, body at level 60, right associativity) : monad_scope. *)

(* Notation "'for2' i '=' min 'to' max '{{' body }}" := (foreach min max (fun i => (body))) (at level 60, i ident, min at level 60,
max at level 60, body at level 60, right associativity) : monad_scope. *) *)

End monads.

Notation "m1 ;; m2" := (state_bind m1 (fun _ => m2))  (at level 60, right associativity) : monad_scope.
Notation "'perf' x '<-' m ';' e" := (state_bind m (fun x => e))
  (at level 60, x ident, m at level 200, e at level 60) : monad_scope.
Notation "{{ P }} m {{ Q }}" := (hoareTripleS P m Q)
(at level 90, format "'[' '[' {{  P  }}  ']' '/  ' '[' m ']' '['  {{  Q  }} ']' ']'") : monad_scope.
Notation "'for' i '=' max 'to' min '{{' body }}" := (foreach max min (fun i => (loopT_liftT body))) (at level 60, i ident, min at level 60,
max at level 60, body at level 60, right associativity) : monad_scope.

Open Scope monad_scope.

Record MySt : Type:= {
  r : nat;
}. 

Definition init_state : MySt := {|r := 1|}.

Definition add_s (i : nat) : State MySt unit :=
  modify (fun s => {| r := s.(r) + i |}).

Definition min_s (i : nat) : State MySt unit :=
modify (fun s => {| r := s.(r) - i |}).

Definition mul_s (i : nat) : State MySt unit :=
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


(* Lemma foreach_break_rule_2 (min max : nat) (P : () -> St -> Prop) (body : nat -> State ()) (compare : State bool)
  : forall (cond : bool), (forall (it : nat), {{fun s => P tt s /\ (min <= it <= max) /\ (cond s = true) }} body it {{P}}) -> 
    {{P tt}} foreach max min (fun it0 => perf cond <- compare;  if (fun s => cond s) then break else loopT_liftT (body it0))
    {{fun _ s => P tt s /\ (cond s) = false}}.
  Admitted. *)

Definition slow_add (m : nat) : State MySt unit :=
  for i = m to 0 {{
    add_s m
  }}.

(* Definition fast_add : State unit :=
  for i = 5 to 0 {{
    add_s i
  }}. *)

Definition compare : State MySt bool :=
  perf s <- (@get MySt) ;
  state_pure (Nat.leb (r s) 2).

(* Definition parity_x : State unit :=
  for_e i = 500 to 0 {{
    perf cond <- compare;
    if (cond) then break
    else loopT_liftT(min_s 2)
  }}.
 *)
(* Compute runState parity_x {| r := 10 |}. *)

(* Lemma l_parity_x :
  {{(fun s : St => r s = 10)}} parity_x {{(fun (_ : unit ) (s : St) => r s = 2)}}.
  Admitted. *)
(* Lemma foreach_rule (min max : nat) (P : () -> St -> Prop) (body : nat -> State ())
  : (forall (it : nat), {{fun s => P tt s /\ (min <= it <= max)}} body it {{P}}) -> 
    {{P tt}} foreach max min (fun it0 => loopT_liftT (body it0)) {{fun _ s => P tt s}}. *)
Lemma l_slow_add (m : nat) : 
 {{(fun s : MySt => True)}} slow_add m{{(fun (_ : unit ) (s : MySt) => r s >= m)}}.
  Proof.
  unfold slow_add.
  eapply weaken.
(*   eapply strengthen. *)
  apply foreach_rule.
  unfold add_s.
  intros.
  eapply weaken.
  apply l_modify.
  simpl.
  intros.
  auto.
  simpl.
  intros.
  auto.
  Admitted.

Fixpoint sumsum (n : nat): nat :=
  match n with
    | 0 => 0
    | S n' => n + (sumsum n')
  end.
  
(* Lemma l_fast_add (n : nat):
  {{(fun s : St => r s = n)}} fast_add {{(fun (_ : unit ) (s : St) => r s < (Nat.add (sumsum 5) n))}}.
  Proof.
  apply weaken with (fun s => r s <= 42).
  eapply strengthen.
  apply foreach_rule. *)

Record tab : Type := {
  mytab : list nat
}.

Fixpoint changeElement (i n : nat) (l: list nat) : list nat :=
 match (l,i) with
  | ([], _) => []
  | (a :: l', 0) => n :: l'
  | (a :: l', S i') => a :: changeElement i' n l'
  end.

(* Compute changeElement 8 18 [0;1;2;3;4;5]. *)

Definition changeTab (i n: nat) : State tab unit :=
  modify (fun s => {| mytab := changeElement i n (mytab s)|}).

(* Compute nth 2 [0;1;2;3;4;5] 0. *)

Definition table : tab := {|mytab := [0;0;0;0;0] |}.

SearchPattern (nat -> nat -> bool).

(* Compute Nat.ltb 10 10. *)

Definition changeTab_m : State tab unit :=
  for i = 4 to 0 {{
    changeTab i i
  }}.

Compute runState changeTab_m table.

Lemma dsqd (P : () -> tab -> Prop) :
  {{P tt}} changeTab_m {{P}}.
  Admitted.

(* Compute Nat.ltb 3 1. *)

Fixpoint init_table_aux (timeout : nat) (m : nat) : State tab unit :=
  match timeout with
    | 0 => state_pure tt
    | S ti' =>  if (Nat.ltb 4 m) then state_pure tt
                else changeTab m m;; 
                      init_table_aux ti' (S m)
  end.

Definition init_table (timeout m : nat) : State tab unit :=
  init_table_aux timeout m.

Lemma initPEntry (tm m : nat):
  {{fun (s : tab)=> True}} init_table tm m {{fun _ s => True}}.
  Proof.
  unfold init_table.
  unfold init_table_aux.
  assert (Hsize : tm + m >= tm) by omega.
  revert Hsize.
  revert m.
  generalize tm.
  induction tm0.
  + intros.
    eapply weaken.
    eapply ret.
    simpl.
    auto.
  + intros.
    