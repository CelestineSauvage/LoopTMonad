(* Require Import Arith. *)
(* Require Import List. *)
Require Import Program.

Module Monad.

Set Implicit Arguments.

Import Notations.
(* Import Arith. *)

Local Notation "f ∘ g" := (fun x => f (g x)) (at level 40, left associativity).

Class Monad (m: Type -> Type) : Type :=
{ return_ : forall {A}, A -> m A;
  bind: forall {A}, m A -> forall {B}, (A -> m B) -> m B
}.

Notation "a >>= f" := (bind a f) (at level 50, left associativity).

Hint Unfold bind return_ : monad_db.

Class Monad_Correct (m : Type -> Type) `{M : Monad m} := {
  bind_right_unit: forall A (a: m A), a = a >>= return_;
  bind_left_unit: forall A (a: A) B (f: A -> m B),
             f a = return_ a >>= f;
  bind_associativity: forall A (ma: m A) B f C (g: B -> m C),
                 bind ma (fun  x=> f x >>= g) = (ma >>= f) >>= g
}.

Check Monad_Correct.

Arguments Monad m : assert.
Arguments Monad_Correct m [M] : rename.

Section monadic_functions.
 Variable m : Type -> Type. 
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
Notation "'perf' a <- e ; c" := (e >>= (fun  a => c)) (at level 60, right associativity).

End monadic_functions.

Section monadic_loop.

Inductive LoopT m c : Type
  := MkLoopT : (forall (r : Type), (c -> m r) -> m r) -> LoopT m c.

Arguments MkLoopT {_} {_} _.

Check MkLoopT.

Definition runLoopT {m c r} : LoopT m c -> (c -> m r) -> m r :=
  fun loop next =>
    match loop with
    | MkLoopT body => body r next
    end.

Arguments runLoopT {_} {_} {_}.

Check runLoopT.

(* pure for Loop *)
Definition loopT_pure {m A} (a : A) : LoopT m A :=
MkLoopT (fun _ cont => cont a).

(* <*> for Loop *)
(* Definition loopT_liftA {m A B} (f1 : LoopT m (A -> B)) (f2 : LoopT m A) : LoopT m B :=
  MkLoopT (fun _ cont => 
    let f' := (fun f => runLoopT f2 (cont ∘ f)) in 
    runLoopT f1 f'). *)

(* >>= for Loop *)
Definition loopT_bind {m A} (x : LoopT m A) {B} (k : A -> LoopT m B) : LoopT m B :=
  MkLoopT (fun _ cont => 
    let f' := (fun a => runLoopT (k a) cont) in 
    runLoopT x f').

(* Monad instance *)
Global Instance loopT_M {m} : Monad (LoopT m) :=
  { return_ := @loopT_pure m;
    bind := @loopT_bind m}.

Instance loopT_Mcorrect {m} : Monad_Correct (LoopT m).
  Proof.
  constructor;intros;simpl; unfold loopT_bind; unfold loopT_pure; simpl; unfold runLoopT. (* permet d'avoir les 3 lois *)
  + case a.
    auto.
  + case (f a).
    auto.
  + case (ma).
    auto.
  Qed.

Definition loopT_liftT {m} `{Monad m} {A} (x : m A) : LoopT m A :=
 MkLoopT (fun _ cont => x >>= cont). 

Global Instance LoopT_T  : MonadTrans LoopT := 
{ liftT := @loopT_liftT}.

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

(* Record S := {
  myval : nat
}. *)

Record S := {
  my_list : list nat
}.

(* Variable S : Type. *)

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

Global Instance stateM : Monad (State) :=
    { return_ := fun A a s=> (a,s);
      bind := @state_bind}.

Definition modify (f : S -> S) : State unit :=
  get >>= (fun s => put (f s)).

End monadic_loop.

(* End Monad. *)
(* Definition init_val := 0.

Definition init_S := {| myval := init_val|}.

Definition changeState (i : nat) : State unit :=
  modify (fun s => {| myval := s.(myval) + i |}).

Check runState (foreach' 0 5 (fun i => (liftT (changeState i)))) init_S.

(* Voir pour plus tard *)
Notation "'foreach i '=' min 'to' max '{{' body }}" := (foreach' min max (fun i => (body))) (at level 60, i ident, min at level 60, 
max at level 60, body at level 60, right associativity).

(*  format "'[v' '[' 'foreach'  i  '='  min  'to'  max ']' '/' '[' '{{' body '}}' ']' ']'")  *)

(* Compute runState (foreach i = 0 bip 5 {{liftT (changeState i)}} init_S. *)

Compute runState (foreach' 0 5 (fun i => (liftT (changeState i)))) init_S.
 *)


(* Programme qui initialise tous les élements d'une liste *)
Open Scope list_scope.

Notation "'foreach' i '=' min 'to' max '{{' body }}" := (foreach' min max (fun i => (body))) (at level 60, i ident, min at level 60, 
max at level 60, body at level 60, right associativity).

Definition nth := 10.

Definition init_S := {| my_list := List.repeat 0 nth |}.

Fixpoint set_i_eme (i val : nat) (liste : list nat) : list nat :=
  match liste, i with
    | [], _ => []
    | x::xs, 0 => (val :: xs)
    | x::xs, j =>  x :: (set_i_eme (j-1) val xs)
  end.

Definition changeIemeElement (i val : nat) : State unit :=
  modify (fun s => {| my_list := set_i_eme i val s.(my_list)|}).

Compute runState (foreach i = 0 to nth {{liftT (changeIemeElement i i)}}) init_S.

(* Compute runState (foreach 0 nth (fun i => (liftT (changeIemeElement i i)))) init_S. *)

