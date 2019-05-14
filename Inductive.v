Inductive ieven : nat -> Prop :=
| iev0 : ieven 0
| iev2 : forall n, ieven n -> ieven (S (S n)).

Fixpoint even (n:nat) : bool :=
match n with
0 => true
| S p => negb (even p) end.

Lemma ieven_even :
forall x, ieven x -> even x = true.
intros x H.