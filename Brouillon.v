Require Import Arith.

Lemma blop : 
  forall n, fun (a : nat) => (Nat.add n 1) -> (Nat.add n 1).