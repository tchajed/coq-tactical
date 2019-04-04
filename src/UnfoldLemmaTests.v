From Tactical Require Import UnfoldLemma.
Require Import Arith.

Definition complicated_definition a b := a + b.

Definition unfold1 a b := unfold_lemma (complicated_definition a b).

Lemma unfold1' a b : complicated_definition a b = a + b.
Proof. reflexivity. Qed.

Theorem use_unfold1 : forall a b, complicated_definition a b = complicated_definition b a.
Proof.
  intros.
  rewrite ?unfold1.
  rewrite (unfold1 b a).
  apply Nat.add_comm.
Qed.

Theorem use_unfold1' : forall a b, complicated_definition a b = complicated_definition b a.
Proof.
  intros.
  rewrite ?unfold1'.
  rewrite (unfold1' b a).
  apply Nat.add_comm.
Qed.

Definition complicated_prop a b := a + 1 = b + 2.

Definition unfold2 a b := unfold_lemma (complicated_prop a b).

Theorem use_unfold2 : complicated_prop 3 2.
Proof.
  rewrite unfold2.
  progress simpl.
  reflexivity.
Qed.
