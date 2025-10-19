(** Rewriting Proof Examples *)

Theorem rewrite_ex1 : forall n m, n = m -> n + n = m + m.
Proof.
  intros n m H.
  rewrite H.
  reflexivity.
Qed.

Theorem rewrite_ex2 : forall n, n + 0 = 0 + n.
Proof.
  intro n.
  rewrite <- plus_n_O.
  rewrite -> plus_O_n.
  reflexivity.
Qed.
