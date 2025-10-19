(** Test file with various incomplete proofs - FOR TESTING ONLY *)

(** This should be flagged - Admitted *)
Theorem incomplete1 : forall (n : nat), n + 0 = n.
Proof.
  intro n.
Admitted.

(** This should be flagged - admit tactic *)
Theorem incomplete2 : forall (n m : nat), n + m = m + n.
Proof.
  intros n m.
  admit.
Qed.

(** This should be flagged - Axiom *)
Axiom excluded_middle : forall (P : Prop), P \/ ~P.

(** This is complete - should NOT be flagged *)
Theorem complete : 2 + 2 = 4.
Proof.
  reflexivity.
Qed.
