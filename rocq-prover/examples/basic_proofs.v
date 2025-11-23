(** Basic Proof Examples - Demonstrating fundamental tactics *)

(** Example 1: Simple reflexivity proof *)
Theorem refl_example : 2 + 2 = 4.
Proof.
  reflexivity.
Qed.

(** Example 2: Using intro and assumption *)
Theorem identity : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  assumption.
Qed.

(** Example 3: Proving implication *)
Theorem modus_ponens : forall (P Q : Prop),
  P -> (P -> Q) -> Q.
Proof.
  intros P Q HP HPQ.
  apply HPQ.
  assumption.
Qed.

(** Example 4: Conjunction introduction *)
Theorem and_intro : forall (P Q : Prop),
  P -> Q -> P /\ Q.
Proof.
  intros P Q HP HQ.
  split.
  - assumption.
  - assumption.
Qed.

(** Example 5: Conjunction elimination *)
Theorem and_elim_left : forall (P Q : Prop),
  P /\ Q -> P.
Proof.
  intros P Q H.
  destruct H as [HP HQ].
  assumption.
Qed.

(** Example 6: Disjunction introduction *)
Theorem or_intro_left : forall (P Q : Prop),
  P -> P \/ Q.
Proof.
  intros P Q HP.
  left.
  assumption.
Qed.

(** Example 7: Simple rewriting *)
Theorem rewrite_example : forall (n m : nat),
  n = m -> n + 0 = m.
Proof.
  intros n m Heq.
  rewrite Heq.
  rewrite <- plus_n_O.
  reflexivity.
Qed.
