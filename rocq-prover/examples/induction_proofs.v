(** Induction Proof Examples - Demonstrating structural induction *)

Require Import Arith.
Require Import Lia.

(** Example 1: Basic induction on natural numbers *)
Theorem plus_n_O : forall n : nat, n + 0 = n.
Proof.
  intro n.
  induction n as [| n' IHn'].
  - (* Base case: n = 0 *)
    simpl.
    reflexivity.
  - (* Inductive case: n = S n' *)
    simpl.
    rewrite IHn'.  (* Apply induction hypothesis *)
    reflexivity.
Qed.

(** Example 2: Associativity of addition *)
Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - (* Base case: n = 0 *)
    simpl.
    reflexivity.
  - (* Inductive case: n = S n' *)
    simpl.
    rewrite IHn'.
    reflexivity.
Qed.

(** Helper lemma: m + 0 = m *)
Lemma plus_0_r : forall m : nat, m + 0 = m.
Proof.
  intro m.
  induction m as [| m' IHm'].
  - (* Base case: m = 0 *)
    simpl.
    reflexivity.
  - (* Inductive case: m = S m' *)
    simpl.
    rewrite IHm'.
    reflexivity.
Qed.

(** Helper lemma: S (m + n) = m + S n *)
Lemma plus_n_Sm : forall n m : nat, S (m + n) = m + S n.
Proof.
  intros n m.
  induction m as [| m' IHm'].
  - (* Base case: m = 0 *)
    simpl.
    reflexivity.
  - (* Inductive case: m = S m' *)
    simpl.
    rewrite IHm'.
    reflexivity.
Qed.

(** Example 3: Commutativity of addition - complete proof without automation *)
Theorem plus_comm : forall n m : nat, n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - (* Base case: n = 0 *)
    (* Goal: 0 + m = m + 0 *)
    simpl.
    (* Goal: m = m + 0 *)
    rewrite plus_0_r.
    (* Goal: m = m *)
    reflexivity.
  - (* Inductive case: n = S n' *)
    (* IHn' : n' + m = m + n' *)
    (* Goal: S n' + m = m + S n' *)
    simpl.
    (* Goal: S (n' + m) = m + S n' *)
    rewrite IHn'.
    (* Goal: S (m + n') = m + S n' *)
    rewrite <- plus_n_Sm.
    (* Goal: S (m + n') = S (m + n') *)
    reflexivity.
Qed.

(** Example 4: Multiplication distributes over addition *)
Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = n * p + m * p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - (* Base case: n = 0 *)
    simpl.
    reflexivity.
  - (* Inductive case: n = S n' *)
    simpl.
    rewrite IHn'.
    rewrite plus_assoc.
    reflexivity.
Qed.

(** Example 5: Simple property using previous lemmas *)
Theorem plus_n_Sm_alt : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - (* Base case: n = 0 *)
    simpl.
    reflexivity.
  - (* Inductive case: n = S n' *)
    simpl.
    rewrite IHn'.
    reflexivity.
Qed.
