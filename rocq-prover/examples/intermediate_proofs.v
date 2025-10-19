(** Intermediate Proof Examples - Working with lists, induction, and lemmas *)

Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Lia.

(** Example 1: List length and append *)

Theorem app_length : forall A (l1 l2 : list A),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros A l1 l2.
  induction l1 as [| x xs IHxs].
  - (* Base case: l1 = [] *)
    simpl.
    reflexivity.
  - (* Inductive case: l1 = x :: xs *)
    simpl.
    rewrite IHxs.
    reflexivity.
Qed.

(** Example 2: List reversal - non-trivial proof *)

Lemma rev_app_distr : forall A (l1 l2 : list A),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros A l1 l2.
  induction l1 as [| x xs IHxs].
  - (* Base case: l1 = [] *)
    simpl.
    rewrite app_nil_r.
    reflexivity.
  - (* Inductive case: l1 = x :: xs *)
    simpl.
    rewrite IHxs.
    rewrite app_assoc.
    reflexivity.
Qed.

Theorem rev_involutive : forall A (l : list A),
  rev (rev l) = l.
Proof.
  intros A l.
  induction l as [| x xs IHxs].
  - (* Base case: l = [] *)
    simpl.
    reflexivity.
  - (* Inductive case: l = x :: xs *)
    simpl.
    rewrite rev_app_distr.
    simpl.
    rewrite IHxs.
    reflexivity.
Qed.


(** Example 3: Arithmetic properties requiring helper lemmas *)

Lemma mult_n_O : forall n,
  n * 0 = 0.
Proof.
  intro n.
  induction n as [| n' IHn'].
  - (* Base case *)
    simpl.
    reflexivity.
  - (* Inductive case *)
    simpl.
    exact IHn'.
Qed.

Lemma mult_n_Sm : forall n m,
  n * S m = n + n * m.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - (* Base case *)
    simpl.
    reflexivity.
  - (* Inductive case *)
    simpl.
    rewrite IHn'.
    lia.
Qed.

Theorem mult_comm : forall n m,
  n * m = m * n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - (* Base case: n = 0 *)
    simpl.
    rewrite mult_n_O.
    reflexivity.
  - (* Inductive case: n = S n' *)
    simpl.
    rewrite IHn'.
    rewrite mult_n_Sm.
    reflexivity.
Qed.


(** Example 4: Working with custom inductive predicates *)

Inductive even : nat -> Prop :=
| even_0 : even 0
| even_SS : forall n, even n -> even (S (S n)).

Lemma even_2 : even 2.
Proof.
  apply even_SS.
  apply even_0.
Qed.

Lemma even_4 : even 4.
Proof.
  apply even_SS.
  apply even_2.
Qed.

(** Inversion on inductive predicates *)
Lemma even_inv : forall n,
  even (S (S n)) -> even n.
Proof.
  intros n H.
  inversion H.
  assumption.
Qed.

(** Example proving non-membership *)
Lemma not_even_1 : ~ even 1.
Proof.
  intro H.
  inversion H.
Qed.

Lemma not_even_3 : ~ even 3.
Proof.
  intro H.
  inversion H.
  inversion H1.
Qed.


(** Example 5: Proof using assert for intermediate goals *)

Theorem square_expansion : forall n,
  (n + 1) * (n + 1) = n * n + 2 * n + 1.
Proof.
  intro n.
  assert (H1: (n + 1) * (n + 1) = (n + 1) * n + (n + 1) * 1).
  { lia. }
  rewrite H1.
  assert (H2: (n + 1) * n = n * n + n).
  { lia. }
  rewrite H2.
  assert (H3: (n + 1) * 1 = n + 1).
  { lia. }
  rewrite H3.
  lia.
Qed.


(** Example 6: Existential quantification *)

Theorem exists_witness : forall n,
  n > 0 -> exists m, n = S m.
Proof.
  intros n Hn.
  destruct n as [| n'].
  - (* n = 0 - contradicts Hn *)
    lia.
  - (* n = S n' *)
    exists n'.
    reflexivity.
Qed.

Theorem double_is_even : forall m,
  even (m + m).
Proof.
  intro m.
  induction m as [| m' IHm'].
  - (* m = 0 *)
    simpl.
    apply even_0.
  - (* m = S m' *)
    simpl.
    rewrite <- plus_n_Sm.
    apply even_SS.
    exact IHm'.
Qed.

Theorem use_exists : forall n,
  (exists m, m + m = n) -> even n.
Proof.
  intros n [m Hm].
  rewrite <- Hm.
  apply double_is_even.
Qed.


(** Example 7: Case analysis on bool *)

Definition is_zero (n : nat) : bool :=
  match n with
  | 0 => true
  | S _ => false
  end.

Lemma is_zero_correct : forall n,
  is_zero n = true <-> n = 0.
Proof.
  intro n.
  split.
  - (* -> *)
    destruct n as [| n'].
    + intro H. reflexivity.
    + intro H. simpl in H. discriminate H.
  - (* <- *)
    intro H.
    rewrite H.
    simpl.
    reflexivity.
Qed.


(** Example 8: Using remember to simplify complex terms *)

Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | S (S n' as n'') => fib n'' + fib n'
  end.

Lemma fib_2 : fib 2 = 1.
Proof.
  simpl.
  reflexivity.
Qed.

Lemma fib_3 : fib 3 = 2.
Proof.
  simpl.
  reflexivity.
Qed.


(** Example 9: Lemma decomposition pattern *)

(** Helper: relationship between length and nil *)
Lemma length_zero_iff_nil : forall A (l : list A),
  length l = 0 <-> l = [].
Proof.
  intros A l.
  split.
  - (* -> *)
    destruct l as [| x xs].
    + intro H. reflexivity.
    + intro H. simpl in H. discriminate H.
  - (* <- *)
    intro H.
    rewrite H.
    simpl.
    reflexivity.
Qed.

(** Using the helper lemma *)
Theorem empty_rev : forall A (l : list A),
  length l = 0 -> rev l = [].
Proof.
  intros A l H.
  apply length_zero_iff_nil in H.
  rewrite H.
  simpl.
  reflexivity.
Qed.


(** Example 10: Proof by contradiction *)

Lemma succ_neq_zero : forall n,
  S n <> 0.
Proof.
  intros n H.
  discriminate H.
Qed.

Theorem contrapositive_example : forall n m,
  n <> m -> S n <> S m.
Proof.
  intros n m Hneq Hcontra.
  apply Hneq.
  injection Hcontra as H.
  exact H.
Qed.
