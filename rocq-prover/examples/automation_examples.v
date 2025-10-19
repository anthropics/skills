(** Automation Examples - Using auto, lia, tauto *)

Require Import Lia.

(** Example 1: Using auto for simple goals *)
Theorem auto_ex : forall P Q R, P -> (P -> Q) -> (Q -> R) -> R.
Proof.
  auto.
Qed.

(** Example 2: Using lia for arithmetic *)
Theorem lia_ex : forall n m, n < m -> n + 1 <= m.
Proof.
  lia.
Qed.

(** Example 3: Using tauto for propositional logic *)
Theorem tauto_ex : forall P Q, P /\ Q -> Q /\ P.
Proof.
  tauto.
Qed.
