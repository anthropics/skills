# Rocq/Coq Tactics Library Reference

Complete reference for Rocq (formerly Coq) proof tactics organized by category.

## Table of Contents

1. [Basic Tactics](#basic-tactics)
2. [Rewriting and Simplification](#rewriting-and-simplification)
3. [Destruction and Case Analysis](#destruction-and-case-analysis)
4. [Construction](#construction)
5. [Automation](#automation)
6. [Search and Discovery](#search-and-discovery)
7. [Tactical Combinators](#tactical-combinators)
8. [Advanced Tactics](#advanced-tactics)

---

## Basic Tactics

### `intro` / `intros`

**Purpose:** Introduce hypotheses from the goal into the context.

**Usage:**
```coq
intro x.        (* Introduce one variable, name it x *)
intros.         (* Introduce all possible variables with auto-generated names *)
intros x y z.   (* Introduce three variables with specific names *)
```

**Example:**
```coq
Theorem example : forall (n m : nat), n = m -> n + 0 = m.
Proof.
  intros n m Heq.  (* Now n, m, and Heq are in context *)
Qed.
```

### `apply`

**Purpose:** Apply a theorem or hypothesis to solve the current goal.

**Usage:**
```coq
apply lemma_name.    (* Apply a lemma to current goal *)
apply H.             (* Apply hypothesis H *)
```

**Example:**
```coq
Lemma helper : forall n, n = n.
Proof. intro. reflexivity. Qed.

Theorem use_helper : forall m, m = m.
Proof.
  intro m.
  apply helper.  (* Solves the goal using helper *)
Qed.
```

### `exact`

**Purpose:** Provide the exact term that proves the goal.

**Usage:**
```coq
exact term.
```

**Example:**
```coq
Theorem exact_example : forall (n : nat), n = n.
Proof.
  intro n.
  exact (eq_refl n).  (* Provide exact proof term *)
Qed.
```

### `assumption`

**Purpose:** Solve the goal using a hypothesis that exactly matches.

**Usage:**
```coq
assumption.
```

**Example:**
```coq
Theorem assumption_example : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  assumption.  (* HP : P matches goal P *)
Qed.
```

### `reflexivity`

**Purpose:** Prove equality when both sides are definitionally equal.

**Usage:**
```coq
reflexivity.
```

**Example:**
```coq
Theorem refl : 2 + 2 = 4.
Proof.
  reflexivity.  (* Computation shows they're equal *)
Qed.
```

---

## Rewriting and Simplification

### `rewrite`

**Purpose:** Replace part of the goal using an equality.

**Usage:**
```coq
rewrite H.          (* Rewrite left-to-right using H : A = B *)
rewrite <- H.       (* Rewrite right-to-left *)
rewrite H1, H2.     (* Multiple rewrites *)
rewrite H in H2.    (* Rewrite in hypothesis H2 *)
```

**Example:**
```coq
Theorem rewrite_ex : forall n m, n = m -> n + 0 = m.
Proof.
  intros n m Heq.
  rewrite Heq.      (* Replace n with m *)
  rewrite <- plus_n_O.  (* n + 0 = n *)
  reflexivity.
Qed.
```

### `simpl`

**Purpose:** Simplify the goal by performing computation.

**Usage:**
```coq
simpl.             (* Simplify entire goal *)
simpl in H.        (* Simplify in hypothesis H *)
```

**Example:**
```coq
Theorem simpl_ex : 2 + 2 = 4.
Proof.
  simpl.  (* Reduces to 4 = 4 *)
  reflexivity.
Qed.
```

### `unfold`

**Purpose:** Unfold a definition to see its underlying form.

**Usage:**
```coq
unfold definition_name.
unfold def1, def2.         (* Multiple unfolds *)
unfold def in H.           (* Unfold in hypothesis *)
```

**Example:**
```coq
Definition double (n : nat) := n + n.

Theorem unfold_ex : double 2 = 4.
Proof.
  unfold double.  (* Expands to 2 + 2 = 4 *)
  simpl.
  reflexivity.
Qed.
```

### `replace`

**Purpose:** Replace a term with another, generating a subgoal to prove they're equal.

**Usage:**
```coq
replace A with B.          (* Replace A with B *)
replace A with B by tactic. (* Prove equality with tactic *)
```

**Example:**
```coq
Theorem replace_ex : forall n, n + 0 = 0 + n.
Proof.
  intro n.
  replace (n + 0) with n.
  - replace (0 + n) with n.
    + reflexivity.
    + apply plus_O_n.
  - apply plus_n_O.
Qed.
```

### `subst`

**Purpose:** Substitute all occurrences of a variable using an equality hypothesis.

**Usage:**
```coq
subst.        (* Substitute all equalities of form x = ... *)
subst x.      (* Substitute only x *)
```

**Example:**
```coq
Theorem subst_ex : forall x y, x = y -> x + x = y + y.
Proof.
  intros x y Heq.
  subst.  (* Replace all x with y *)
  reflexivity.
Qed.
```

---

## Destruction and Case Analysis

### `destruct`

**Purpose:** Perform case analysis on a term.

**Usage:**
```coq
destruct x.                 (* Case analysis on x *)
destruct x as [  ].        (* With naming patterns *)
destruct x eqn:Heq.        (* Remember the equality *)
```

**Example:**
```coq
Theorem destruct_bool : forall b : bool, b = true \/ b = false.
Proof.
  intro b.
  destruct b.
  - left. reflexivity.   (* b = true *)
  - right. reflexivity.  (* b = false *)
Qed.
```

### `induction`

**Purpose:** Proof by induction on an inductive type.

**Usage:**
```coq
induction n.                (* Induction on n *)
induction n as [| n' IHn']. (* With naming *)
induction n using scheme.   (* Custom induction principle *)
```

**Example:**
```coq
Theorem plus_n_O : forall n, n + 0 = n.
Proof.
  induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *)
    simpl.
    rewrite IHn'.  (* Use induction hypothesis *)
    reflexivity.
Qed.
```

### `inversion`

**Purpose:** Analyze an inductive hypothesis, deriving all consequences.

**Usage:**
```coq
inversion H.          (* Invert hypothesis H *)
inversion H as [  ].  (* With naming pattern *)
inversion H; subst.   (* Common: invert and substitute *)
```

**Example:**
```coq
Inductive even : nat -> Prop :=
| even_0 : even 0
| even_SS : forall n, even n -> even (S (S n)).

Theorem inversion_ex : even 2 -> even 0.
Proof.
  intro H.
  inversion H.  (* Derives: H1 : even 0 *)
  assumption.
Qed.
```

### `case`

**Purpose:** Case analysis (like destruct but preserves dependencies).

**Usage:**
```coq
case term.
```

---

## Construction

### `split`

**Purpose:** Prove a conjunction by proving both parts.

**Usage:**
```coq
split.  (* Splits A /\ B into two subgoals *)
```

**Example:**
```coq
Theorem split_ex : forall P Q, P -> Q -> P /\ Q.
Proof.
  intros P Q HP HQ.
  split.
  - assumption.  (* Prove P *)
  - assumption.  (* Prove Q *)
Qed.
```

### `exists`

**Purpose:** Provide a witness for an existential quantification.

**Usage:**
```coq
exists term.  (* Provide witness *)
```

**Example:**
```coq
Theorem exists_ex : exists n : nat, n + 2 = 5.
Proof.
  exists 3.  (* Witness is 3 *)
  reflexivity.
Qed.
```

### `left` / `right`

**Purpose:** Prove a disjunction by choosing a side.

**Usage:**
```coq
left.   (* Prove A in goal A \/ B *)
right.  (* Prove B in goal A \/ B *)
```

**Example:**
```coq
Theorem left_ex : forall P Q, P -> P \/ Q.
Proof.
  intros P Q HP.
  left.  (* Choose to prove P *)
  assumption.
Qed.
```

### `constructor`

**Purpose:** Apply the appropriate constructor of an inductive type.

**Usage:**
```coq
constructor.    (* Try all constructors *)
constructor n.  (* Apply nth constructor *)
```

**Example:**
```coq
Theorem constructor_ex : 2 + 2 = 4 /\ 3 + 3 = 6.
Proof.
  constructor.  (* Same as split for /\ *)
  - reflexivity.
  - reflexivity.
Qed.
```

---

## Automation

### `auto`

**Purpose:** Automatic proof search using a database of hints.

**Usage:**
```coq
auto.            (* Default hint database *)
auto with db.    (* Use specific database *)
auto 5.          (* Search depth 5 *)
```

**Example:**
```coq
Theorem auto_ex : forall P Q R, P -> (P -> Q) -> (Q -> R) -> R.
Proof.
  auto.  (* Automatically finds proof *)
Qed.
```

### `tauto`

**Purpose:** Solve propositional tautologies.

**Usage:**
```coq
tauto.
```

**Example:**
```coq
Theorem tauto_ex : forall P Q, P /\ Q -> Q /\ P.
Proof.
  tauto.  (* Propositional reasoning *)
Qed.
```

### `lia`

**Purpose:** Linear integer arithmetic solver (formerly omega).

**Usage:**
```coq
lia.
```

**Example:**
```coq
Require Import Lia.

Theorem lia_ex : forall n m, n < m -> n + 1 <= m.
Proof.
  lia.  (* Solves linear arithmetic *)
Qed.
```

### `omega`

**Purpose:** Deprecated - use `lia` instead. Still works in older Coq versions.

### `ring`

**Purpose:** Solve ring equalities (commutative rings).

**Usage:**
```coq
ring.
```

**Example:**
```coq
Require Import Ring.

Theorem ring_ex : forall n m : nat, n + m = m + n.
Proof.
  intros.
  ring.  (* Proves using ring properties *)
Qed.
```

### `field`

**Purpose:** Solve field equalities (like ring but for fields).

**Usage:**
```coq
field.
```

---

## Search and Discovery

### `SearchAbout`

**Purpose:** Find theorems mentioning a specific term.

**Usage:**
```coq
SearchAbout term.
SearchAbout (pattern).
```

**Example:**
```coq
SearchAbout plus.      (* Find theorems about addition *)
SearchAbout (_ + 0).   (* Find theorems matching pattern *)
```

### `Search`

**Purpose:** Search for theorems by type pattern.

**Usage:**
```coq
Search pattern.
Search (?n + 0 = ?n).
```

### `SearchPattern`

**Purpose:** Search for exact pattern matches.

**Usage:**
```coq
SearchPattern (_ + _ = _ + _).
```

### `Check`

**Purpose:** Display the type of a term.

**Usage:**
```coq
Check term.
Check (2 + 2).  (* nat *)
```

### `Print`

**Purpose:** Print the definition of a constant.

**Usage:**
```coq
Print definition_name.
```

---

## Tactical Combinators

### Sequencing (`;`)

**Purpose:** Apply a tactic to all subgoals generated by another tactic.

**Usage:**
```coq
tactic1; tactic2.
```

**Example:**
```coq
Theorem seq_ex : (1 = 1) /\ (2 = 2).
Proof.
  split; reflexivity.  (* reflexivity applied to both subgoals *)
Qed.
```

### Branching (`[ | | ]`)

**Purpose:** Apply different tactics to different subgoals.

**Usage:**
```coq
tactic. [ tactic1 | tactic2 | tactic3 ]
```

**Example:**
```coq
Theorem branch_ex : forall b, b = true \/ b = false.
Proof.
  intro b.
  destruct b.
  [ left; reflexivity | right; reflexivity ].
Qed.
```

### Try (`try`)

**Purpose:** Try a tactic, don't fail if it doesn't apply.

**Usage:**
```coq
try tactic.
```

**Example:**
```coq
Theorem try_ex : 2 = 2.
Proof.
  try (apply some_lemma).  (* Won't fail if lemma doesn't exist *)
  reflexivity.
Qed.
```

### Repeat (`repeat`)

**Purpose:** Repeat a tactic until it fails.

**Usage:**
```coq
repeat tactic.
```

**Example:**
```coq
Theorem repeat_ex : forall n m p, n = m -> m = p -> n = p.
Proof.
  intros.
  repeat (rewrite H || rewrite H0).  (* Keep rewriting *)
  reflexivity.
Qed.
```

### Alternative (`||`)

**Purpose:** Try first tactic, if it fails try second.

**Usage:**
```coq
tactic1 || tactic2.
```

---

## Advanced Tactics

### `assert`

**Purpose:** Introduce a new hypothesis by proving it as a subgoal.

**Usage:**
```coq
assert (H : statement).
```

**Example:**
```coq
Theorem assert_ex : forall n, n + 0 = n.
Proof.
  intro n.
  assert (H : 0 + n = n).
  - apply plus_O_n.
  - (* Continue with H available *)
Admitted.
```

### `generalize`

**Purpose:** Move a term from the goal into a universally quantified hypothesis.

**Usage:**
```coq
generalize term.
generalize dependent x.
```

### `remember`

**Purpose:** Give a name to a complex term.

**Usage:**
```coq
remember term as x.
remember (complex expression) as y eqn:Heq.
```

### `specialize`

**Purpose:** Instantiate a universally quantified hypothesis.

**Usage:**
```coq
specialize (H arg1 arg2).
```

**Example:**
```coq
Theorem specialize_ex : (forall n, n = n) -> 5 = 5.
Proof.
  intro H.
  specialize (H 5).  (* H : 5 = 5 *)
  assumption.
Qed.
```

---

## Common Patterns

### Pattern 1: Split and Prove Both

```coq
split; [ tactic1 | tactic2 ].
```

### Pattern 2: Induction with Hypothesis

```coq
induction n as [| n' IHn']; simpl; try (rewrite IHn'); reflexivity.
```

### Pattern 3: Destruct and Substitute

```coq
destruct H as [x Hx]; subst; reflexivity.
```

### Pattern 4: Try Automation, Fall Back

```coq
try auto; try tauto; try lia.
```

---

## Tips

1. **Use bullets** (`-`, `+`, `*`) to organize subgoals
2. **Indent** nested proofs for readability
3. **Name hypotheses** descriptively in intro/destruct patterns
4. **Chain tactics** with `;` when appropriate
5. **Use automation** (auto, tauto, lia) as a first attempt
6. **Break complex proofs** into smaller lemmas

---

## Common Mistakes

1. **Not introducing hypotheses before destruct/induction**
   ```coq
   (* Wrong *)
   destruct n.  (* n not in context yet *)

   (* Right *)
   intro n. destruct n.
   ```

2. **Rewriting in the wrong direction**
   ```coq
   (* If H : a = b and you want to replace b with a *)
   rewrite <- H.  (* Not rewrite H *)
   ```

3. **Forgetting to handle all cases**
   ```coq
   (* After destruct, must handle all branches *)
   destruct b.
   - (* true case *)
   - (* false case - don't forget! *)
   ```

4. **Using the wrong automation tactic**
   - `auto` - logical reasoning
   - `tauto` - propositional logic
   - `lia` - linear arithmetic
   - `ring` - ring equations
   - Don't mix them up!
