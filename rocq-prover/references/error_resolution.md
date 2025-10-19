# Error Resolution Guide for Rocq/Coq

Systematic strategies for resolving common Rocq/Coq compilation and proof errors.

## Table of Contents

1. [Unification Errors](#unification-errors)
2. [Tactic Failures](#tactic-failures)
3. [Type Errors](#type-errors)
4. [Universe Errors](#universe-errors)
5. [Incomplete Proofs](#incomplete-proofs)
6. [Compilation Errors](#compilation-errors)

---

## Unification Errors

### Error: "Unable to unify X with Y"

**What it means:** Rocq cannot prove that two types or terms are equal.

**Common causes:**
1. Terms are not definitionally equal
2. Missing simplification or computation
3. Wrong rewrite direction
4. Type mismatch

**Resolution strategies:**

**Strategy 1: Simplify first**
```coq
(* Before *)
rewrite H.  (* Fails *)

(* After *)
simpl.      (* Simplify goal *)
rewrite H.  (* May now succeed *)
```

**Strategy 2: Check types**
```coq
(* Use Check to verify types match *)
Check term1.
Check term2.
```

**Strategy 3: Unfold definitions**
```coq
(* Unfold custom definitions *)
unfold my_definition.
simpl.
```

**Strategy 4: Rewrite direction**
```coq
(* Try opposite direction *)
rewrite <- H.  (* Instead of rewrite H *)
```

### Error: "Cannot infer X"

**What it means:** Rocq cannot automatically determine a type or value.

**Resolution:**
```coq
(* Provide explicit type annotations *)
apply (lemma_name : forall n : nat, ...).
```

---

## Tactic Failures

### Error: "Tactic failure: not an inductive product"

**What it means:** Cannot use `intro` because goal is not a forall or implication.

**Resolution:**
```coq
(* Check goal structure first *)
(* If goal is already fully instantiated, use different approach *)

(* Instead of intro *)
reflexivity.  (* or other appropriate tactic *)
```

### Error: "No applicable tactic"

**What it means:** The tactic cannot make progress on this goal.

**Resolution strategies:**

**Strategy 1: Check goal structure**
```coq
(* Print current goal *)
Show.
```

**Strategy 2: Try alternative tactics**
```coq
(* If apply fails, try *)
- refine   (* Partial application *)
- exact    (* Exact term *)
- assumption  (* Use hypothesis directly *)
```

**Strategy 3: Transform goal first**
```coq
simpl.   (* Simplify *)
unfold definition_name.  (* Unfold *)
destruct hypothesis.  (* Case analysis *)
```

### Error: "Tactic failure: The tactic change has nothing to do"

**What it means:** Trying to change goal to something not definitionally equal.

**Resolution:**
```coq
(* Instead of change, use assert or replace *)
replace term1 with term2.
- (* Prove replacement *)
- (* Continue *)
```

---

## Type Errors

### Error: "The term ... has type ... which should be coercible to ..."

**What it means:** Type mismatch - term has wrong type.

**Resolution strategies:**

**Strategy 1: Check term type**
```coq
Check problematic_term.
```

**Strategy 2: Add type annotations**
```coq
(* Explicit type *)
exact (term : expected_type).
```

**Strategy 3: Convert or coerce**
```coq
(* Use conversion functions *)
apply f_equal.
apply eq_ind.
```

### Error: "The reference ... was not found"

**What it means:** Lemma, definition, or variable name not found.

**Resolution:**

**Strategy 1: Check spelling**
```coq
(* Common misspellings *)
plus_n_O  (* Not plus_n_0 *)
```

**Strategy 2: Search for similar names**
```coq
SearchAbout plus.  (* Find related lemmas *)
```

**Strategy 3: Import required modules**
```coq
Require Import Arith.
Require Import Lia.
```

---

## Universe Errors

### Error: "Universe inconsistency"

**What it means:** Universe level constraints are violated.

**Resolution strategies:**

**Strategy 1: Use Polymorphic**
```coq
(* Make definition universe polymorphic *)
Polymorphic Definition my_def := ...
```

**Strategy 2: Check universe constraints**
```coq
Print Universes.
```

**Strategy 3: Avoid circular dependencies**
```coq
(* Don't create types that depend on themselves in incompatible ways *)
(* Redesign the definition structure *)
```

### Error: "Large non-propositional inductive types"

**What it means:** Trying to eliminate from Type to Prop incorrectly.

**Resolution:**
```coq
(* Use Set instead of Prop *)
Inductive my_type : Set := ...

(* Or redesign to avoid large elimination *)
```

---

## Incomplete Proofs

### Error: "Error: Proof is not complete"

**What it means:** Proof has unsolved subgoals or uses Admitted.

**Resolution:**

**Strategy 1: Check for remaining subgoals**
```coq
Show.  (* Display remaining subgoals *)
```

**Strategy 2: Find admits**
```coq
(* Use find_admits.py script *)
python scripts/find_admits.py file.v
```

**Strategy 3: Complete all branches**
```coq
(* After destruct or induction, handle all cases *)
destruct n.
- (* Case 1 - MUST complete *)
- (* Case 2 - MUST complete *)
```

**Strategy 4: Replace Admitted with Qed**
```coq
(* Before *)
Proof.
  (* ... *)
Admitted.

(* After *)
Proof.
  (* ... complete proof *)
Qed.
```

### Error: "No more subgoals but non-instantiated existential variables"

**What it means:** Existential variables (created by eauto, etc.) not instantiated.

**Resolution:**
```coq
(* Use concrete tactics instead of eauto *)
(* Or provide explicit instantiations *)
instantiate (1 := concrete_term).
```

---

## Compilation Errors

### Error: "File ... not found"

**What it means:** Required file or module cannot be located.

**Resolution:**

**Strategy 1: Check file path**
```coq
(* Ensure file exists *)
Require Import MyModule.  (* Must be MyModule.v in load path *)
```

**Strategy 2: Add to load path**
```coq
(* In _CoqProject *)
-R path/to/theories LogicalName
```

**Strategy 3: Compile dependencies first**
```bash
# Compile required files before this one
coqc dependency.v
coqc main.v
```

### Error: "Syntax error"

**What it means:** Invalid Rocq/Coq syntax.

**Resolution:**

**Strategy 1: Check for common syntax issues**
```coq
(* Missing period *)
Theorem name : statement.  (* Needs period *)

(* Missing Proof/Qed *)
Theorem name : statement.
Proof.
  (* tactics *)
Qed.  (* Must end with Qed *)

(* Wrong comment syntax *)
(* This is correct *)
// This is wrong
```

**Strategy 2: Check parentheses and brackets**
```coq
(* Balanced parens *)
forall (n : nat), (n = n)  (* OK *)
forall (n : nat), n = n)   (* Syntax error *)
```

### Error: "Anomaly: Uncaught exception"

**What it means:** Internal Rocq error (bug).

**Resolution:**

**Strategy 1: Simplify to minimal example**
```coq
(* Reduce proof to minimal failing case *)
(* Report to Coq bug tracker if repeatable *)
```

**Strategy 2: Try different tactic sequence**
```coq
(* Avoid specific tactic combination that triggers anomaly *)
```

**Strategy 3: Update Rocq/Coq**
```bash
(* May be fixed in newer version *)
```

---

## Debugging Workflow

### Systematic Debugging Process

1. **Identify exact error location**
   ```bash
   python scripts/verify_proof.py file.v
   ```

2. **Read error message carefully**
   - Note line number
   - Note exact error text
   - Note any suggested fixes

3. **Classify error type**
   - Use this guide's categories

4. **Apply appropriate strategy**
   - Try strategies in order
   - Test after each attempt

5. **Verify fix**
   ```bash
   python scripts/verify_proof.py file.v
   ```

6. **Check for new errors**
   - Fixing one error may reveal others
   - Repeat process

### Debugging Tactics

**Display current state:**
```coq
Show.              (* Current goal *)
Show Proof.        (* Proof term so far *)
Show Existentials. (* Existential variables *)
```

**Check types:**
```coq
Check term.
Check (hypothesis : type).
```

**Search for help:**
```coq
SearchAbout concept.
Search pattern.
```

---

## Prevention Strategies

### 1. Compile Frequently

```bash
(* After every significant change *)
python scripts/verify_proof.py file.v
```

**Why:** Catch errors early before they cascade.

### 2. Use Descriptive Names

```coq
(* Good *)
intro n.
intros n m Heq.

(* Bad *)
intros.  (* Auto-generated names are cryptic *)
```

**Why:** Easier to debug when names are meaningful.

### 3. Keep Proofs Simple

```coq
(* Break complex proofs into lemmas *)
Lemma helper1 : ...
Lemma helper2 : ...
Theorem main : ... (* Uses helper1, helper2 *)
```

**Why:** Smaller proofs easier to debug.

### 4. Use Type Annotations

```coq
(* Explicit types help catch errors early *)
Definition f (n : nat) : nat := n + 1.
```

**Why:** Type errors caught at definition, not use.

### 5. Test Incrementally

```coq
(* Complete each branch before moving on *)
destruct n.
- (* Complete this case fully *)
  (* Test compilation *)
- (* Then complete this case *)
```

**Why:** Isolates which case causes problems.

---

## Common Error Patterns

### Pattern 1: Missing Simplification

**Error:** "Unable to unify n + 0 with n"

**Fix:**
```coq
rewrite <- plus_n_O.  (* Need lemma about n + 0 *)
```

### Pattern 2: Wrong Rewrite Direction

**Error:** "Unable to unify after rewrite"

**Fix:**
```coq
rewrite <- H.  (* Try opposite direction *)
```

### Pattern 3: Missing Import

**Error:** "Reference lia not found"

**Fix:**
```coq
Require Import Lia.
```

### Pattern 4: Incomplete Induction

**Error:** "Proof incomplete"

**Fix:**
```coq
(* Handle ALL cases *)
induction n.
- (* n = 0 - complete this *)
- (* n = S n' - complete this too *)
```

### Pattern 5: Type Mismatch

**Error:** "should be coercible to"

**Fix:**
```coq
(* Check types match *)
Check term1.  (* : nat *)
Check term2.  (* : nat -> nat *)
(* These don't match - fix the term *)
```

---

## Emergency Tactics

When completely stuck:

1. **Start fresh in new file**
   ```bash
   python scripts/new_proof.py fresh_attempt
   ```

2. **Search for similar proofs**
   ```coq
   SearchAbout similar_concept.
   ```

3. **Ask for goal state**
   ```coq
   Show.
   ```

4. **Try brute automation**
   ```coq
   auto.
   tauto.
   lia.
   intuition.
   ```

5. **Break into smaller pieces**
   ```coq
   assert (helper : ...).
   ```

6. **Consult documentation**
   - Read tactics_library.md
   - Check Coq reference manual
   - Search Coq standard library
