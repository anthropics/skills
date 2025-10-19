---
name: rocq-prover
description: Comprehensive toolkit for formal verification using Rocq (formerly Coq). Use this when working with theorem proving, formal proofs, .v files, proof verification, tactics development, or any formal methods work involving Rocq/Coq. Emphasizes complete proof development with zero admits/axioms and systematic proof strategies.
---

# Rocq Prover Skill

## Overview

To work with Rocq (formerly Coq) theorem prover for formal verification, proof development, and mathematical formalization, use this skill. Rocq enables writing machine-checked proofs with absolute correctness guarantees.

**Critical Philosophy: This skill operates under strict standards:**
- ZERO admits, axioms, or aborts are acceptable
- Every proof must terminate with `Qed`
- Compilation must succeed after every change
- Systematic proof strategies over ad-hoc attempts

## When to Use This Skill

Use this skill when:
- Writing or verifying `.v` files (Rocq/Coq source files)
- Developing formal proofs and theorems
- Working with proof tactics and strategies
- Formalizing mathematical theorems
- Verifying software correctness properties
- Debugging proof failures or compilation errors
- Extracting executable code from proofs
- Working with advanced features (HoTT, universe polymorphism, etc.)

## Quick Start

### Verifying a Proof File

To verify a Rocq proof file:

```bash
# Standard compilation
python scripts/verify_proof.py path/to/file.v

# With project-specific flags (HoTT, etc.)
python scripts/verify_proof.py path/to/file.v --project-file _CoqProject

# Interactive mode
python scripts/verify_proof.py path/to/file.v --interactive
```

### Creating a New Proof

To start a new proof development:

```bash
python scripts/new_proof.py my_theorem --template induction
```

Available templates: `simple`, `induction`, `case_analysis`, `rewriting`, `tactical`

## Core Workflow

### 1. Proof Development Cycle

**The fundamental cycle:**

1. **Write proof attempt** - Implement proof using tactics
2. **Compile immediately** - Run `verify_proof.py` to check compilation
3. **Fix errors systematically** - Address failures one by one
4. **Verify completion** - Ensure proof ends with `Qed`, never `Admitted`

**CRITICAL: Never accumulate "edit debt"** - compile after every substantive change. Delayed compilation leads to cascading errors that become extremely difficult to debug.

### 2. Proof Strategy Selection

To select an appropriate proof strategy, analyze the goal structure:

**Decision Tree:**

```
Goal structure → What am I proving?
  ├─ Equality (A = B)?
  │   ├─ Both sides definitionally equal → reflexivity
  │   ├─ Need to rewrite using hypotheses → rewrite, apply
  │   └─ Need computation → simpl, unfold, compute
  │
  ├─ Implication (A → B)?
  │   ├─ Introduce hypothesis → intro, intros
  │   └─ Apply known lemma → apply, exact
  │
  ├─ Conjunction (A ∧ B)?
  │   ├─ Proving → split
  │   └─ Using → destruct
  │
  ├─ Disjunction (A ∨ B)?
  │   ├─ Proving → left or right
  │   └─ Using → destruct
  │
  ├─ Universal quantification (∀ x, P x)?
  │   ├─ Proving → intro
  │   └─ Using → apply, specialize
  │
  ├─ Existential (∃ x, P x)?
  │   ├─ Proving → exists <witness>
  │   └─ Using → destruct
  │
  ├─ Inductive type?
  │   ├─ Structural recursion → induction
  │   ├─ Case analysis needed → destruct
  │   └─ Custom induction principle → induction using
  │
  └─ Complex goal?
      ├─ Decompose into lemmas
      ├─ Try automation (auto, tauto, lia, omega)
      └─ Search for applicable lemmas (SearchAbout, Search)
```

### 3. Systematic Error Resolution

When a proof fails, follow this systematic approach:

**Step 1: Identify the exact error**
```bash
python scripts/verify_proof.py file.v
```

**Step 2: Classify the error type**
- Tactic failure (tactic does not apply)
- Type mismatch (term has wrong type)
- Universe inconsistency (universe level problems)
- Missing hypothesis (assumption not available)
- Incomplete proof (proof has admits/axioms)

**Step 3: Apply appropriate fix strategy**

See `references/error_resolution.md` for comprehensive error-type-specific strategies.

**Step 4: Verify fix immediately**
```bash
python scripts/verify_proof.py file.v
```

### 4. Proof Tactics Reference

**Loading tactics documentation:**

To understand available tactics and their usage, read `references/tactics_library.md` which contains:
- Complete tactics reference organized by category
- Usage examples for each tactic
- Common pitfalls and solutions
- Tactical combinators (`;`, `||`, `repeat`, etc.)

**Quick tactic categories:**
- **Basic:** `intro`, `apply`, `exact`, `assumption`
- **Rewriting:** `rewrite`, `replace`, `subst`, `simpl`, `unfold`
- **Destruction:** `destruct`, `induction`, `case`, `inversion`
- **Construction:** `split`, `exists`, `left`, `right`, `constructor`
- **Automation:** `auto`, `tauto`, `lia`, `omega`, `ring`, `field`
- **Search:** `SearchAbout`, `Search`, `SearchPattern`

## Advanced Features

### Working with HoTT (Homotopy Type Theory)

To work with HoTT libraries:

```bash
# Verify HoTT proof with proper flags
python scripts/verify_proof.py file.v \
  --coq-flags "-R path/to/HoTT/theories HoTT -noinit -indices-matter"

# Or use _CoqProject file
python scripts/verify_proof.py file.v --project-file _CoqProject
```

**HoTT-specific considerations:**
- Universe polymorphism is required (`-indices-matter`)
- Standard library is not loaded (`-noinit`)
- Univalence axiom is available
- Path types replace equality in many contexts

See `references/hott_patterns.md` for HoTT-specific proof patterns.

### Universe Polymorphism

To work with universe polymorphic definitions:

```coq
Polymorphic Definition id {A : Type} (x : A) : A := x.

Polymorphic Lemma id_compose : forall (A B C : Type) (f : A -> B) (g : B -> C) (x : A),
  g (f x) = (fun y => g (f y)) x.
Proof.
  intros. reflexivity.
Qed.
```

**Key points:**
- Use `Polymorphic` keyword for universe polymorphic definitions
- Universes are inferred automatically
- Check universe constraints with `Print Universes`

### Extraction to OCaml/Haskell

To extract executable code from proofs:

```bash
python scripts/extract_code.py file.v --target ocaml --output extracted.ml
```

**Extraction considerations:**
- Proofs are erased (only computational content extracted)
- Some types may need custom extraction rules
- Test extracted code separately from proofs

## Proof Patterns Library

### Pattern 1: Structural Induction

```coq
Lemma example_induction : forall (n : nat), (* property about n *).
Proof.
  intro n.
  induction n as [| n' IHn'].
  - (* Base case: n = 0 *)
    (* prove for 0 *)
  - (* Inductive case: n = S n' *)
    (* IHn' : property holds for n' *)
    (* prove for S n' using IHn' *)
Qed.
```

### Pattern 2: Case Analysis

```coq
Lemma example_destruct : forall (b : bool), (* property about b *).
Proof.
  intro b.
  destruct b.
  - (* Case: b = true *)
    (* prove for true *)
  - (* Case: b = false *)
    (* prove for false *)
Qed.
```

### Pattern 3: Rewriting Chain

```coq
Lemma example_rewrite : forall (a b c : nat),
  a = b -> b = c -> a = c.
Proof.
  intros a b c Hab Hbc.
  rewrite Hab.
  rewrite Hbc.
  reflexivity.
Qed.
```

### Pattern 4: Lemma Decomposition

When facing a complex proof, decompose into smaller lemmas:

```coq
Lemma helper_lemma_1 : (* simpler property 1 *).
Proof.
  (* prove simpler property *)
Qed.

Lemma helper_lemma_2 : (* simpler property 2 *).
Proof.
  (* prove simpler property *)
Qed.

Lemma main_theorem : (* complex property *).
Proof.
  (* use helper_lemma_1 and helper_lemma_2 *)
  apply helper_lemma_1.
  apply helper_lemma_2.
Qed.
```

### Pattern 5: Proof by Contradiction

```coq
Lemma example_contradiction : forall (P : Prop),
  ~ ~ P -> P. (* Only provable with classical logic *)
Proof.
  intros P Hnnp.
  (* This requires classical axioms like excluded middle *)
  (* Without axioms, some propositions are not provable *)
Abort. (* Cannot prove constructively *)
```

## Debugging Failed Proofs

### Common Failure Modes

**1. "Error: Unable to unify X with Y"**

**Cause:** Type mismatch - trying to use a term where the types don't match.

**Solution:**
- Check the types: `Check term.`
- Use `simpl` or `unfold` to normalize types
- Verify hypotheses match what the tactic expects

**2. "Error: No applicable tactic"**

**Cause:** The tactic cannot make progress on the current goal.

**Solution:**
- Examine the goal structure carefully
- Try a different tactic approach
- Check if hypotheses provide what you need
- Use `SearchAbout` to find relevant lemmas

**3. "Error: Proof is incomplete"**

**Cause:** Proof ends with `Admitted` or has unsolved subgoals.

**Solution:**
- Use `Show.` to see remaining subgoals
- Use `admit` temporarily to focus on one subgoal, then replace
- Never leave `Admitted` in final code

**4. "Universe inconsistency"**

**Cause:** Universe level constraints are violated.

**Solution:**
- Use `Polymorphic` for definitions that should work at any universe
- Check `Print Universes` to see constraints
- Avoid circular universe dependencies

### Proof Debugging Scripts

To debug a failing proof:

```bash
# Show detailed error information
python scripts/debug_proof.py file.v --verbose

# Extract the failing goal state
python scripts/debug_proof.py file.v --show-goals

# Check universe constraints
python scripts/debug_proof.py file.v --check-universes
```

## Project Configuration

### _CoqProject Files

For projects with multiple files and dependencies, create a `_CoqProject` file:

```
# Logical paths
-R theories MyProject
-Q vendor/lib ExternalLib

# Options
-arg -w -arg -notation-overridden

# Files (in dependency order)
theories/Basics.v
theories/Induction.v
theories/Advanced.v
```

**Using _CoqProject:**

```bash
# Verify with project configuration
python scripts/verify_proof.py file.v --project-file _CoqProject

# Compile entire project
python scripts/compile_project.py --project-file _CoqProject
```

### Makefile Generation

To generate a Makefile from `_CoqProject`:

```bash
coq_makefile -f _CoqProject -o Makefile
make
```

## Best Practices

### 1. Proof Organization

**DO:**
- Group related definitions and lemmas together
- Put helper lemmas before main theorems
- Use meaningful names that describe what is proven
- Add comments explaining proof strategy for complex proofs
- Organize files by logical topic

**DON'T:**
- Mix unrelated theorems in one file
- Use cryptic names like `lemma1`, `lemma2`
- Leave proofs uncommented when strategy is non-obvious
- Create circular dependencies between files

### 2. Proof Style

**DO:**
- Use bullet points (`-`, `+`, `*`) for subgoals
- Indent subproofs for readability
- Use `Proof.` and `Qed.` explicitly
- Break long tactic sequences into multiple lines
- Use `admit` temporarily during development, but replace before completion

**DON'T:**
- Write proofs as single-line tactic chains
- Mix proof and definition sections confusingly
- Leave `Admitted` in final code
- Use deprecated tactics without good reason

### 3. Compilation Hygiene

**DO:**
- Compile after every significant change
- Fix compilation errors immediately
- Test with clean build (`make clean && make`)
- Verify all dependencies compile

**DON'T:**
- Accumulate multiple errors before compiling
- Assume code works without testing
- Commit code that doesn't compile
- Ignore deprecation warnings

### 4. Performance Considerations

**DO:**
- Use `Qed` for theorems that should be opaque
- Use `Defined` for definitions that need to compute
- Profile slow proofs with `Set Ltac Profiling`
- Cache intermediate results in lemmas

**DON'T:**
- Make everything transparent with `Defined`
- Repeat expensive computations
- Use brute-force automation on large goals
- Inline large proofs repeatedly

## Resources

This skill includes comprehensive reference documentation:

### Reference Files

- **`references/tactics_library.md`** - Complete tactics reference with examples
- **`references/error_resolution.md`** - Systematic error debugging strategies
- **`references/hott_patterns.md`** - HoTT-specific proof patterns
- **`references/standard_library.md`** - Commonly used standard library modules
- **`references/proof_strategies.md`** - Advanced proof strategy patterns

### Example Proofs

- **`examples/basic_proofs.v`** - Simple proofs demonstrating fundamental tactics
- **`examples/induction_proofs.v`** - Structural induction examples on natural numbers
- **`examples/intermediate_proofs.v`** - List proofs with lemma decomposition
- **`examples/rewriting_proofs.v`** - Rewriting and simplification techniques
- **`examples/automation_examples.v`** - Using auto, lia, tauto effectively
- **`examples/hott_example.v`** - HoTT-style proofs (requires HoTT library)
- **`examples/test_admits.v`** - Test file for find_admits.py (intentionally incomplete)

### Scripts

- **`scripts/verify_proof.py`** - Verify .v files compile successfully
- **`scripts/new_proof.py`** - Create new proof from templates
- **`scripts/debug_proof.py`** - Debug failing proofs with detailed output
- **`scripts/compile_project.py`** - Compile entire Rocq projects
- **`scripts/extract_code.py`** - Extract executable code from proofs
- **`scripts/find_admits.py`** - Locate all admits/axioms in codebase

## Integration with Development Tools

### CoqIDE

To open a file in CoqIDE:
```bash
coqide file.v
```

### VS Code with Coq Extension

To use with VS Code:
1. Install "Coq" or "VsCoq" extension
2. Open `.v` file
3. Step through proofs with keyboard shortcuts

### Proof General (Emacs)

To use with Emacs:
1. Install Proof General
2. Open `.v` file in Emacs
3. Use `C-c C-n` to step forward, `C-c C-u` to step backward

## Troubleshooting

### Coqtop Not Found

If `coqtop` is not in PATH:

**On Windows:**
```bash
# Set path explicitly in scripts
export COQ_BIN="C:/Coq-Platform~8.19~2024.10/bin"
```

**On Linux/Mac:**
```bash
export PATH=$PATH:/path/to/coq/bin
```

### Compilation Hangs

If compilation appears to hang:

**Check for:**
- Infinite loops in recursive definitions (use `Timeout` command)
- Universe consistency checking taking too long
- Large proof search spaces in automation

**Solutions:**
- Add `Timeout 10` before commands to limit execution time
- Simplify goals before using automation
- Break large proofs into smaller lemmas

### Out of Memory

If Rocq runs out of memory:

**Solutions:**
- Use `Qed` instead of `Defined` to make proofs opaque
- Clear unnecessary intermediate results
- Compile files separately rather than all at once
- Increase available memory or use 64-bit version

## License

Apache 2.0
