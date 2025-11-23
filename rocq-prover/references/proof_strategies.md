# Advanced Proof Strategies for Rocq/Coq

## Strategy 1: Lemma Decomposition

Break complex proofs into smaller, manageable lemmas.

## Strategy 2: Strengthen Induction Hypothesis

Add extra assumptions to make induction work.

## Strategy 3: Generalize Before Induction

Use `generalize dependent` before `induction`.

## Strategy 4: Well-Founded Induction

For recursive structures that aren't structurally decreasing.

## Strategy 5: Proof by Reflection

Use computation to prove goals automatically.

## Strategy 6: Ltac Automation

Write custom tactics for repeated patterns.

See tactics_library.md and error_resolution.md for detailed examples.
