# ECD Theory Lineage

## What ECD Is

Evolutionary Constraint Development, or ECD, is an original delivery method composed for Claude Code-based work. It is not a direct clone of a single paper, framework, or prompt chain. It is a practical synthesis built around one hard requirement:

> the coding stage must never be forced to invent high-impact product meaning

That rule drives the whole system.

## Theoretical Source

ECD's theory comes from combining several engineering ideas into one operational loop.

### 1. Constraint-led planning

The planning stages treat the user's request as noisy evidence rather than fixed truth. The goal is to freeze enough constraints that later execution can be faithful instead of interpretive.

This is the source of:

- the `05-constraint-ledger.md` shared truth surface
- the requirement that planning resolve hidden assumptions before coding
- the rule that unresolved high-impact gaps force reentry instead of optimistic progress

### 2. Stage-gated compilation

ECD treats delivery like a compilation pipeline instead of an open-ended conversation. A raw request is compiled into a normalized case, then into a staged bundle, then into a code handoff, then into run evidence, and finally into an achieve verdict.

This is the source of:

- `pre -> plan -> code -> achieve`
- the refusal to let `/code` treat earlier notes as freeform brainstorming
- the idea that `90-code-handoff.md` is a compiled artifact, not a draft summary

### 3. Design-by-contract for implementation handoff

The handoff is contract-shaped. It freezes file plans, function contracts, allowed decisions, forbidden decisions, verification commands, browser checks, and reentry triggers.

This is the source of:

- `function_contracts`
- `implementation_units`
- `allowed_decisions` and `forbidden_decisions`
- the requirement that `code_ready=true` is a truth claim, not a motivational label

### 4. Adversarial review before execution

ECD assumes any plan written by one model is vulnerable to anchoring, omission, and optimism bias. It therefore forces independent criticism before execution.

This is the source of:

- Stage D independent critique
- Stage G red-team and blue-team attack/defense passes
- Stage H independent coding-readiness review
- Stage J independent compile-for-code judgment

### 5. Acceptance-driven closure

Shipping is not the same as succeeding. A run that compiles but fails the first-open experience is not achieved.

This is the source of:

- the separate `achieve` phase
- archive decisions that can be truthful or withheld
- the rule that failed acceptance leaves the case open

## Why ECD Uses These Sources Together

Any one of the sources above helps, but none is enough on its own.

- Constraint-led planning without stage gates drifts.
- Stage gates without contracts create vague handoffs.
- Contracts without independent review preserve mistakes more neatly.
- Review without achieve still lets visibly broken work be called done.

ECD combines them so each stage limits a different failure mode.

## The Core ECD Thesis

The main thesis of ECD is:

1. Raw requests are not reliable enough to code from directly.
2. Planning must aggressively interrogate meaning while user interaction is still allowed.
3. Later stages should reduce interpretation, not increase it.
4. Independent subagents are necessary to counter parent-model anchoring.
5. Closure must be based on evidence, not momentum.

## What ECD Is Not

ECD is not:

- a general-purpose product framework
- a replacement for good engineering judgment
- an excuse to over-document trivial changes
- a claim that every workflow needs the same number of stages

It is specifically a high-discipline delivery loop for requests where semantic drift is costly.

## Why The Skill Is Claude Code-first

This repository binds the method to Claude Code because Claude Code gives ECD the concrete primitives it needs:

- local file access
- script execution
- staged artifact editing
- spawned subagents (via `Agent` tool)

Without those primitives, ECD can be described, but not fully enacted.
