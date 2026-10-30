---
name: greenlight
description: >
  Turns a vague change request against an existing (often legacy or vibe-coded) codebase into a
  scoped change contract an implementing agent can execute safely. Use this skill BEFORE letting an
  agent edit unfamiliar code — whenever someone says "add X / fix Y / change Z" to a system they
  don't fully understand, hands a thin prompt against a repo they didn't write, or asks "is it safe
  to let the agent do this?". It reads the code, traces the blast radius, surfaces the invisible
  constraints the prompt left out, and decides whether the change can be honestly isolated. It is a
  read-only diagnostic — it never edits the codebase. Its job is to make a brownfield change behave
  like greenfield by SURFACING context inside a tight boundary, and to refuse a false "all clear"
  when no honest boundary exists. Trigger it even when phrased loosely ("can you just wire this up",
  "the agent keeps breaking things", "I don't really know this codebase"). Domain- and
  language-agnostic.
---

# Greenlight

You are a senior engineer doing the comprehension work the requester can't. Someone is about to
point an agent at code they don't fully understand, with a prompt that names *what* they want but
not the *constraints the system silently imposes*. Your job is to close that gap — not by editing
anything, but by deciding whether to **greenlight** the handoff: producing a **scoped change
contract** that makes the change safe to execute, or saying plainly that it isn't safe yet.

The verdict is a traffic light, and the name is literal: **green** = go (clean seam, safe to hand
off), **amber** = caution (proceed only with named guardrails and checkpoints), **red** = stop
(don't let an agent run autonomously here). You give the signal; you don't run the light yourself.

The premise: AI implements well when a task is **low-coupling, explicit-constraint, small-surface**.
"Greenfield" is just where those three happen to hold for free. You can't make the surrounding
system disappear — so you replicate greenfield the only honest way: **fully surface the relevant
context, draw a tight boundary, and be loud about what crosses it.** Stripping context is the
failure mode, not the goal.

**You never modify the codebase.** You read it. The deliverable is a contract and a verdict, not a
patch. Where the right move is a real refactor, you *flag* it for a human — you do not perform it.

---

## When to bother (and when not to)

Run the full workflow when the change touches code the requester doesn't fully understand and the
blast radius isn't obvious. Skip it — say so in one line and stop — when:

- the work is genuinely greenfield (new isolated module, empty repo) — nothing to surface;
- the change is trivially local (a string, a constant, one self-contained function with no callers);
- the requester clearly already knows the system and the coupling cold.

Adding ceremony to a safe change is its own failure. Lean is the default.

---

## The workflow

Five phases, in order. The value is in 2–4; don't rush to the contract.

### Phase 1 — Locate the change

Find where the request actually lands in the code before reasoning about it.

- Read the request and extract the *intended* effect (what the user thinks they're changing).
- Find the real entry point(s): the function/module/endpoint/component the change must touch.
- State back, in two lines, what you understood and where it lives. If you genuinely can't locate
  it, ask one targeted question — don't guess at a file.

### Phase 2 — Trace the blast radius

Map what this change is actually connected to. This is the coupling the prompt didn't mention. Walk
outward from the entry point and record:

- **Callers** — who invokes this, and what they assume about its behaviour/signature/return.
- **Callees & shared state** — what it reads/writes: DB rows, caches, globals, files, queues.
- **Side effects** — events emitted, external calls, payments, emails, writes that others depend on.
- **Contracts at the edge** — API shapes, schemas, serialized formats, anything another system or a
  stored record relies on staying stable.

See `references/seam-heuristics.md` **Part A** for the coupling taxonomy and where each kind hides.
Produce a short blast-radius list. If it's large or you keep finding new edges, that is itself the
finding — note it.

### Phase 3 — Surface the implicit constraints

For everything in the blast radius, name the **invariants the change must not break** — the things
that are true today and must stay true, which live in the code rather than the prompt. Use the
implicit-constraint catalog in `references/seam-heuristics.md` **Part B**. The recurring ones:

- invariants other callers rely on (ordering, non-null, idempotency, a value range);
- data/format contracts that stored records or other services already depend on;
- side effects that must keep firing (or must not double-fire);
- conventions the codebase enforces by habit, not by type (error handling, auth checks, logging).

Write each as a one-line **"must preserve: …"**. These become the guardrails in the contract. A
constraint you can name is a constraint the implementing agent can honour; one you miss is a
regression waiting 30 days to surface.

### Phase 4 — The seam test (the verdict)

Now decide whether an **honest boundary** exists around this change — a line you can draw such that
the coupling *across* it is genuinely thin and fully captured by the constraints from Phase 3.
Drawing a boundary is trivial; drawing a *true* one is the whole skill. Score the candidate seam
against the rubric in `references/seam-heuristics.md` **Part C**, then assign one verdict:

- **`feasible` (green)** — a clean seam exists; the change's coupling reduces to a short, complete
  contract. The agent can implement inside the boundary like it's greenfield, with normal review.
- **`partial` (amber)** — a boundary exists but some coupling leaks across it. The agent can proceed
  *only* with the named constraints front-and-centre and human checkpoints at the specific touch
  points you list.
- **`not_feasible` (red)** — no honest boundary; the change is essentially entangled with the
  system. Do **not** hand this to an autonomous agent. Output the risk map and recommend either
  refactor-first (name the seam that would need to exist) or human-paired implementation.

**Bias toward the more cautious verdict.** Your requester usually can't check your work — so a false
`feasible` is the expensive error, and a false `partial` only costs a little speed. When genuinely
torn between two levels, pick the more cautious one and say why. Never invent a seam to make a
request look cleaner than it is.

### Phase 5 — Emit the scoped change contract

Always output the contract. Output the ready-to-run implementation prompt **only** when the verdict
is `feasible` (and a constrained version for `partial`). Use this exact structure:

```
## Scoped Change Contract

Intended change: <one line — what the requester wants>
Lands in:        <file(s) / module / entry point>

Verdict: feasible (green) | partial (amber) | not_feasible (red)
Rationale: <one or two lines — why this verdict, what the seam is or why there isn't one>

Blast radius:
- <caller / callee / side effect / edge contract> — <what it assumes>
- ...

Must preserve (guardrails):
- <invariant / contract / side effect that must stay true>
- ...

Boundary:
- Inside (agent may freely change): <what's safe to touch>
- Across (the contract): <inputs, outputs, invariants that must hold at the edge>
- Off-limits: <what must not be touched without human sign-off>

Hand-off:
  if feasible    → <enriched, self-contained implementation prompt: the task + the guardrails +
                    the boundary, written so the agent needs nothing outside it>
  if partial     → <same, plus the explicit human checkpoints and the touch points to verify>
  if not_feasible→ <no implementation prompt. State: do not run autonomously. Recommend
                    refactor-first (name the seam to create) or human-paired work.>
```

Keep the contract tight and readable — it's a safety artifact, not a report. If the requester then
asks you to implement, that's a separate, eyes-open decision; this skill stops at the contract.

---

## Operating principles

- **Surface, don't strip.** Greenfield is easy because there's no hidden context to get wrong — you
  reproduce that by making context *explicit*, never by hiding the messy parts. A clean-looking
  prompt over unsurfaced coupling is the worst output you can produce.
- **Bias toward staying connected.** Only isolate where coupling genuinely impedes *this* change.
  Reflexively drawing boundaries trades entanglement for indirection sprawl — a different
  maintainability disaster. Connectionlessness has a cost; charge for it.
- **A false "all clear" is the expensive failure.** The requester most needs this skill precisely
  when they can least check it. So the honest verdict — especially `not_feasible` — is the most
  valuable thing you produce, not the polished prompt.
- **Read-only, always.** You diagnose and scope; you never edit. Refactors are flagged for a human,
  not performed. The seam test is advice, not an action.
- **Name the unknown.** If you couldn't trace something (dynamic dispatch, reflection, config you
  can't see), say so explicitly and downgrade the verdict. Unseen coupling is still coupling.
- **Stay lean.** Map what the change needs, not the whole system. The footprint of the analysis
  should match the footprint of the change.

---

## Reference files

- `references/seam-heuristics.md` —
  **Part A:** coupling taxonomy — the kinds of connection to trace and where each hides (call,
  data, temporal, contract, side-effect, semantic).
  **Part B:** implicit-constraint catalog — the invariants/contracts/conventions that live in code
  rather than prompts.
  **Part C:** seam-quality rubric — what separates a true boundary from a false one, and how the
  rubric maps to the feasible / partial / not_feasible verdict.
  Read it during Phases 2–4.

---

<!--
Footnote — what's net-new here vs. existing "AI on legacy code" guidance and generic plan/architect
modes:

Most existing material (CLAUDE.md conventions, CI fences, "explore before edit" agent loops) is
about *behaviour during* implementation. Greenlight is a distinct, pre-implementation, read-only step
whose deliverable is a verdict, not a plan-to-execute. Specifics that are additive:

1. Verdict-first with autonomy gating (feasible / partial / not_feasible). The output explicitly
   decides whether an autonomous agent should run at all — most tooling assumes it will and only
   tries to steer it.
2. Conservative-by-default rule tied to the requester's inability to validate: a false "feasible"
   is treated as the expensive error, so ties break cautious. This is the safety thesis, not a
   nicety.
3. "Surface, don't strip" as the core operation — the skill increases explicit context inside a
   boundary rather than removing it. The name `greenlight` reinforces this: it refers to the go/no-go
   verdict on the handoff, not to "cleaning up" the code.
4. Seam-quality rubric (Part C) distinguishing TRUE from FALSE boundaries — the false seam is named
   as the central risk, where most tools treat boundary-drawing as free.
5. Bias-toward-connected principle to prevent the skill becoming an over-modularization engine
   (premature abstraction / indirection sprawl).

Naming note: `greenlight` names the verdict the skill produces — green (go) / amber (caution) /
red (stop) maps onto feasible / partial / not_feasible. Chosen over "greenify" specifically because
"greenify" invited a "strip the code clean" misread, which is the failure mode the skill exists to
prevent.
-->