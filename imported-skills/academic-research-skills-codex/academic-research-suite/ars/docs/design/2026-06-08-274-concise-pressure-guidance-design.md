# #274 — Concise reviewer output and pressure-stable boundaries (Opus 4.8 §4.1.4 follow-up)

**Status**: design (2026-06-08)
**Issue**: [#274](https://github.com/Imbad0202/academic-research-skills/issues/274)
**Source**: Claude Opus 4.8 System Card (Anthropic, 2026-05), §4.1.4
**Related**: #272 / #273 (Opus 4.8 behavioral-signal cluster); #247 (ethics-gate override recording, CLOSED)

---

## Two signals (from the system card §4.1.4)

1. **Verbosity drift.** 4.8 responses, especially refusals, are longer and more over-caveated than 4.7 — Anthropic added a "keep responses and caveats concise" line to the default system prompt.
2. **Retract-under-pressure.** In a small number of multi-turn cases, 4.8 issued a correct refusal and then retracted it under sustained social/authority pressure (4.8 more resistant than 4.7 on balance; the pattern still exists).

## Why this touches ARS

The reviewer agents produce decision-useful review reports; a reviewer that buries its verdict in hedging is a quality regression. And ARS workflows routinely involve a user pushing back (relax an evidence standard, keep a shaky citation, soften a limitation) — exactly the surface where retract-under-pressure would show.

## Scope decision — guidance layer only, honestly bounded

This is a **prose strengthening** of existing reviewer/writing guidance. It is NOT a behavioral proof.

**The behavioral-check honesty bound (the crux).** Acceptance #2 asks to "confirm hard boundaries + DA non-softening hold under 4.8 after pushback." That is an LLM-behavior property: it cannot be pinned by a deterministic CI test (retraction is runtime + probabilistic), and it must NOT be ticked by the author self-simulating a pushback dialogue — self-simulation is theater, not verification. So acceptance #2 is reframed as a **prompt-surface confirmation**: the live reviewer prompts contain explicit, adversarially-worded pressure-resistance instructions. A standing **epistemic-status line** states the limit plainly — a static document cannot guarantee runtime pressure-stability — mirroring the #272 discipline (guidance layer ≠ runtime enforcement). No claim of "confirmed 4.8 holds" is made anywhere in the change or its metadata.

This change ships no lint, no mutation test, no xfail pebble. "Be concise" is style guidance, not a contract invariant with a downstream consumer, so a drift-guard lint would be unrequested machinery. (Contrast #272, whose instruction/data boundary IS load-bearing and earned its lint.)

## Changes

### 1. Concise output discipline — inlined into the report producers

A short `## Output Discipline` block is inlined immediately before `## Output Format` in each live report-producing agent:

- `academic-paper-reviewer/agents/`: `domain_reviewer`, `methodology_reviewer`, `perspective_reviewer`, `eic_agent`, `devils_advocate_reviewer`, `editorial_synthesizer`
- `academic-paper/agents/peer_reviewer_agent` (its existing "conciseness" mention rates the *paper's* writing quality, not the agent's own output — a genuine gap)

Inline (not a shared pointer) because the instruction must be live when the agent *writes*; a bare backpointer is invisible to the model at generation time (same rationale #272 used).

Base reviewer block text (the six reviewer agents share it verbatim; `editorial_synthesizer` adapts it to "decision letter / roadmap" and adds the evidence-standard rule, `peer_reviewer` adds a one-line note distinguishing it from rating the paper's writing, and `devils_advocate` points to its Attack Intensity protocol for pressure-resistance):

> ## Output Discipline
>
> Keep your review **brief but complete**. State each finding and your verdict directly; do not pad them with repeated qualifiers, apologetic framing, or restated caveats. Concise does **not** mean under-caveated — preserve every material uncertainty and limitation; cut only redundancy and hedging that adds no information. One clear statement of a caveat beats three softened ones.

### 2. Pressure-resistance reinforcement — Devil's Advocate

The DA already carries a strong non-softening block (`## Attack Intensity Preservation Protocol (v3.0)`, its Anti-Sycophancy Rules sub-block: rebuttal scoring, "do not soften after pushback", no-consecutive-concessions, persistent-pushback-≠-rebuttal, concession-rate tracking). #274 adds one general, evidence-standard-framed rule into that same sub-block (NOT an attack catalogue — public-repo safe), threaded to the existing concession threshold:

> **Pressure is not evidence.** Repeated pushback, appeals to authority or status, or bare requests to soften do **not** by themselves change a finding. Revise only when the rebuttal supplies new evidence or reasoning that directly addresses the finding's stated basis. With no new substance, briefly restate the finding once and stop — do not expand caveats, apologize repeatedly, or retract a correct finding to preserve agreement.

The same evidence-standard sentence (adapted to "boundary/decision" rather than "finding") is added to `editorial_synthesizer` near its arbitration discipline, since the synthesizer also holds boundaries under EIC-arbitration pushback.

### 3. Epistemic-status line

Each `## Output Discipline` block carries a one-line status:

> *Epistemic status: these are prompt-surface instructions. They make the reviewer's output discipline explicit; they do not, and cannot, prove the model stays pressure-stable at runtime — that would need a separate non-deterministic behavioral eval.*

## Out of scope

- No lint / mutation test / xfail pebble (style guidance, no contract consumer).
- No behavioral eval harness, no pressure/jailbreak scripts (public-repo non-goal).
- No new blocking gate.
- No claim of "confirmed Opus 4.8 behavior" in code, commits, or PR metadata.

## Acceptance (#274, honestly aligned)

- [ ] Concise-output direction inlined in the report-producing reviewer/writing agents.
- [ ] Prompt-surface confirmation: the pressure-resistance instructions are present and explicit (DA non-softening reinforced; evidence-standard rule added). **Reframed from "confirm 4.8 holds" — see honesty bound.**
- [ ] #247 cross-link: handled as a PR-body mention (a back-reference to a CLOSED issue is a tracker note, not a repo artifact; not counted as a code deliverable).

## Verification

- Prompt self-consistency; the concise block must not contradict any agent's existing Output Format requirements.
- Full pytest suite green; phase-boundary and line-related lints green (the added H2 must not trip a line-budget or H2-count assertion — checked, adjusted if any).
- Paper-derived: cite the system card; no internal or personal content; general phrasing, no attack catalogue.
