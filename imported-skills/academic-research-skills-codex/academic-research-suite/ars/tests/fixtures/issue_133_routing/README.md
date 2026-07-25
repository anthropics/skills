# Issue #133 — L1 Routing Behavioral Smoke Test Fixtures (v3.9.2)

**Spec:** `docs/design/2026-05-18-ars-v3.9.2-phase-boundary-spec.md` Phase L1.4
**Issue:** #133 (phase scope inflation hot-fix)
**Status:** v3.9.2 hot-fix; behavioral smoke tests, NOT deterministic unit tests

## Honest framing

These fixtures are **behavioral smoke tests + cross-model spot-check**, not deterministic green/red unit tests. The unit-under-test is a Large Language Model (Claude / GPT / Gemini) following the routing rules in `.claude/CLAUDE.md` "Routing Discipline (v3.9.2)" + `shared/references/intent_clarification_protocol.md`.

LLM-behavior assertions are flaky in the way model-behavior tests always are:

- A test that passes on one model generation can regress on the next (observed Opus 4.7 → 4.8; recalibrated on Fable 5, 2026-06)
- A test can pass with prompt cache warm and fail cold
- A test can pass at temp=0 and fail at temp=1

This is acceptable for **routing discipline** (which is a calibration target, not a deterministic gate) but you should not promote these to CI green/red gates without recalibrating against the current model fleet.

## Acceptance criterion (v3.9.2 ship gate)

- **100% pass on the current primary model** — the inherited Claude Code session model (Opus 4.7 at the v3.9.2 ship; Fable 5 at the 2026-06 recalibration)
- **≥ 75% pass on Sonnet 4.6 and GPT-5.5** (degradation flagged but non-blocking ship)
- Cross-model divergence > 1 fixture between primary and Sonnet/GPT → recalibrate routing prose

If you cannot reach 100% on the current primary model, the routing prose in CLAUDE.md / protocol doc needs tightening — fix the prose, not the test.

## Fixture index

| # | Fixture | Input class | Expected routing |
|---|---|---|---|
| 01 | `01_cross_phase_abstract_plus_lit/` | Abstract (Phase 4) + literature (Phase 2) | **Clarify** (cross-phase ambiguous) |
| 02 | `02_single_phase_literature_only/` | Literature only (Phase 2) + lit-review request | **Proceed** (explicit + single-phase) |
| 03 | `03_no_materials_ambiguous/` | "Can you help me with my paper?" | **Clarify** (no-materials ambiguous) |
| 04 | `04_explicit_slash_command/` | `/ars-lit-review` invocation | **Proceed** (explicit slash command) |
| 05 | `05_direct_mode_honored/` | `[direct-mode] run bibliography_agent` | **Proceed** (escape hatch honored, no clarification) |
| 06 | `06_direct_mode_mid_message_not_honored/` | "Please [direct-mode] dispatch X" | **Clarify** (escape hatch ignored — not byte-0) |
| 07 | `07_direct_mode_case_insensitive/` | `[Direct-Mode] write an abstract` | **Proceed** (case-insensitive accepted) |
| 08 | `08_full_draft_plus_abstract_plus_lit/` | Full draft + abstract + literature, no clear intent | **Clarify** (cross-phase, multiple plausible workflows) |
| 09 | `09_korean_revision_not_review/` | Korean 수정 (revise) request + draft (#452) | **Proceed** → `academic-paper:revision` (not reviewer) |
| 10 | `10_korean_review_not_revision/` | Korean 심사 (referee) request + manuscript (#452) | **Proceed** → `academic-paper-reviewer:full` (not paper) |

## Fixture file format

Each fixture directory contains:

```
NN_<slug>/
├── input.md          — user message (verbatim) + any provided artifacts described in markdown
├── expected.yaml     — expected routing outcome (machine-readable)
└── rationale.md      — why this is the expected outcome (human-readable, cites routing prose lines)
```

### `expected.yaml` schema

```yaml
fixture_id: <NN_slug>
expected_routing_class: clarify | proceed
expected_destination: <skill_name> | <agent_name> | clarification_only
escape_hatch_applied: true | false
direct_mode_stripped_message: <string, only when escape_hatch_applied: true>
notes: <optional free-text>
```

### Running the smoke test (manual)

Until v3.10 conductor brings deterministic dispatch, these fixtures are run **manually against a live ARS session**:

1. Start a fresh Claude Code session in a clean workspace
2. Paste the `input.md` content as the first message
3. Observe whether the response classifies as `expected_routing_class`
4. Record pass/fail in a calibration log

For cross-model spot-check, run the same fixtures against Opus / Sonnet / GPT-5.5 and compare.

## v3.10 forward note

When active conductor (#134) ships, these fixtures translate to deterministic envelope-dispatch tests with structured `task_envelope.schema.json` validation. The behavioral-smoke-test framing becomes obsolete — the conductor's routing decision is then code-testable, not LLM-behavior-testable.
