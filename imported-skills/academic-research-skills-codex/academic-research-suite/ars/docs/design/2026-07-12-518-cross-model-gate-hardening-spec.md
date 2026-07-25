# Cross-model gate hardening (#518)

**Issue:** #518 — risk-stratified sampling, blind disagreement checkpoints, capability allowlist, gpt-5.6-sol promotion bakeoff
**Date:** 2026-07-12
**Files touched:** `shared/cross_model_verification.md`, `academic-pipeline/agents/integrity_verification_agent.md`, `deep-research/agents/research_architect_agent.md` + its byte-identical plugin mirror `agents/research_architect_agent.md`, `academic-paper-reviewer/agents/editorial_synthesizer_agent.md`, `docs/SETUP.md` + `docs/SETUP.zh-TW.md` (feature table), `.claude/CLAUDE.md`, `shared/raise_framework.md`, `CHANGELOG.md`
**Status:** design frozen per issue #518 (2026-07-11 consult); parameters chosen in this spec

## Problem

A 2026-07-11 cross-model consult (gpt-5.6-sol, xhigh) on verifier placement produced three recommendations plus one routing correctness gap:

1. The integrity-gate cross-model sample is a **uniform random 30%** — it spends the same verification budget on a decorative background citation as on the reference backing the paper's headline effect size. High-impact citations can escape the sample entirely.
2. The two **irreversible checkpoints** (research-design freeze; final editorial accept/revise/reject) have no cross-model check at all, and the only design on file for peer review — the "6th reviewer" — matches the consult's counterproductive-conditions list (score averaging, role duplication, findings treated as confirmed defects, majority-vote false confidence, synthesizer context burn).
3. The model-detection `case` declares **any** `gpt-*`/`gemini-*` id grounded-route-available before the API ever rejects it (`gpt-made-up` included). "Which provider endpoint" and "is this id known-good" are conflated.
4. `gpt-5.6-sol` is listed provisional (#516 / PR #515) with the promotion criteria named but **not operationalized** — no defined run flips the recommended default.

## Load-bearing invariants (must hold after this change)

- **Grounding invariant unchanged:** a cross-model `VERIFIED` counts as agreement only with API-level grounding evidence. Stratification changes *which* references are sent, never *how* verdicts are counted.
- **Routing precedence unchanged:** any `gpt-*`/`gemini-*` id still takes the grounded first-party route (D3 adds a *status* signal, never a routing change — an unlisted first-party id must not fall through to the ungrounded compatible branch).
- **Advisory posture unchanged:** checkpoint disagreement is a review trigger for the human, never a vote, never averaged, never a block. Consistent with the Collaboration Depth Observer's "never blocks" and the `terminal_policies` opt-in philosophy.
- **Consent boundary unchanged:** blueprints, reviewer cards, and manuscripts go to an external provider only after the existing consent gate.

## Design

### D1 — Risk-stratified sampling at integrity gates

Replaces the uniform random 30% (min 5, max 15) in `shared/cross_model_verification.md` §Integrity Verification and its consumer copy in `integrity_verification_agent.md`.

**Tier classification (by the primary, at selection time, reported in the results table).** Four tiers, mutually exclusive by precedence (`HIGH-IMPACT` > `NEW-CHANGED` > `CONTROL`/`RANDOM`); a reference qualifying for more than one is classified once at the highest tier and verified once:

- **HIGH-IMPACT — verify 100%, no cap (both gates).** A reference is high-impact if it supports any of: (a) a headline conclusion (abstract- or conclusions-level claim); (b) a numerical claim (statistic, effect size, percentage, threshold); (c) a causal claim; (d) a methods-critical claim (the validity of the chosen method rests on it); (e) a disputed claim (already carrying a contradiction disclosure or reviewer split).
- **RANDOM (Stage 2.5 only) — the non-high-impact remainder**, sampled at 10%, rounded up (min 3, max 10; if the remainder < 3, sample all of it).
- **NEW-CHANGED (Stage 4.5 only) — verify 100%, no cap:** every reference supporting a claim new or changed since Stage 2.5, whatever its impact class.
- **CONTROL (Stage 4.5 only) — the unchanged, non-high-impact remainder**, sampled at 10%, rounded up (min 3, max 10), to catch silent drift. CONTROL replaces RANDOM at the final gate.

**Cost model change (documented, deliberate):** calls now scale with the count of high-impact (and, at Stage 4.5, new/changed) citations instead of total reference count. A results-dense paper approaches 100% coverage; that is the point — precision where the paper's weight rests. The old flat cap (max 15) is retired; only the sampled tiers (RANDOM/CONTROL) carry a cap (max 10 each).

Sampling parameters (10% / round-up / min 3 / max 10) are this spec's choice, not the issue's; they are tunable without protocol redesign. *(Round-1 codex review: the tier set was widened from three to four — a new/changed non-high-impact reference was unrepresentable — and the stale "max 15 survives" sentence was removed.)*

### D2 — Blind disagreement checkpoints (replaces the "6th reviewer — Planned" section)

Two irreversible checkpoints gain an optional cross-model check when `ARS_CROSS_MODEL` is set and consent is granted:

| Checkpoint | Primary owner | Cross-model input (never the primary's decision) | Structured decision enum |
|---|---|---|---|
| Research-design freeze | `research_architect_agent` (deep-research) | RQ Brief + draft Methodology Blueprint | `sound` / `revise_before_freeze` / `fundamental_concern` |
| Final editorial decision | `editorial_synthesizer_agent` (academic-paper-reviewer) | The panel's usable reviewer cards (`panel_size` N — 5 in full mode, 2 under `methodology_focus`) + paper metadata | `accept` / `minor_revision` / `major_revision` / `reject` |

**Mechanics (shared):**

1. The primary reaches its decision as normal and commits it in the SAME structured form (enum + up to 3 drivers) before the cross-model is called — enum-against-enum comparison, both sides blind. The architect records it separately from the blueprint and sends the cross-model a sanitized payload with the Design-Freeze Checkpoint Audit section stripped (writing the decision into the blueprint before the call would leak it and break blindness — round-2 verify fix); the audit section is populated after the comparison, with an `unavailable — transport error` representation for the no-cross-model case. The synthesizer's decision is the emitted one (in sprint-contract mode, the mechanical protocol's `editorial_decision` verbatim, with the checkpoint running strictly post-Step-3, never extending the contract arithmetic).
2. The cross-model receives the same input material and a structured-decision prompt. It **never** sees the primary's decision, scores, or reasoning first — same anchoring-prevention rule as the integrity samples.
3. Output contract: `{decision: <enum>, drivers: [≤3 one-sentence reasons], confidence: low|medium|high}`.
4. Mechanical comparison: **material divergence = differing enum values.** (Adjacent categories, e.g. minor vs major revision, are still material; the report notes adjacency.)
5. On divergence: a **targeted rebuttal** — the primary must address each cross-model driver specifically against the evidence already on file (reviewer cards / blueprint content), no generic reassurance. Both decisions + the rebuttal surface to the user. The primary's decision stands unless the *user* changes it.
6. On agreement: one log line `[CROSS-MODEL-CHECKPOINT: agreement — <checkpoint>]`; both structured decisions are still recorded.
7. Graceful degradation: transport failure → `[CROSS-MODEL-ERROR]`, proceed single-model, note in the report (existing rules).

**Grounding:** checkpoint decisions are judgment, not lookup — an ungrounded/compatible provider is first-class here (same scoping as DA critique: a divergence from any provider is an adversarial hypothesis and review trigger, never a confirmed defect).

**Synthesizer boundary (v3.6.2 compatibility):** under a sprint contract the synthesizer's decision comes from the mechanical Step 1–3 protocol; the blind check compares against that output and its rebuttal may cite only existing reviewer-card content. The cross-model's drivers are not new review comments and are never inserted into the reviewer matrix, dimension scores, or failure-condition evaluation — the sprint-contract arithmetic is closed to them.

**Why not the generic 6th reviewer:** the consult's counterproductive-conditions list — score averaging, role duplication, findings treated as confirmed defects, majority-vote false confidence, synthesizer context burn — matches ARS's documented anti-patterns one-for-one. The "Planned" section is removed, not deferred; the two blind checkpoints are the replacement design. Mirrors updated: `.claude/CLAUDE.md` v3.0 note, `shared/raise_framework.md` self-declaration, SETUP feature table. Historical changelog/README release-notes lines stay as written (they describe what was true then).

### D3 — Capability allowlist (id status, not routing)

The §Detecting Available Models snippet gains a second output alongside `CROSS_MODEL_AVAILABLE`:

```
CROSS_MODEL_ID_STATUS = validated | provisional | unlisted
```

- `validated`: `gpt-5.5`, `gpt-5.5-pro`, `gpt-5.4`, `gpt-5.4-pro`, `gemini-3.1-pro-preview`
- `provisional`: `gpt-5.6-sol` (per #516 / PR #515)
- `unlisted`: any other `gpt-*`/`gemini-*` id — routed grounded as before, but with an explicit warning: not a known-good id, the API may reject it, run `scripts/cross_model_smoke_test.sh` before trusting results.

Status applies to first-party routes only; compatible-route ids are user-declared and carry no allowlist (routing there is endpoint-governed, unchanged from #455). Routing behavior is byte-identical; only the announcement changes.

### D4 — `gpt-5.6-sol` promotion bakeoff (provisional → validated → recommended default)

New subsection in the canonical doc operationalizing the five measures already named in the provisional note.

- **Entry gate:** `scripts/cross_model_smoke_test.sh` passes against the candidate id.
- **Probe-set precondition:** the 30-reference probe set (20 real: 10 easy DOI-keyed + 10 hard preprints/DOI-less/non-English; 10 synthetic plausible fabrications) must be committed as a versioned, labeled fixture with its sha256 recorded in the run report before any run counts as a gate result.
- **Procedure:** baseline (`gpt-5.5`) and candidate the same day, one call per reference, 3 repeats; per-reference verdict = ≥2/3 agreement, a 1–1–1 split is indeterminate and scored conservatively against the model that produced it.
- **Non-inferiority thresholds (all five must pass):**
  1. Grounded-search completion rate ≥ baseline − 5 pp.
  2. Citation-mismatch recall on the 10 fabrications ≥ baseline − 5 pp AND ≥ 80% absolute.
  3. False-disagreement rate on the 20 real ≤ baseline + 5 pp.
  4. jq-guard shape stability: zero guard misfires attributable to response-shape change (hard requirement).
  5. p95 latency ≤ 2× baseline.
- **Outcome — two promotions, not one:** all five pass → `provisional` becomes `validated` (allowlist + Supported Models note; run recorded under `audits/` with the probe-set hash). The **recommended default** flips only with an additional stated reason (superiority on ≥1 measure with no inferiority elsewhere, or a named operational benefit) — a candidate that merely scraped under every tolerance is validated but not the new recommendation. Any fail → stays provisional, results still recorded. *(Round-1 codex review: outcome split added — a bare non-inferiority pass no longer auto-flips the default; probe-set fixture + tie handling made preconditions. Round-2 verify: the two introductory statements that still implied pass ⇒ default were aligned to the split.)*

Thresholds are this spec's choice; recorded here so a future bakeoff argues against numbers, not vibes.

## Out of scope

- No schema change (items 1–2 are prose-layer, per the issue).
- No change to DA critique flow, compatible-provider normalization, jq guards, or the smoke test script itself.
- Actually *running* the bakeoff (requires live keys + spend) — this PR defines it.
- #517 model tiering (separate issue; its Stage 2.5/4.5 quality-boost surfaces will reference the checkpoint design added here).

## Verification

- `scripts/check_cross_model_verification_sync.py` (jq wiring + safety branches survive the doc edit)
- `scripts/check_setup_cross_model_parity.py` (SETUP en/zh-TW stay pinned)
- `scripts/check_v3_9_2_phase_boundary.py` + full local pytest manifest
- Local personal-boundary / PII pre-push scan (maintainer-side hook)
