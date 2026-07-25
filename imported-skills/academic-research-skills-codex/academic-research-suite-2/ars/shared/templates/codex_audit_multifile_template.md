# Codex Multi-File Audit Prompt Template

**Spec:** v3.6.7 §7.2 — audit prompt template for downstream-agent deliverable cross-model audit.

**Audience:** ARS pipeline orchestrator (academic-pipeline, deep-research, academic-paper) producing codex audit prompts for Phase 2 / Phase 3 deliverables. Human authors running ad-hoc cross-model review on a deliverable bundle.

**Why this template exists:** Live ARS pipeline runs surfaced 17 downstream-agent hallucination/drift patterns (spec §3) that single-file or single-dimension audit could not catch. The patterns interact across files (synthesis_agent's effect-inventory drift surfaces only when comparing two narrative sections; report_compiler_agent's compression overclaim surfaces only when comparing abstract against body). A multi-file audit prompt with explicit dimensions makes the cross-file checks first-class. Spec §4.1 (Lesson D1) records the empirical observation that multi-file parallel audit catches more findings per round than sequential single-file audit at comparable token cost.

This template fixes a single audit-prompt structure so the orchestrator's audit hooks (spec §5) generate consistent, reproducible prompts.

---

## Template structure

A v3.7.1 multi-file audit prompt has eight sections in this order (Section 0 prepended additively per v3.7.1 D2; Sections 1–7 stay byte-equivalent to v3.6.7):

0. Scope Report (mandatory; rides verbatim in every round; v3.7.1 D2)
1. Round metadata
2. Bundle inventory
3. Audit dimensions (the 7 specified below)
4. Round-specific job
5. Convergence target
6. Output format
7. Anti-fake-audit guard (mandatory; rides verbatim in every audit dispatch)

The orchestrator fills the placeholders in `{curly_braces}`. Everything else rides verbatim. Section 0 is non-negotiable — its purpose is to disclose the audit's actual coverage so a "PASSED" verdict cannot mask un-retrieved sources (spec v3.7.1 §3.2 / Pattern D2). Section 7 is non-negotiable — omitting it leaves sub-agents free to fake audit-passed metadata, which is the failure mode v3.6.7 spec §5.3 + Pattern C3 + `feedback_subagent_tool_hallucination.md` exist to prevent.

---

## Section 0 — Scope Report (mandatory; v3.7.1 D2)

Every audit round MUST open with a Scope Report that quantifies how many of the audited entries had a retrieved original source vs. were verified only against derivative bibliography or self-consistency. The block below rides verbatim in every audit dispatch, ahead of any pass/fail summary.

```
## Codex Audit Round N — Scope Report

**Total entries audited:** <N_total>
**Entries with retrieved original source:** <N_with_source> (verified against original publication)
**Entries description-only (no retrieved source):** <N_without_source> (verified only against derivative bibliography or self-consistency)

**Audit scope warning:** <N_without_source> entries cannot be independently verified by this audit round. Their `verified` status reflects internal consistency between entry .md and the derivative bibliography source, NOT correctness against the original publication. These entries should be treated as **unverifiable until original sources are retrieved**.

**Affected refcodes (description-only):** <comma-separated list>
```

**Two firm rules (spec v3.7.1 §3.2):**

- The Scope Report block must appear **before** any pass/fail summary in the audit output.
- The aggregate verdict MUST be split into the following three reporting lines (the combined-aggregate "PASSED" verb is forbidden in the audit summary):
  - `verified-against-source: PASS | FAIL` (over the retrieved-source subset)
  - `description-internally-consistent: PASS | FAIL` (over the non-retrieved subset)
  - `unaudited-due-to-missing-source: <count>` (always reported, never hidden)

**Why this exists:** in the 2026-04-30 production session, a codex round-3 report stated "ADDRESSED" without disclosing that only 22 of 53 entries had retrieved original sources; the remaining 31 description-only entries inherited the "verified" verdict by aggregation. The Scope Report renders that split first-class so a reader cannot conflate self-consistency with retrieval-grounded verification.

---

## Section 1 — Round metadata

```
Audit round: {N} of {target_rounds}
Previous rounds: {summary_of_prior_findings_or "none (first round)"}
Bundle scope: {phase or stage label, e.g. "Phase 2 chapter deliverables" or "Phase 3 abstract + reflexivity disclosure"}
```

**Fill rules:**
- `target_rounds` defaults to 3 per spec §4.2 (Lesson D2: convergence requires 3+ rounds, not 1 or 2). Increase to 4–5 when prior round count exceeded 3 without convergence.
- `summary_of_prior_findings` cites finding counts by severity for each prior round, e.g. "Round 1: P1×4 / P2×5 / P3×1 (10 total). Round 2: P1×0 / P2×3 / P3×1 (4 total)."
- For first round, `Previous rounds: none (first round, baseline audit)`.

---

## Section 2 — Bundle inventory

```
Authoritative context (commit {git_sha}):

Primary deliverables (audit target):
- {file path 1 with one-line description}
- {file path 2 ...}

Supporting context (do not audit; reference only):
- {file path A with one-line role}
- {file path B ...}

Out-of-scope (do not read):
- {explicit exclusions, if any}
```

**Fill rules:**
- Pin the audit to a commit SHA so the audit is reproducible. Codex sometimes reads files at a slightly different state than the human reviewer expects; the SHA pins the boundary.
- Distinguish primary deliverables from supporting context. Primary gets audited; supporting answers questions but is not the audit target.
- Out-of-scope is optional but useful when the bundle sits inside a larger directory with files that look adjacent but are not part of this audit.

---

## Section 3 — Audit dimensions (the 7)

Codex evaluates the bundle along seven dimensions. Each dimension surfaces a specific class of pattern from spec §3:

### 3.1 Cross-reference integrity

**What to check:** Every claim cited to file X actually appears in file X at the cited location. Every back-pointer (file Y references file X) terminates at a real anchor. Wikilink-style references (`[[file]]` or `(file.md)`) resolve.

**Patterns surfaced:** Pattern A3 (mis-anchored citation), Pattern B5 (primary-source list mismatch).

### 3.2 Hallucination detection

**What to check:** Declarative claims about external entities (laws, decisions, sibling documents, prior studies) are checkable against ground truth provided in the bundle. Conditional claims about un-provided documents use conditional language, not declarative.

**Patterns surfaced:** Pattern A5 (sibling-document fabrication), Pattern A2 (pending-source assumed as fact), Pattern B5 (option-list overclaim), Pattern C1 (compression overclaim).

### 3.3 Primary-source integrity

**What to check:** Verbatim quotes match the primary source character-for-character within marked phrase boundaries. Quote scope does not creep beyond the verified anchor. Translations of foreign-language primary sources are independently verifiable.

**Patterns surfaced:** Pattern A4 (quote scope creep), and the cross-reference half of Pattern A3.

### 3.4 Internal coherence

**What to check:** A source cited in multiple sections receives compatible characterizations across sections. A claim qualified at one anchor is not contradicted at another anchor without explicit reconciliation. The bundle does not contain mutually-incompatible statements about the same proposition.

**Patterns surfaced:** Pattern A1 (legal-effect drift / cross-section internal contradiction).

### 3.5 Instrument quality (survey designer mode bundles only)

**What to check:** Items labelled "reverse-coded" pass the construct-equivalence test (see `psychometric_terminology_glossary.md`). IRB terminology in consent script matches the operational reality of data handling (see `irb_terminology_glossary.md`). Retrospective items use event-anchored phrasing when sample lacks a common date. Item phrasing is neutral and balanced.

**Patterns surfaced:** Pattern B1 (anonymity / confidentiality conflation), Pattern B2 (pseudo-reverse), Pattern B3 (calendar-anchored without shared event), Pattern B4 (leading items / chapter-vocabulary contamination).

### 3.6 Round-N framing

**What to check:** The audit's own framing is consistent with prior rounds. Findings closed in earlier rounds remain closed (no regression). New findings introduced by prior-round corrections are surfaced. Anchoring bias is named when the bundle has converged to a structure that resists fresh critique.

**Patterns surfaced:** Pattern D2 (convergence requires 3+ rounds), Pattern D3 (PARTIAL ≠ CLOSED).

### 3.7 COI adequacy (conflict-of-interest / disclosure adequacy)

**What to check:** Conflict-of-interest and reflexivity disclosures use explicit temporal bounds (year ranges, role-bounded periods, "former" prefix). Deictic temporal phrases ("during this period," "at the time," "currently") are absent or fully resolved by adjacent context. Disclosure obligations under publisher policy are met at abstract / executive-summary level, not only at body level.

**Patterns surfaced:** Pattern C2 (temporal ambiguity).

Note: word-count convention, 3–5% buffer adherence, and protected-hedge preservation against compression are **not** covered by §3.7. They are handled by the bundle-specific check in Section 4 (f) below — see the report_compiler_agent example for the expected `(f)` clause.

---

## Section 4 — Round-specific job

```
Round {N} job:
(a) Verify each round-{N-1} finding closed correctly. List by ID.
(b) Audit for new issues introduced by round-{N-1} corrections (cascade audit per feedback_cross_model_review_cascade_inconsistency.md).
(c) Run the 7 audit dimensions (§3.1–§3.7) plus the bundle-specific Section 4(f) check on the primary deliverables. Report each finding with the dimension or `4(f)` that surfaced it.
(d) Anchoring-bias residual check: for each finding closed in prior rounds, confirm the closure is not a wording change that left the failure mode operative (per feedback_lint_passes_but_prompt_silent.md).
(e) PARTIAL-vs-CLOSED check: every finding marked PARTIAL in prior rounds is either fully closed or remains open with a concrete remaining-work description.
(f) {bundle-specific check, e.g. "compression overclaim check: every claim in the abstract is at least as hedged as its anchor in the body"}
```

**Fill rules:**
- (a)–(e) ride verbatim every round (with N substitution).
- (f) is bundle-specific. The orchestrator picks the bundle-specific check based on which downstream agent produced the deliverable. For report_compiler_agent bundles, (f) is mandatory and combines three sub-checks; the others are single-check. Examples:
  - synthesis_agent bundle: cross-section consistency check on every source cited in 2+ sections.
  - research_architect_agent bundle: construct-equivalence test on every reverse-coded item.
  - report_compiler_agent bundle (mandatory three-part check): (i) word count = `len(body.split())` ≤ publisher cap minus 3–5% buffer per `word_count_conventions.md`; (ii) every entry of upstream `protected_hedges` block per `protected_hedging_phrases.md` appears verbatim in the abstract; (iii) no claim in the abstract is less hedged than its anchor in the body. Failure of any sub-check is a P1 finding.

---

## Section 5 — Convergence target

```
Convergence target: ZERO findings of ANY severity in one round.

Per feedback_codex_iterative_spec_review_to_zero.md: goal = 0 findings in a single round, NOT N rounds of "0 P1." A round with P2/P3 only still counts as un-converged. Iterate until one full round produces zero findings or until {fallback condition, e.g. "round 5 is reached and remaining findings are 'add counter, do not change rule' per feedback_codex_review_vs_resume_audit_scope.md"}.
```

**Fill rules:**
- The fallback condition is part of spec §5.2 stop conditions. Default fallback: "after 5 rounds, escalate remaining findings to user for ship-or-iterate decision."
- Do NOT loosen convergence to "0 P1+P2 findings" or "0 P1 findings" — those are weaker stop conditions that v3.6.7 replaces with the strict 0-anything bar.

---

## Section 6 — Output format

```
Output:
- Cumulative numbered findings (carry forward IDs from round 1; new findings get next available ID).
- For each finding: ID, severity (P1/P2/P3), dimension (one of §3.1–§3.7 or `4(f)` for bundle-specific failures), file:line anchor, one-line description, suggested fix.
- Do NOT propose fixes that change the spec; the spec is authoritative. Suggested fixes operate on the deliverables only.
- End with severity-bucket count summary: "Round {N}: P1×{n1} / P2×{n2} / P3×{n3} ({total} total)".
- If zero findings, end with: "Round {N}: 0 findings of any severity. Convergence reached."
```

**Fill rules:**
- The "do NOT propose fixes that change the spec" clause prevents codex from drifting into spec critique when the audit target is deliverables. If codex finds a spec issue, it should be raised separately, not folded into the deliverable audit.
- Severity bucket summary at the end is what the orchestrator parses to decide round-N+1 vs. ship.

---

## Section 7 — Anti-fake-audit guard (Pattern C3, mandatory)

**Critical clause that rides in every audit dispatch context:**

```
DO NOT simulate any audit step. DO NOT claim to have run codex/external review on your own output. The orchestrator runs codex audit afterward; output metadata must not claim audit-passed state. If you cannot complete a step, surface the gap explicitly rather than reporting a simulated pass.
```

**Why:** Sub-agents have been observed (see `feedback_subagent_tool_hallucination.md`) reporting that they ran codex audit and surfacing simulated findings, when in fact no audit ran. The deliverable then carries a fake audit-passed marker that downstream consumers trust. The guard above is verbatim what the agent prompts say, plus the orchestrator-side post-verification (spec §5.3) that reads audit transcript metadata and rejects deliverables claiming audit completion without matching transcript.

This guard rides in agent prompts AND in audit dispatch. The agent prompt forbids fake claims; the dispatch reminds the auditor not to accept fake claims at face value.

---

## Worked example: synthesis_agent Phase 2 audit, round 2

```
Audit round: 2 of 3
Previous rounds: Round 1: P1×3 / P2×7 / P3×2 (12 total); all P1 closed; 4 P2 closed; 3 P2 + 2 P3 carried.

Bundle scope: Phase 2 chapter deliverables — synthesis output for chapter 4

Authoritative context (commit a1b2c3d):

Primary deliverables (audit target):
- chapter4_synthesis.md (synthesis_agent output, 14k words across 6 sections)
- chapter4_evidence_inventory.md (effect inventory per source, synthesis_agent companion artefact)

Supporting context (do not audit; reference only):
- shared/contracts/passport/literature_corpus_entry.schema.json
- deep-research/agents/synthesis_agent.md (the agent prompt — for understanding patterns, not for audit)
- chapter4_bibliography.json (bibliography_agent output, V2_CLEAN — verified upstream)

Out-of-scope (do not read):
- chapter1-3 / chapter5+ deliverables (separate bundles)

Round 2 job:
(a) Verify each round-1 finding closed correctly. List by ID.
(b) Audit for new issues introduced by round-1 corrections.
(c) Run the 7 audit dimensions on the two primary deliverables.
(d) Anchoring-bias residual check on closed findings.
(e) PARTIAL-vs-CLOSED check.
(f) Cross-section consistency check: for every source cited in 2+ sections of chapter4_synthesis.md, verify the source's characterization is compatible across sections; flag any pair of sections that pull the source's effect in incompatible directions (Pattern A1).

Convergence target: ZERO findings of ANY severity in one round.
[+ standard fallback]

Output:
[+ standard output format]

DO NOT simulate any audit step. [+ standard Section 7 anti-fake-audit guard]
```

---

## Cross-references

- `shared/references/irb_terminology_glossary.md` — referenced by dimension §3.5.
- `shared/references/psychometric_terminology_glossary.md` — referenced by dimension §3.5.
- `shared/references/protected_hedging_phrases.md` — referenced by Section 4(f) report_compiler bundle check (sub-checks ii + iii).
- `shared/references/word_count_conventions.md` — referenced by Section 4(f) report_compiler bundle check (sub-check i).
- ARS feedback memory `feedback_codex_iterative_spec_review_to_zero.md` — convergence target rationale.
- ARS feedback memory `feedback_cross_model_review_cascade_inconsistency.md` — round-N+1 cascade audit rationale.
- ARS feedback memory `feedback_subagent_tool_hallucination.md` — anti-fake-audit guard rationale.
- ARS feedback memory `feedback_codex_xhigh_for_drift_audit.md` — model + reasoning-effort selection (gpt-5.5 + xhigh for high-blast-radius bundles).
