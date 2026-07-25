# Harness Retirement Audit — `academic-research-skills` (2026-07)

| | |
|-|-|
| Repo path | `~/Projects/academic-research-skills` |
| Branch / commit | `main @ 17c518b` |
| Date | 2026-07-01 |
| Target model | **Opus 4.8** (`claude-opus-4-8[1m]`) — inherited Claude Code session model |
| Scope | Issue #476 — the **22 Bucket A agents only** (agent prompt bodies, under the v3.9.2 Phase Boundary fence). NOT the ~11 non-Bucket-A agents in the same dirs (see manifest below). |
| Files scanned | 22 (`deep-research/agents/*.md` ×9, `academic-paper/agents/*.md` ×7, `academic-paper-reviewer/agents/*.md` ×6) — 8,111 prompt lines |
| Method | 3 parallel opus sub-agents (one per skill family) + first-party grep (Cat 1/3/5) + **independent codex cross-model challenge pass** |
| Auditor | `/harness-retirement` skill v0.1.0 |

### The exact 22 Bucket A files (manifest — resolves the "dir has 33 .md, report says 22" ambiguity codex raised)

- **deep-research (9):** `research_question`, `research_architect`, `bibliography`, `source_verification`, `synthesis`, `editor_in_chief`, `ethics_review`, `risk_of_bias`, `meta_analysis`
- **academic-paper (7):** `literature_strategist`, `structure_architect`, `draft_writer`, `citation_compliance`, `abstract_bilingual`, `peer_reviewer`, `formatter`
- **academic-paper-reviewer (6):** `eic`, `methodology_reviewer`, `domain_reviewer`, `perspective_reviewer`, `devils_advocate_reviewer`, `editorial_synthesizer`
- **NOT in scope** (present in the dirs, excluded by issue #476): `monitoring`, `timeline_extraction`, `devils_advocate` (deep-research), `socratic_mentor` (×2), `intake`, `argument_builder`, `visualization`, `revision_coach`, `field_analyst`, `shared/agents/compliance`. A future wider pass should cover these.

## Executive summary

- **Total findings**: **5 — all P2 (nice-to-have). Zero P0, zero P1.** (F-001..F-003 from the primary pass; F-004, F-005 added after the codex cross-model challenge — see "Cross-model challenge" below.)
- **By category** (against issue #476's six debt buckets):

  | Cat | Issue-#476 bucket | Count | Verdict |
  |-----|-------------------|------:|---------|
  | 1 — Hardcoded model IDs | Deprecated tool references / model IDs | **0** | Empty — grep-confirmed zero across all 22 files. `model: inherit` migration (#346/#347, v3.7.0) already cleaned this. |
  | 2 — Anti-hallucination patches | Defensive few-shot for model limits | **0** | Every candidate is contract-bound (citation existence/faithfulness) → iron-rule KEEP. This is the product, not debt. |
  | 3 — Sampling / budget overrides | Sonnet 3.x workarounds | **0** | grep-confirmed zero `temperature`/`max_tokens`/`budget_tokens`/`top_p` in bodies or frontmatter. |
  | 4 — Few-shot redundancy | Verbose CoT / few-shot | **1** (F-005) | One genuine basic-citation-format few-shot in draft_writer (caught by codex; my primary pass over-KEEP'd it as "style calibration"). |
  | 5 — Defensive scaffolding / verbose CoT | Pre-tool-use scaffolds / verbose CoT templates | **2** (F-002, F-004) | Format auto-detect ladder + a triple-nested step-by-step drafting template that hand-holds a model that no longer needs it. |
  | 6 — Negative framing | (cross-cuts several buckets) | **2** (F-001, F-003) | Two low-stakes stylistic prohibition lists with an existing positive twin. |

- **Suggested batch order**: F-004/F-005 → F-001 → F-002 → F-003 (all P2; opportunistic, next minor release — none block a tag).
- **Overall verdict**: **the 22 Bucket A agent bodies are in very good harness shape** — but "3 findings" was slightly too clean. The classic mechanical targets (hardcoded model IDs, sampling overrides, retry/repair loops, generic "don't hallucinate" patches) are **structurally absent**. The real residual debt is concentrated in **one agent — `draft_writer`** — which still carries pre-Opus-4.8 writing-process scaffolding (a triple-templated TEEL/step-by-step drafting algorithm + basic citation-format few-shot). All 5 findings are P2 stylistic/procedural trims; none blocks a tag. The previous audit (`harness-retirement-2026-06-10.md`, Fable-5 target, 73-file scope) found all 9 of ITS findings OUTSIDE the agent bodies (`shared/`, `commands/`, `SKILL.md`); this narrower body-only pass confirms the bodies are lean except for the `draft_writer` writing-harness cluster.

### Cross-model challenge (codex, 2026-07-01)

An independent codex consult pass was run specifically to attack this audit's conservatism ("a conservative audit that misses real debt is a failure, not a safe default"). Codex's verdict and my adjudication:

- **Accepted → F-004**: `draft_writer` "Detailed Execution Algorithm" (L186-225) + TEEL (L227-257) + a duplicate Paragraph-Structure block (L100-105) is obsolete writing-process templating, not a contract. Codex rated it P1; **I hold it at P2** — TEEL/fixed paragraph shape is partly a legitimate academic-writing *domain convention* (debt_patterns.md lists domain formatting as KEEP), and there is no eval showing output quality has regressed. Retire by *splitting* (keep TEEL as a one-line convention, drop the step-by-step process narration + the duplicate), not deleting. **codex's P1 dissent is recorded here for the user to overrule.**
- **Accepted → F-005**: `draft_writer` L107-119 Smith/Chen/Kim citation-format examples teach basic narrative/parenthetical forms a current model knows — genuine Cat 4 few-shot, not style calibration. My primary pass over-KEEP'd it.
- **Accepted (wording fix, not a new finding)**: the cross-file `Output Discipline` duplication should be logged as "real prompt-maintenance debt needing a shared-include refactor," not filed under "no debt / out of scope." Reworded in the Kept-as-debt section.
- **Accepted (report fix)**: added the exact 22-file manifest above — codex correctly noted the dirs hold 33 `.md` and the bare "22 scanned" line was ambiguous. (Codex read this as possible *incomplete coverage*; it is not — issue #476 scopes exactly these 22. The manifest removes the ambiguity.)
- **Rejected**: codex agreed F-003 is the weakest finding (possibly over-flagged, not under-rated) — consistent with my own "lowest-confidence P2" note. No change.

> ⚠️ **Before applying ANY finding**: run `python3 scripts/run_ci_pytest_manifest.py`. Several lints assert literal prose strings; a prose edit that forgets its lint mirror fails CI (and a lint that silently stops matching is a fake-green). All three findings below are prose-only and touch no contract/lint-mirrored line — but verify.

---

## Findings

### [F-001] `academic-paper/agents/abstract_bilingual_agent.md:122-135` — Category 6 (negative framing)

**Excerpt**
```
## Common Errors to Avoid
### English Abstract
- Starting with "This paper..." (vary openings)
- Vague findings ("results were significant")
...
### Chinese Abstract
- Translation tone (directly translating English grammar)
- Overuse of passive voice (Chinese prefers active voice)
...
```

**Why this is debt.** The file already carries a positive twin — the "Green flags for independent writing" block (L116-120) — covering the same terrain. This parallel count-heavy prohibition list restates negatives that Opus 4.8 avoids natively once given the positive green-flag targets. It is redundant weight, not a hard boundary.

**Proposed change.** *Trim, not delete.* Fold the two or three non-obvious items that aren't already implied by the green flags (e.g. "always define abbreviations in the abstract", "keep academic terminology consistent") into the existing positive guidance, then remove the prohibition-list framing.

**Iron-rule check.** Passed — not a Phase Boundary, not a citation contract, not a formatter gate. These are low-stakes stylistic writing-quality preferences (not silent-failure academic-integrity rules), and a positive twin already exists in the same file.

**Decision** — [ ] accept  [ ] reject  [ ] defer (annotate: _________________)

---

### [F-002] `academic-paper/agents/citation_compliance_agent.md:243-263` — Category 5 (defensive scaffolding, light)

**Excerpt**
```
Step 1: Sample Check (extract first 5 in-text citations)
Step 2: Confirm (check Reference List format)
Step 3: If unable to determine -> ask user; if user does not respond -> default to APA 7th
```

**Why this is debt.** The three-step "Sample → Confirm → ask/default" ladder is a determinism scaffold for citation-**format** auto-detection that Opus 4.8 resolves in a single pass. The multi-step decomposition is procedural padding. The *fallback rule itself* (default APA 7th) is worth keeping.

**Proposed change.** *Trim.* Collapse the 3-step procedure into the format-signature table (the `(Author, Year) → APA` / `[N] → IEEE` mappings) plus the one-line default rule. Keep "default to APA 7th" verbatim.

**Iron-rule check.** Passed — this is format-**style** detection, NOT citation existence/faithfulness verification. It is not one of the named citation contracts (R-L3-1, R-CIM, three-firm-rules), not a formatter refusal rule, not a hard boundary. The anti-fabrication machinery in this same agent (plagiarism/retraction decision tree, "STOP, flag as potential fabrication", L111-139) is **untouched** and stays.

**Decision** — [ ] accept  [ ] reject  [ ] defer (annotate: _________________)

---

### [F-003] `deep-research/agents/research_question_agent.md:128-137` — Category 6 (negative framing)

**Excerpt**
```
### What It Does NOT Do
- Does not directly produce an RQ Brief ...
- Does not score FINER on behalf of the user ...
- Does not proactively generate candidate RQs ...
### What It Does Instead
- Guides the user to derive the RQ themselves ...
```

**Why this is debt.** The Socratic-mode behaviour is defined first as three "does not" prohibitions, then restated positively immediately below. Opus 4.8 follows the positive "guide the user to derive it themselves" framing (L135-137) reliably without the mirror-image prohibition list; the negative block is mostly redundant.

**Proposed change.** *Replace with positive framing.* Fold the three "Does not…" bullets into the existing "What It Does Instead" section as positive directives — e.g. "Guide the user to derive the RQ rather than producing the Brief directly; use FINER as guiding questions rather than a scoring table; withhold candidate RQs until the 5-round F1 failure path (see `failure_paths F1`)." Keep the F1 escape-hatch reference intact.

**Iron-rule check.** Passed — not a Phase Boundary, not a PATTERN PROTECTION block, not a citation rule. These negatives describe *mode behaviour* (Socratic vs full), not a hard closed prohibition, and the positive rephrase is unambiguous. **Flagged as the lowest-confidence P2** because the negation still carries a slight mode-contrast signal that the positive form loses — a "reject/defer" here is entirely defensible.

**Decision** — [ ] accept  [ ] reject  [ ] defer (annotate: _________________)

---

### [F-004] `academic-paper/agents/draft_writer_agent.md:100-105, 186-225, 227-257` — Category 5 (verbose CoT / process templating) — *added by codex challenge*

**Excerpt**
```
## Detailed Execution Algorithm
  Writing flow for each section:
  1. Write Opening paragraph ...  2. Write Body paragraphs ...  3. Each paragraph follows TEEL ...
### Paragraph Structure Rules (TEEL Framework)  [T—Topic / E—Evidence / E—Explanation / L—Link]
```

**Why this is debt.** The drafting behaviour is templated **three times**: a short "Paragraph Structure" block (L100-105), then a step-by-step "Detailed Execution Algorithm" (L186-225), then a full TEEL framework with fixed sentence-count-per-component and paragraph-length rules (L227-257). This is exactly the kind of hand-holding "how to think" process template a strong model no longer needs; keeping it nudges Opus 4.8 toward more formulaic, mechanical academic prose. It is **not** a machine-checked contract (no lint pin, no `<!--ref:-->` marker, no fail-closed gate).

**Why it is P2, not P1 (codex rated it P1 — dissent recorded).** TEEL and fixed paragraph shape are **partly a legitimate academic-writing domain convention**, which `debt_patterns.md` lists as KEEP; and no eval yet shows drafting quality has regressed. Retiring the *wrong half* (the convention, not the templating) would degrade structural consistency some venues expect.

**Proposed change.** *Split, don't delete.* Keep a single one-line TEEL convention ("each body paragraph: topic → evidence-with-citation → analysis → link; ~120-200 EN words") and the word-count target rule. **Delete** the duplicate L100-105 block and the step-by-step "Detailed Execution Algorithm" process narration (L186-225) — Opus 4.8 sequences a draft without a numbered flowchart. Measure one draft before/after for structural regression.

**Iron-rule check.** Passed — not a Phase Boundary, not a citation contract, not a formatter gate. The retirement is scoped to the *process narration + duplication*, preserving the domain-convention core. Flagged P2 because the split requires judgment; a lazy full-delete would be a false-positive retirement.

**Decision** — [ ] accept  [ ] reject  [ ] defer (annotate: _________________)  ← *codex recommends P1/accept; auditor recommends P2*

---

### [F-005] `academic-paper/agents/draft_writer_agent.md:107-119` — Category 4 (few-shot redundancy) — *added by codex challenge*

**Excerpt**
```
### Citation Integration
**Narrative**: > Smith (2024) demonstrated that AI-assisted QA reduces evaluation variance by 23%.
**Parenthetical**: > ...significantly (Smith, 2024).
**Multiple sources**: > ...(Chen, 2023; Kim, 2024; Smith, 2024).
```

**Why this is debt.** These four Smith/Chen/Kim examples teach *basic* narrative vs parenthetical vs multi-source vs direct-quote citation forms — a format Opus 4.8 already produces correctly from the instruction alone. They are not edge-case encodings and not style/voice calibration (the fake citations carry no house voice); they are the textbook few-shot pattern the audit is meant to trim. My primary pass over-KEEP'd this as "Style Calibration references."

**Proposed change.** *Trim to 0-1.* Keep at most the direct-quote example (the one with a non-obvious rule: "use sparingly, cite page number"); delete the narrative/parenthetical/multiple-source trio and state the rule in one sentence.

**Iron-rule check.** Passed — not a domain-jargon anchor (the forms are standard across all citation styles), not style calibration, not an edge case. The anti-fabrication citation *contracts* (R-L3-1, R-CIM at L491+) are untouched.

**Decision** — [ ] accept  [ ] reject  [ ] defer (annotate: _________________)

---

## Kept as debt (iron rule filtered these OUT — recorded so the next audit doesn't re-surface them)

The audit examined and **deliberately did not flag** the following. This list is as important as the findings: it proves the load-bearing patterns were checked, not missed.

**Phase Boundary fence (the v3.9.2 hard fence itself):**
- All **22** `## Phase Boundary (v3.9.2)` blocks + their `You MUST NOT:` phase-inflation lists. **KEEP** — enforcement is prompt-level-only (deterministic PreToolUse hook deferred to v3.10 active conductor #134); these negatives are the *only* thing preventing phase-inflation and the failure would be **silent**. Retiring them is exactly the false-positive the iron rule warns against.

**Named citation / anti-fabrication contracts (the product's core value — silent + high-stakes):**
- `draft_writer` & `synthesis` Two-Layer / Three-Layer Citation Emission, `<!--ref:-->` / `<!--anchor:-->` machinery, R-L3-1-A/B/C, R-CIM-A/B/C/D. **KEEP.**
- `bibliography` contamination_signals / Semantic Scholar + OpenAlex + Crossref triangulation / trust-chain refusal-on-uncertain (L285-404). **KEEP** — tool-grounded, not boilerplate.
- `source_verification` Tier 0/1/2 verification, "Red Flags for Hallucinated References", `S2_NOT_FOUND`/`FABRICATED` branches. **KEEP** — real API-grounded protocol; the degradation branch handles API outage, not model incapacity.
- `citation_compliance` plagiarism/retraction decision tree + "STOP, flag as potential fabrication" + "Must not silently resolve". **KEEP.**
- `ethics_review` "no ghost citations" / "no fabricated references (even one)" blocking condition. **KEEP.**
- `lit_strategist` Iron Rules 1-4 + three firm rules / trust-chain. **KEEP.**

**Determinism / anti-anchoring / anti-sycophancy contracts (the reviewer skill's product value):**
- `devils_advocate_reviewer` Attack-Intensity Preservation, "score rebuttal 1-5 before conceding", "no concession below ≥4", frame-lock detection, concession-rate tracking (L305-358). **KEEP** — the iron rule names this verbatim as the core anti-sycophancy feature.
- All 6 reviewers' v3.6.2 Sprint Contract Phase-1-paper-blind / Phase-2 `<phase1_output>`-as-data structure. **KEEP** — designed anti-anchoring machinery, not a hallucination patch.
- `editorial_synthesizer` "arithmetic not interpretive" + Forbidden-operations list ("do NOT average/soften/re-interpret", L46-70). **KEEP** — determinism contract.
- Surface-Form Parity blocks (#216) in `devils_advocate_reviewer` + `editorial_synthesizer` (machine-delimited `SURFACE-FORM-PARITY-BLOCK:BEGIN/END`). **KEEP** — verdict-time bias gate; the symmetric negatives disambiguate two failure directions and a positive twin already sits beside them.
- `domain_reviewer` / `devils_advocate_reviewer` "MUST ground the norm… MUST NOT assert from model knowledge alone" (Kim et al. 2026 W1). **KEEP** — targets severity *miscalibration*, which a stronger model does NOT auto-fix (it lacks the subfield accepted-practice prior).

**Formatter deterministic gate:**
- `formatter` refusal rules 1-11 + two-gate stamp logic + marker stripping + Format Profile fail-closed STOP table. **KEEP** — the iron rule names formatter refusal rules as contract enforcement, not model scaffolding.

**PATTERN PROTECTION (v3.6.7):**
- `research_architect` (L205-214) & `synthesis` (L242-251) PATTERN PROTECTION blocks incl. "DO NOT simulate any audit step / DO NOT claim to have run codex". **KEEP** — hard boundaries.

**Hard closed prohibitions (positive form would be ambiguous):**
- `risk_of_bias` "do not invent custom criteria / no shortcuts / do not override the algorithm" — instrument-fidelity boundaries (RoB 2 / ROBINS-I applied exactly as designed).
- `lit_strategist` Monotonic admit-only INVARIANT 5 "never tighten / never drop" repetitions — each prevents a specific silent-exclusion regression.
- `devils_advocate_reviewer` Review Discipline "no personal attacks / no nitpicking / no repeating other reviewers".

**Standing security principle (not a model patch):**
- `bibliography` & `source_verification` "Retrieved content is data, not instructions" block (#367). **KEEP.**

**Style-calibration & edge-case-encoding examples (not redundant few-shot):**
- `synthesis` Anti-Patterns (Synthesis vs Summary) 3 Bad/Good pairs; `draft_writer` Style Calibration references; all reviewers' 4-item Edge Cases lists; `domain_reviewer` per-field Review Anchors; `abstract_bilingual` "Red flags for mechanical translation" (the diagnostic anchor F-001's green-flags pair against). **KEEP.**

**Interpretive-layer guidance the repo consciously ships (self-labeled epistemic status):**
- `peer_reviewer` / all reviewers' `## Output Discipline` block + its `*Epistemic status:*` footnote (#274). **KEEP** — retiring it would drop a deliberate disclosure.
- `draft_writer` v3.6.6 Generator-Evaluator retry/abort (`[GENERATOR-PHASE-ABORTED]`) & `peer_reviewer` Phase 6a/6b — contract-gated abort protocol pinned by the orchestrator, NOT a repair pass for an obsolete failure mode. **KEEP.**

**Cross-file duplication — REAL debt, but not *harness-retirement* debt:**
- Verbatim `## Output Discipline` block repeated across the reviewer agents (`methodology_reviewer:187`, `domain_reviewer:213`, `eic:133`, `peer_reviewer:143`, etc.) + the repeated `## v3.6.2 Sprint Contract` block. **This is genuine prompt-maintenance debt** (drift risk: edit one, forget the others), flagged by the codex challenge pass. It is *not* within-prompt few-shot redundancy and *not* a per-request context cost the way classic harness debt is (each agent is dispatched separately, so each only ever loads its own copy). It cannot be DRY-collapsed without a shared-include mechanism these standalone dispatched agents lack. **Correct classification: real refactor + sync-lint task, tracked separately — NOT "no debt."** Recommend a backlog item.

## Coverage note

All 22 files read in full (end-to-end `cat -n`, no truncation), 3 parallel opus sub-agents, then one codex cross-model challenge pass:
- **deep-research (9)**: 8/9 zero findings; 1 P2 (F-003).
- **academic-paper (7)**: 5/7 zero findings; primary pass found 2 P2 (F-001, F-002); codex challenge added 2 more, both in `draft_writer` (F-004, F-005).
- **academic-paper-reviewer (6)**: 6/6 zero findings (codex re-examined the reviewer anti-sycophancy/Output-Discipline surface and confirmed no *retirable* debt — only the cross-file duplication maintainability item).

First-party grep independently confirmed **zero** hardcoded model IDs, **zero** sampling/budget overrides, and **zero** retry/repair/schema-revalidation loops across all 22 files — so debt categories 1 and 3 are empty at the grep level, corroborating the sub-agent reads. (Category 5 as *verbose CoT templating* is NOT empty — F-004; the grep only rules out the retry/repair form.)

**Value of the two-track pass:** the single-track (sub-agent) result was "3 findings, all in low-stakes stylistic prose." The codex challenge overturned the premise that `draft_writer`'s example/template blocks were all load-bearing "style calibration," surfacing the one agent (`draft_writer`) that actually carries pre-Opus-4.8 writing-harness scaffolding. Net: +2 findings, +1 reclassification, +1 coverage-manifest fix. No fabricated findings on either side.

## Apply log (filled during a separate apply turn — never bundled with the audit)

| Finding | Action | Commit | Verified |
|---------|--------|--------|----------|
| F-001 | pending user decision | — | — |
| F-002 | pending user decision | — | — |
| F-003 | pending user decision | — | — |
| F-004 | pending user decision (codex P1 / auditor P2 — user breaks tie) | — | — |
| F-005 | pending user decision | — | — |

## Next audit

- Suggested date: after the next minor release, or on the next default-model upgrade.
- Re-scan: same 22 Bucket A files, plus any new agent files added since.
- Carry forward: this "Kept as debt" list — verify each keep-reason still holds (especially whether the v3.10 deterministic Phase-Boundary hook has landed, which would change the enforcement calculus for the Phase Boundary fence).
- Note: the broader `shared/` + `commands/` + `SKILL.md` surface (where the 2026-06-10 audit's 9 findings lived) is OUT of this issue's scope but is where real debt tends to accumulate — worth a separate wider pass at the next model bump.
