# Harness Retirement Audit — `academic-research-skills` (2026-07-04, continuation pass)

| | |
|-|-|
| Repo path | `~/Projects/academic-research-skills` |
| Branch / commit | `main @ d3c2876` |
| Date | 2026-07-04 |
| Target model | **Fable 5** (`claude-fable-5`) — inherited Claude Code session model |
| Scope | The **17 agent files never covered by a deep per-file pass** (excluded from issue #476's 22-file Bucket A manifest), + 2 commands added since 2026-06-10 (`ars-3w`, `ars-rebuttal-audit`), + 3 carry-forward re-checks from the two prior audits |
| Files scanned | 19 prompt files (~6,900 lines), all read end-to-end |
| Method | 4 parallel Fable 5 sub-agents (one per skill family + one residual/re-check batch), per-finding lint-mirror grep, + **independent codex cross-model challenge pass** (see below) |
| Auditor | `/harness-retirement` skill v0.1.0 |

### Scanned manifest (the 17 + 2)

- **academic-pipeline (5):** `pipeline_orchestrator`, `integrity_verification`, `state_tracker`, `claim_ref_alignment_audit`, `collaboration_depth`
- **deep-research (5):** `socratic_mentor`, `report_compiler`, `monitoring`, `devils_advocate`, `timeline_extraction`
- **academic-paper (5):** `socratic_mentor`, `visualization`, `intake`, `revision_coach`, `argument_builder`
- **academic-paper-reviewer (1):** `field_analyst` · **shared (1):** `compliance_agent`
- **commands (2):** `ars-3w.md`, `ars-rebuttal-audit.md`
- Top-level `agents/*.md` mirrors excluded (byte-identical copies, CI-pinned by `check_agents_mirror_sync.py`) — but two findings require mirror re-sync on apply (B4-F01, B2-F03).

## Executive summary

- **Total findings (post-challenge): 13 — 2 P1, 11 P2. Zero P0.** 10 of 19 files are finding-free. The codex challenge upgraded the two live contradictions to P1 (auditor concurs) and added one new P2 (B4-F03, with auditor dissent recorded).
- **By category:**

  | Cat | Count | Findings |
  |-----|------:|----------|
  | 1 — Hardcoded model IDs / stale factual pins | 2 | B4-F01 (stale enforcement sentence, repo-wide), B4-F02 (SETUP gpt-5.4 leftover) |
  | 4 — Few-shot redundancy | 5 | B3-F01, B1-F01, B1-F03, B2-F03, B4-F03 (challenge-added) |
  | 5 — Defensive scaffolding / duplication / stale constants | 6 | B2-F01 (**P1**), B2-F02, B3-F02 (**P1**), B3-F03, B1-F02, B3-F04 |
  | 2, 3, 6 | 0 | — (Cat 6 resolved via the F-007 closure below) |

- **Dominant disease of this pass: duplication-drift.** Both `socratic_mentor` agents wrote their convergence/auto-end rules twice (deep-research: B2-F01/F02; academic-paper: B3-F02), and both duplicated copies have **already drifted into live self-contradictions** (15-vs-30 round threshold; a stale 10/15-round constant that bypasses the v3.0 exploratory protection layer). The orchestrator's user-response dispatch is written three times with one row missing from the authoritative table (B1-F02). These are not just token weight — the duplicates are actively contradicting the current rules.
- **2026-06-10 F-007 (deferred negative-framing reframe) is hereby CLOSED as "verified, no rewrite needed."** All three top-density files were re-examined sentence-by-sentence: `pipeline_orchestrator` (57 hits ≈ 31 rule sites), `integrity_verification` (29 ≈ 21 sites), deep-research `socratic_mentor` (44/44) — **zero safely-reframeable negatives**. The density lives in gate/contract semantics, anti-sycophancy machinery, flag-gated product boundaries, and incident-born patches (several lint-pinned verbatim). The correct disposition is *reclassified as contract*, not rewritten. The count growth since 2026-06 (33→44 etc.) comes from new flag-gated contract blocks, not from decayed scaffolding.
- **Suggested batch order (post-challenge):** B2-F01 + B3-F02 first (the two **P1** live contradictions; each needs one user threshold decision) → B4-F02 (mechanical, challenge-amended scope) → B4-F01 (one sentence × 29 surfaces, lint-safe wording verified) → B2-F02 + B1-F02 (dedup/merge) → B3-F01/B3-F03/B1-F01/B1-F03/B2-F03/B4-F03 (few-shot & narration trims) → B3-F04 (weakest, reject defensible).

## Carry-forward re-check verdicts

**B-1 — Phase Boundary fence keep-reason (2026-07 audit) — verdict: all 23 fence blocks stay KEEP; keep-reason rewritten; one new finding (B4-F01).**
The 2026-07 keep-reason ("enforcement is prompt-level-only; deterministic hook deferred to #134") was already false when written: #134 closed COMPLETED on 2026-06-01 via PR #294, which shipped a deterministic PreToolUse write-scope guard (23-agent manifest, structured-write globs, Bash deny-all for fenced agents). Cross-checking guard coverage against fence clauses: only the `MUST NOT WRITE files in phase{M}_*/` clause is machine-covered, and **only under the plugin install** — the git-clone + symlink track (first-class since v3.7.0) and non-Claude-Code runtimes load no hooks, and the #294 spec itself designates the prose blocks as the documented fallback layer and the human-readable mirror of the machine layer. All other clauses (deliverable-content overreach, persona simulation, "helpfully" continuing, MAY READ read-direction, return-control) are pure-prose behaviors outside any guard's reach. **No fence clause is trimmed.** New keep-reason: *WRITE clause = degradation layer for non-hook installs + designed human-readable mirror of the machine layer (spec §3.5); all other clauses = sole defense for prose-level overreach.* The stale enforcement status sentence itself is B4-F01.

**B-2 — command model routing — verdict: clean, no finding.** 16 commands: 13 × `model: sonnet` (11 original + the 2 new), 3 heavy commands with no model key (inherit session model, per 2026-06-10 F-004 apply). Zero `model: opus`, zero haiku, zero hardcoded IDs. The two "opus" strings in command bodies are historical notes about the retired floor — records, not pins.

**B-3 — cross-model verifier lineup — verdict: canonical doc internally consistent; one downstream leak found (B4-F02).** `shared/cross_model_verification.md` is self-consistent post-F-003 (gpt-5.5/gpt-5.5-pro table, `gpt-*` prefix glob immune to the F-003 bug class, judge default `gpt-5.5-xhigh` consistent). `docs/SETUP.md` + zh-TW twin missed the 2026-06-10 migration.

⚠️ **Before applying ANY finding**: run `python3 scripts/run_ci_pytest_manifest.py`. Every finding below carries a per-finding lint-mirror verdict (grepped against `scripts/` + `.github/workflows/`), but the full suite is the gate. Two findings touch byte-identical mirror pairs — re-sync `agents/*.md` copies in the same commit or `check_agents_mirror_sync.py` fails CI.

---

## Findings

### [B4-F01] 23 agent files (`## Phase Boundary` blocks) + 2 mirrors + 4 `SKILL.md` — stale enforcement status sentence — Cat 1-type stale pin · P2 · confidence high

**Excerpt** (`deep-research/agents/synthesis_agent.md:27`, same-shape sentence at all 29 surfaces)
```
**Enforcement (v3.9.2):** prompt-level only. Advisory verifier (scripts/check_pipeline_integrity.py)
can detect violations post-hoc. Deterministic PreToolUse hook deferred to v3.10 active conductor (#134).
```
**Why debt.** False since PR #294 (2026-06-01): the deterministic write-scope guard is shipped and live (`hooks/hooks.json` → `run_guard.sh` → `scripts/ars_write_scope_guard.py`, 23-agent manifest). Every dispatch tells the agent and every maintainer that no machine layer exists when one does; the 2026-07 audit's keep-reason was itself written on this false premise.
**Proposed change.** Keep the lint-pinned `Enforcement (v3.9.2):` prefix; rewrite the sentence body to state both layers: prompt-level fence + advisory post-hoc verifier; deterministic PreToolUse write-scope guard since #134 rescope (PR #294) under the plugin install (structured writes fenced to `allowed_write_globs`, Bash denied for fenced agents); symlink/non-CC installs degrade to this prose fence. Sync the 4 SKILL.md same-shape sentences; byte-resync the 2 mirrors.
**Iron-rule check.** Passed — corrects a factual statement *beside* the fence; all prohibition clauses untouched (see B-1 verdict).
**Lint-mirror.** `check_v3_9_2_phase_boundary.py` requires only the literal markers `## Phase Boundary (v3.9.2|v3.9.4)`, `MUST NOT`, `MAY READ`, `Enforcement (v3.9.2|v3.9.4)` (regex verified L101-115) — rewrite is green if the prefix survives. `check_agents_mirror_sync.py` forces mirror re-sync. No lint pins "prompt-level only" / "deferred to v3.10".
**Challenge correction (codex, accepted).** Phrase the rewrite as *hook-registered vs hook-absent environments*, not "plugin install vs symlink": `ars_write_scope_guard.py:474-480` resolves git-clone/symlink roots too when the hook is registered, and `run_guard.sh` passes through on guard failure — the accurate split is "where the PreToolUse hook runs, the machine layer enforces; elsewhere this prose fence is the enforcement layer."

**Decision** — [ ] accept  [ ] reject  [ ] defer (annotate: _________________)

---

### [B4-F02] `docs/SETUP.md:151,155` + `docs/SETUP.zh-TW.md:151,155` — Cat 1 (hardcoded model ID drift) · P2 · confidence high

**Excerpt**
```
export OPENAI_API_KEY="sk-your-key-here"  # For GPT-5.4 Pro
export ARS_CROSS_MODEL="gpt-5.4-pro"      # Best reasoning
```
**Why debt.** The 2026-06-10 F-003 lineup migration fixed the canonical doc but missed SETUP: new users are taught to export a legacy model labeled "Best reasoning", contradicting the canonical table (gpt-5.5-pro = strongest). Functionally harmless (the `gpt-*` glob accepts it); pedagogically wrong.
**Proposed change.** Both files, same PR: `ARS_CROSS_MODEL="gpt-5.5-pro"  # Strongest reasoning (premium ~6× gpt-5.5)` — or recommend `gpt-5.5` to match the canonical recommended pair. **Challenge amendment (codex, accepted):** the stale surface is six lines per language, not two — also `docs/SETUP.md:3,145,172` + `docs/SETUP.zh-TW.md:3,145,172` ("Claude Opus 4.8" and GPT-5.4 Pro pricing prose). Fix all in the same PR.
**Iron-rule check.** Passed — live install guide, not a benchmark pin or historical record.
**Lint-mirror.** None (`check_cross_model_verification_sync.py` scans only the canonical doc; zh-TW duality lint compares H2 structure + version markers only — edit both files in one PR).

**Decision** — [ ] accept  [ ] reject  [ ] defer (annotate: _________________)

---

### [B2-F01] `deep-research/agents/socratic_mentor_agent.md:613,642` — Cat 5 (stale constants, pre-v3.0 residue) · **P1** (challenge-upgraded; auditor concurs) · confidence high

**Excerpt**
```
L613: - If **no convergence after 10 rounds** … → gently suggest switching to `full` mode…
L642: At the end of the dialogue (Layer 5 completed or 15-round limit reached), compile all INSIGHTs…
```
**Why debt.** Both constants predate the v3.0 Intent Detection layer (40/60 max rounds, 10/15 stagnation with exploratory carve-out, exploratory auto-convergence disabled). L642's "15-round limit" matches no current auto-end condition; L613 lacks the exploratory carve-out and contradicts L570/L598. Followed literally, L642 ends the dialogue before a typical session completes and bypasses the entire exploratory protection layer. A live contradiction, not just weight.
**Proposed change.** L642 → "(Layer 5 completed or max-round limit reached — 40 goal-oriented / 60 exploratory)". Delete L613-614 (fully covered by Auto-End Triggers 2/3 at L596-600); at minimum align to "10 goal-oriented / 15 exploratory".
**Iron-rule check.** Passed — the rules themselves (40/60, 10/15, carve-out) are preserved; only the contradicting stale copies go.
**Lint-mirror.** None ("15-round", "no convergence after 10 rounds", "Auto-End", "STAGNATION": 0 hits in scripts/ + workflows).

**Decision** — [ ] accept  [ ] reject  [ ] defer (annotate: _________________)

---

### [B2-F02] `deep-research/agents/socratic_mentor_agent.md:545-551 vs 594-614` (also 570 vs 598) — Cat 5 (repetition-as-reinforcement) · P2 · confidence medium

**Excerpt**
```
L545: ### Auto-End Conditions (Precise)   [4 conditions]
L594: #### Auto-End Trigger               [nearly the same 4, restated]
L570 / L598: stagnation threshold (10 goal-oriented / 15 exploratory) — stated twice
```
**Why debt.** The full end-condition set is stated twice (plus a third partial restatement at L613-614 = B2-F01). Near-repetition was a weak-model reading aid; under Fable 5 it is pure drift substrate — the B2-F01 constant divergence occurred *on the duplicated copy*.
**Proposed change.** Merge L594-599 into the L545-551 authoritative list; hang the closing-summary template (L602-611) under the merged list; keep one stagnation statement. Preserve the exploratory carve-out text verbatim.
**Iron-rule check.** Passed — dedup, zero rule deletion; anti-sycophancy (Health Indicator), probe blocks, Kong boundaries untouched.
**Lint-mirror.** None (0 hits, incl. "Convergence Mechanism").

**Decision** — [ ] accept  [ ] reject  [ ] defer (annotate: _________________)

---

### [B3-F02] `academic-paper/agents/socratic_mentor_agent.md:438-445 vs 504-516` — Cat 5 (duplicated + **conflicting** convergence scaffolding) · **P1** (challenge-upgraded; auditor concurs) · confidence high

**Excerpt**
```
L445: | > 30 total rounds without completing all chapters | Suggest switching to `outline-only` mode … |
L510: - All 6 chapters + Stress Test typically takes 20-30 dialogue rounds
L515: - If the entire process exceeds 15 rounds without completing all chapters → suggest switching to outline-only
```
**Why debt.** The same auto-end/convergence machinery is written twice ("Auto-End Rules" table vs "Non-Convergence Handling" bullets) and has drifted into direct conflict: >30 in one copy, >15 in the other — while the file itself says a typical run takes 20-30 rounds. Followed literally, L515 advises quitting before a typical successful session finishes. Same disease as B2-F01/F02, independently evolved in the sibling agent.
**Proposed change.** Merge into a single Auto-End Rules table under Convergence Criteria. **Threshold value (30 vs 15) is a user call** — 30 is consistent with "typical 20-30"; 15 appears to be the stale value. Fold the two unique rules (L513 5-round chapter summarize-first; L516 user-initiated stop → save) into the same table; delete the duplicate bullets. Mid-Process Save (L518-528) untouched.
**Iron-rule check.** Passed — conversation-pacing parameters, not an integrity gate; all unique rules survive the merge.
**Lint-mirror.** None for this span. ⚠️ Same file L27-64 (Wording-Pattern Advisory, Kong #257) is literal-anchored by `scripts/test_check_rq_framing_patterns.py:66-78` — the merge must not touch that section.

**Decision** — [ ] accept  [ ] reject  [ ] defer (annotate: _________________)  ← includes the 30-vs-15 threshold call

---

### [B3-F01] `academic-paper/agents/socratic_mentor_agent.md:449-500` (edit span 455-489) — Cat 4 (few-shot redundancy) · P2 · confidence medium

**Excerpt**
```
#### 1. Clarifying Questions
| Template | When to Use | Example |
| "When you say X, do you mean A or B?" | User uses ambiguous terms | "…internal QA processes or external accreditation?" |
(4 question types × 3 template/example rows = 12 worked examples)
```
**Why debt.** The four-type taxonomy + per-chapter ≥1-of-each rule + distribution matrix (L491-500) are product spec — KEEP. But 12 rows of generic "here is what a clarifying question looks like" teach a weak model basic Socratic question forms; Fable 5 produces these natively from the type definitions ("senior doctoral advisor" persona). All happy-path, no edge cases, no house voice (tone owned by a separate section). Same class as the #478-retired draft_writer few-shot.
**Proposed change.** Trim — keep type names + Purpose lines + the L491-500 distribution table verbatim; cut each 3-row template table to ≤1 row or delete the tables (~35-40 lines).
**Iron-rule check.** Passed — not style calibration (tone has its own section), not edge-case spec, not jargon anchoring; the Socratic no-drafting product behavior fully preserved.
**Lint-mirror.** None for this span (same-file Kong #257 caveat as B3-F02).

**Decision** — [ ] accept  [ ] reject  [ ] defer (annotate: _________________)

---

### [B3-F03] `academic-paper/agents/visualization_agent.md:385-452` (edit span ~397-422, Steps 2-6 narration only) — Cat 5 (verbose process narration) · P2 · confidence medium

**Excerpt**
```
## Detailed Execution Algorithm
Step 2: Chart Type Selection — 2.1 For each candidate, apply the Chart Type Decision Logic …
Step 3: Code Generation — 3.1 Select language … 3.2 Apply APA 7.0 figure settings …
Step 6: Quality Check — 6.1 Run all 10 mandatory checks …
```
**Why debt.** Same-named, same-shaped block as the 2026-07 F-004 (draft_writer "Detailed Execution Algorithm"): Steps 2-6 re-narrate specs that already exist as their own sections (decision tree L43-73, code standards L205-260, caption spec L131-161, LaTeX L164-199, Quality Gates L266-279). Dual-written = drift risk. Step 1 (unique), Step 6.5 (VLM capability degradation), Step 6.6 (#261 fidelity-gate contract), Step 7 are NOT debt.
**Proposed change.** Split — Steps 2-6 each collapse to one pointer line at their owning section; Steps 1, 6.5, 6.6, 7 byte-untouched (~20-25 lines saved). A lazy full-delete would be a false-positive retirement.
**Iron-rule check.** Passed — #261 contract, VLM protocol, Quality Gates table body untouched.
**Lint-mirror.** None ("Detailed Execution Algorithm", "figure_table_trace" etc.: path-level hits only).

**Decision** — [ ] accept  [ ] reject  [ ] defer (annotate: _________________)

---

### [B1-F02] `academic-pipeline/agents/pipeline_orchestrator_agent.md:164-172` (vs 146-155, 322-337) — Cat 5 (procedural duplication) · P2 · confidence medium

**Excerpt**
```
5. Wait for user response
5. Based on user response, decide:
   - "continue" "yes" → increment consecutive_continue_count; proceed …
   (7 bullets: adjust / view progress / redo / skip / abort …)
```
**Why debt.** User-response dispatch is written three times (Steps sub-list; §User Engagement Tracking; the authoritative §Checkpoint Confirmation Semantics table). Drift already present: the sub-list's `view progress` is missing from the authoritative table. Duplicate step number "5." is a companion bug.
**Proposed change.** Collapse to "5. Wait for user response; act per §Checkpoint Confirmation Semantics; update `consecutive_continue_count` per §User Engagement Tracking." Same PR: add the missing `view progress` row to the Semantics table (reset count; show Dashboard; no state change).
**Iron-rule check.** Passed — skip validation, MANDATORY semantics, observer dispatch, L175 IRON RULE untouched; table becomes a strict superset before the sub-list is removed.
**Lint-mirror.** Two lints watch this *section* but not this span (verified): `check_spec_consistency.py:187-202` pins the L133 status-line row + expect_absent "auto-continue in 5 seconds"; `check_collaboration_depth_rubric.py:103-134` pins the step-3 dispatch anchor. Target strings: 0 hits.

**Decision** — [ ] accept  [ ] reject  [ ] defer (annotate: _________________)

---

### [B1-F01] `academic-pipeline/agents/pipeline_orchestrator_agent.md:69-76` — Cat 4 (few-shot redundancy) · P2 · confidence medium

**Excerpt**
```
Example rendering (no `pending_decision`, no override):
### Resume Acknowledged
- Hash: a3f2b7c9d0e1 …
```
**Why debt.** The normative template (L57-63) + bracket-omission rule (L65) fully define the output; this happy-path substitution adds zero marginal information. The second example (L78-88, two-stage `pending_decision` resolution) encodes edge-case information the template cannot — KEEP. Same "trim to 0-1" precedent as 2026-07 F-005.
**Proposed change.** Delete L69-76 (incl. heading); keep L78-88.
**Iron-rule check.** Passed — `[PASSPORT-RESET:]` machine anchor, hash serialization, resume obligations 1-11, iron rules 1-9 untouched.
**Lint-mirror.** None (verified against `check_passport_reset_contract.py` + `check_spec_consistency.py:656-664` — pinned literals live at L199/L277, untouched).

**Decision** — [ ] accept  [ ] reject  [ ] defer (annotate: _________________)

---

### [B1-F03] `academic-pipeline/agents/state_tracker_agent.md:95-109,163-178` — Cat 4 (verbose exemplar) · P2 · confidence medium

**Excerpt**
```
"2":  { "name": "WRITE", … }      (15-line full-field instance)
"3p": { "name": "RE-REVIEW", … }  (16-line full-field instance)
```
**Why debt.** The Tracked State Structure example spans 238 lines (46% of the file), expanding all 9 stages — classic pre-Opus-4.x "one full instance per stage for pattern-matching." Stage "2" is a shape-subset of stage "1"; "3p" is shape-identical to "3"; both carry zero new information. Every other entry encodes a unique shape (verdict/retry, decision, items, skipped, in_progress, pending) — spec, KEEP.
**Proposed change.** Compress the two objects to one-line ellipsis form (~28 lines). **Side-observation (out of scope, not auto-fixed):** only stage "1" carries `dialogue_log_ref`, contradicting L28's "every stage transition" — needs its own decision.
**Iron-rule check.** Passed — ownership/ACL, append-only, monotonic, cannot-skip untouched; every unique field/shape still exemplified once; no script parses this example.
**Lint-mirror.** None (Bucket D no-Phase-Boundary rule unaffected; write-guard manifest is path-level).

**Decision** — [ ] accept  [ ] reject  [ ] defer (annotate: _________________)

---

### [B2-F03] `deep-research/agents/report_compiler_agent.md:142-147` — Cat 4 (basic citation-format few-shot) · P2 · confidence medium

**Excerpt**
```
- **Narrative**: Author (Year) found that…
- **Parenthetical**: Evidence suggests X (Author, Year).
- **Direct quote**: "exact words" (Author, Year, p. X).
```
**Why debt.** Isomorphic to 2026-07 F-005 (draft_writer Smith/Chen/Kim, codex-confirmed Cat 4): narrative-vs-parenthetical is textbook form Fable 5 produces from instruction alone. Smaller (5 lines), and three rows carry non-obvious rules (page number, alphabetical ordering, as-cited-in).
**Proposed change.** Trim — delete Narrative + Parenthetical rows; keep Direct quote / Multiple sources / Secondary. **Mirror `agents/report_compiler_agent.md` must be byte-resynced in the same commit.** Defer is fully defensible given the small size + mirror cost.
**Iron-rule check.** Passed — format style teaching, not a citation existence/faithfulness contract; Two-Layer/Three-Layer/R-L3-1/R-CIM untouched.
**Lint-mirror.** `check_agents_mirror_sync.py` (byte-equality — sync both copies). Prose itself: 0 hits.

**Decision** — [ ] accept  [ ] reject  [ ] defer (annotate: _________________)

---

### [B3-F04] `academic-paper/agents/revision_coach_agent.md:121-137` — Cat 5 (obsolete keyword-matching recipe) · P2 · confidence medium-low — **weakest finding of this pass**

**Excerpt**
```
| Section | Keywords in Comment |
| Introduction | "introduction", "motivation", "background", "opening" |
| Results | "results", "findings", "table", "figure", "data", "statistics" |
```
**Why debt.** The keyword column is a naive-matching recipe for a model that couldn't do semantic mapping; Fable 5 maps semantically, and keywords actively mislead (a Discussion-context comment mentioning "table" keys to Results). The real spec — 9 closed section values + General fallback + "use actual headings when draft provided" — survives.
**Proposed change.** Rewrite-positive: replace the table with one sentence enumerating the closed section list + General fallback + actual-headings rule.
**Iron-rule check.** Passed — closed value domain (downstream Roadmap column contract) fully preserved; failure is non-silent (Quality Gate 3 requires draft-checked mapping + user-confirmed parsing).
**Lint-mirror.** None.

**Decision** — [ ] accept  [ ] reject  [ ] defer (annotate: _________________)  ← reject is defensible (per the 2026-07 F-003 "lowest-confidence" precedent)

---

### [B4-F03] `academic-paper-reviewer/agents/field_analyst_agent.md:112-130` — Cat 4 (few-shot redundancy) · P2 · confidence low — *added by codex challenge; auditor dissent recorded*

**Excerpt**
```
### Dynamic Configuration Examples   (2 worked reviewer-panel configurations:
Higher-education QA domain; Taiwan private-university domain)
```
**Why this is (disputed) debt.** Codex: the normative reviewer-card contract is already fully defined (L70-85), output structure at L163-172, quality gates at L177-184; the two configurations are happy-path few-shot, and actual edge cases are separately encoded at L188-211. **Auditor dissent (primary pass judged KEEP):** 2 examples sit below the Cat 4 recognise-threshold (3+), and the two examples anchor *different domains* while calibrating how concrete a reviewer identity must be — closer to the spec-anchoring counter-example than to redundancy. Both readings are defensible; recorded as lowest-confidence P2 for the user to break the tie (mirrors the 2026-07 F-004 dissent-recording pattern).
**Proposed change (if accepted).** Trim to 1 example (keep the domain closer to real usage) or delete both, keeping the contract + gates + edge cases untouched.
**Iron-rule check.** Passed in codex's reading (no lint pins the example rows; not a Phase Boundary; field_analyst is Bucket C/D exempt). Auditor holds the counter-example reading.
**Lint-mirror.** None (verified — no script parses these rows).

**Decision** — [ ] accept  [ ] reject  [ ] defer (annotate: _________________)  ← codex recommends trim; auditor recommends keep — user breaks tie

---

## Kept as debt (iron rule filtered these OUT — recorded so the next audit doesn't re-surface them)

Condensed; each batch verified the full kept inventory. Highlights new to this pass (prior-audit kept items re-confirmed, not restated):

- **F-007 closure inventory:** all negative-framing sites in `pipeline_orchestrator` (31 rule sites: gate/fail-closed family incl. lint-pinned L680-681 "can NEVER be skipped"; reset-boundary lock contracts; advisory-never-blocks; consent/privacy; negative+positive twin pairs), `integrity_verification` (21 sites: incident-grounded anti-hallucination contracts — the Lin-et-al. mashup case study is documented in-file; fail-closed precedence; consent gates), and deep-research `socratic_mentor` (44/44: anti-sycophancy family incl. incident-born premature-convergence rules; Kong #257/#393 L2 verb-test boundaries; Reading/Adjacent Probe blocks — both **lint-pinned** by `test_reading_probe_lint.py` / `test_adjacent_framing_probe_lint.py`; SCR invisibility; INSIGHT definitional exclusions; Health Indicator). **KEEP, reclassified as contract.**
- `claim_ref_alignment_audit_agent` — entire file clean (v3.8-era, schema/lint-bound throughout: JUDGE-PROMPT-CANONICAL is lint-hashed; 38 invariants pinned). Judge default `gpt-5.5-xhigh` verified current.
- `intake_agent` — clean; the most lint-anchored file in the batch (3 lints parse its prose: #392/#439/domain-evidence). Its "NEVER fill a field from memory of the journal" family = laundering-guard provenance contracts, not generic anti-hallucination.
- `argument_builder`, `monitoring`, `devils_advocate` (deep-research), `compliance_agent`, both new commands — clean; kept inventories in batch records. `compliance_agent:113/118` F-008 annotation confirmed intact (stays deferred per 2026-06-10). (`timeline_extraction` carries a B4-F01 instance; `field_analyst` carries the disputed B4-F03.)
- `argument_builder_agent.md:36-49, 63-69` (sub-argument tree + counter-argument table) — **challenged by codex, challenge REJECTED**: the counter-argument table's 3 rows each demonstrate a *distinct* rebuttal strategy (acknowledge+limit / safeguards / concede-short-term) = the Cat 4 "examples as spec" counter-example verbatim; the tree + CER table are single canonical examples, already at the rubric's 0-1 target density. KEEP stands.
- `visualization_agent` Steps 6.5/6.6, palette/rcParams config constants, Chart Type Decision Logic (house policy), Edge Cases tables — KEEP.
- academic-paper `socratic_mentor` Wording-Pattern Advisory (Kong #257) — KEEP + **lint-pinned** (`test_check_rq_framing_patterns.py:66-78` asserts heading, marker, WP01-20 IDs, and literal sentences). Any same-file edit must keep clear of L27-64.
- Cross-file `Output Discipline` duplication — still the separately-tracked refactor+sync-lint backlog item (2026-07 classification unchanged).

## Coverage

| Batch | Files | Lines read | Findings | Clean files |
|---|---|---:|---:|---|
| B1 academic-pipeline | 5 | 2,737 (all end-to-end) | 3 | integrity_verification, claim_ref_alignment_audit, collaboration_depth |
| B2 deep-research | 5 | 1,572 | 3 | monitoring, devils_advocate, timeline_extraction |
| B3 academic-paper | 5 | 1,935 | 4 | intake, argument_builder |
| B4 residual + re-checks | 4 (+ guard spec, hooks, lints, 23-file roster greps) | ~530 + evidence reads | 2 | field_analyst, compliance_agent, both commands |

Cat 1 (model IDs) and Cat 3 (sampling overrides) grep-confirmed **zero** across all 17 agent bodies (the only config model ID — the external judge default — verified current; the GPT-3.5/4/4o figures in integrity_verification are cited-literature statistics, i.e., records). Every proposed edit string was grepped against `scripts/` + `.github/workflows/`; per-finding lint-mirror verdicts above.

### Cross-model challenge (codex, 2026-07-04)

Independent codex pass (gpt-5.5, high reasoning, read-only; ~1.10M tokens) attacked the audit in three directions. Verdicts and first-party adjudication:

**Direction 1 — false-positive retirements.** 12/12 excerpts verified real against file content; 11 findings ACCEPT as written, 1 AMEND: **B4-F02 was incomplete** — the stale SETUP surface is six lines per language (also `:3,145,172`: "Claude Opus 4.8" + GPT-5.4 Pro pricing), not just the two export lines. Accepted; finding amended. Codex independently re-verified the lint-safety claims (Phase Boundary marker regex, mirror byte-equality, no pins on the target strings).

**Direction 2 — missed debt.** Both headline conclusions **survive**:
- (a) F-007 closure confirmed — codex found zero safely-reframeable negatives in the three high-density files ("representative hits are hard boundaries").
- (b) Phase Boundary all-KEEP confirmed with a precision correction (accepted into B4-F01): the accurate split is *hook-registered vs hook-absent environments*, not "plugin vs symlink" — the guard resolves symlink roots too when invoked, and `run_guard.sh` passes through on guard failure, so the prose fence remains the documented degradation layer. Zero clause trims stands.
- Two new candidates: `field_analyst:112-130` examples (**accepted as B4-F03**, auditor dissent recorded) and `argument_builder:36-49/63-69` examples (**rejected** — the counter-argument table encodes distinct strategies = Cat 4 "examples as spec" counter-example; tree/CER already at 0-1 target density; rejection rationale in Kept-as-debt).
- Classic targets re-confirmed empty: no hardcoded model IDs, no sampling overrides, no retirable retry/repair loops in the 19 files.

**Direction 3 — priority.** Codex argued B2-F01 and B3-F02 are P1, not P2: the stale 15-round copies actively terminate/misroute *normal-length* sessions (typical run = 20-30 rounds), i.e., wrong behavior today, not weight. **Accepted — both upgraded to P1**, auditor concurs. (Distinct from the 2026-07 F-004 dissent, where the P1 claim lacked evidence of active harm; here the harm is arithmetic: 15 < 20-30.)

**Net challenge value:** +1 finding (B4-F03, disputed), +1 scope amendment (B4-F02), +1 wording correction (B4-F01), +2 priority upgrades (B2-F01, B3-F02 → P1), +1 rejected candidate (recorded). No fabricated findings on either side. Two-track value confirmed again: the single-track result ("12 findings, all P2") understated both scope and severity.

## Apply log (2026-07-04 apply turn; user decisions: B3-F04 rejected, B4-F03 kept, all others accepted)

| Finding | Action | Notes | Verified |
|---------|--------|-------|----------|
| B4-F01 | accepted → applied | enforcement sentence rewritten at 23 agents + 4 SKILL.md (hook-registered vs hook-absent wording per challenge correction); 2 mirrors byte-resynced; body tightened 39→35 words in the /simplify pass (semantics preserved); defrift lint (canonical-string pin) tracked as #491 | mirror lint green; zero residual "deferred to v3.10 active conductor" outside records |
| B4-F02 | accepted → applied (amended scope) | all six lines per language fixed (3, 145, 151, 155, 172); cost line provenance-labelled per 2026-06-10 F-002 pattern | — |
| B2-F01 | accepted → applied (**P1**) | stale 10/15-round bullets deleted; compilation trigger now references Auto-End Conditions | — |
| B2-F02 | accepted → applied | Auto-End Conditions (Precise) is now the single 6-condition authority; Auto-End Trigger section removed; stagnation constants single-sourced in Convergence Rules | — |
| B3-F02 | accepted → applied (**P1**; threshold = 30 per user) | Auto-End Rules table = single authority (6 rows incl. 5-round summarize-first + user-stop); conflicting Non-Convergence Handling bullets removed; Kong #257 block untouched | — |
| B3-F01 | accepted → applied | 4 template tables (12 rows) → 1 canonical example per type; taxonomy + Purpose lines + distribution table untouched | — |
| B3-F03 | accepted → applied | Steps 2-6 collapsed to pointer lines; Steps 1, 6.5, 6.6, 7 byte-untouched | — |
| B1-F02 | accepted → applied | duplicate step-5 dispatch sub-list → pointer to Checkpoint Confirmation Semantics; `view progress` row added to the table; duplicate "5." numbering fixed | — |
| B1-F01 | accepted → applied | happy-path Resume Acknowledged example deleted; pending_decision example kept | — |
| B1-F03 | accepted → applied | stages "2" and "3p" compressed to one-line ellipsis form; side-observation (`dialogue_log_ref` example-vs-rule) NOT touched — carried forward | — |
| B2-F03 | accepted → applied | Narrative + Parenthetical rows deleted; 3 non-obvious rows kept; `agents/report_compiler_agent.md` mirror byte-resynced | mirror lint green |
| B3-F04 | **rejected by user** | keyword mapping table stays; recorded — do not resurface next audit without new evidence | — |
| B4-F03 | **kept by user** (tie broken: auditor keep > codex trim) | Dynamic Configuration Examples stay; recorded as examined-and-kept — do not resurface next audit without new evidence | — |

## Next audit

- Suggested: next default-model upgrade, or next minor release.
- With this pass, **every agent prompt file in the repo has now had a deep per-file pass** (22 Bucket A in 2026-07 + these 17). Remaining un-deep-scanned surface: `shared/references/*.md`, `shared/templates/*.md`, `*/references/*.md` protocol docs (the 2026-06-10 pass covered them at grep level only).
- Carry forward: the F-008 annotation (unchanged); the Output Discipline shared-include backlog item; the B1-F03 side-observation (`dialogue_log_ref` example-vs-rule contradiction in state_tracker) if not resolved during apply; **#491** (canonical-string defrift lint for the enforcement sentence + SETUP model-token parity — the /simplify altitude finding).
- 2026-06-10 F-007 is closed by this pass (verified no-rewrite-needed); do not re-surface.
