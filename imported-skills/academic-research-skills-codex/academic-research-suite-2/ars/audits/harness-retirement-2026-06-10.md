# Harness Retirement Audit — `academic-research-skills`

| | |
|-|-|
| Repo path | `~/Projects/academic-research-skills` |
| Branch / commit | `main @ e48d2c2` (2026-06-09) |
| Date | 2026-06-10 |
| Target model | **Fable 5** (`claude-fable-5`), migrated from Opus 4.8 |
| Files scanned | 73 prompt files (`SKILL.md` ×4, `agents/*.md` ×40, `commands/*.md` ×14, `shared/*.md` ×11+, references, hooks, `.claude/CLAUDE.md`) |
| Auditor | `/harness-retirement` skill v0.1.0 |

## Executive summary

- **Total findings**: 9 (5 recommended accept, 3 defer, 1 cosmetic)
- **By category**:

  | Cat | Count | Priority |
  |-----|------:|----------|
  | 1 — Hardcoded model IDs | 4 (F-001, F-002, F-003, F-009) | high (mechanical) |
  | 2 — Anti-hallucination patches | 1 (F-008) | low — almost all candidates passed the iron rule (contract-bound, not generic) |
  | 3 — Model/sampling overrides | 1 (F-004) | **high — the single biggest Fable 5 win** |
  | 4 — Few-shot redundancy | 0 | — (no file has 3+ examples; already lean) |
  | 5 — Defensive scaffolding | 0 | — (all retry logic is HTTP-429 backoff protecting external API contracts) |
  | 6 — Negative framing | 1 category-level (F-007) | medium, next minor release |
  | — — Model-premise re-baseline | 2 (F-005, F-006) | medium (measurement, not prompt edits) |

- **Suggested batch order**: F-004 → F-001/F-002 → F-003 (verify OpenAI lineup first) → F-005 → F-006 (open issue) → F-007 (next minor) → F-008/F-009 (opportunistic)
- **Overall verdict**: the repo is in unusually good harness shape. PR #346/#347 already established the "inherited session model, don't assert an id string" pattern; anti-hallucination text is contract-bound (R-CIM-D / EP-INV-3 / MATERIAL GAP protocol) rather than generic patching; few-shot and defensive-scaffolding debt is zero. The remaining debt is concentrated in **display-name drift** and **the `model: opus` floor that Fable 5 turned into a ceiling**.

⚠️ **Before applying ANY finding**: run the full lint suite (`python3 scripts/run_ci_pytest_manifest.py`). Several lints assert literal prose strings (e.g. `check_cross_model_verification_sync.py`, `check_version_consistency.py`). A prose edit that forgets its lint mirror will fail CI — and worse, a lint that silently stops matching is a fake-green.

---

## Findings

### [F-001] `shared/cross_model_verification.md:28,33` — Category 1 (hardcoded model ID)

**Excerpt**
```
| Claude Opus 4.8 | _(inherited Claude Code session model)_ | Anthropic | Primary model (default for all ARS skills) |
...
**Recommended cross-verification pair:** Claude Opus 4.8 (primary) + GPT-5.4 Pro or Gemini 3.1 Pro (verifier).
```

**Why this is debt.** The API-ID column already says *inherited session model* (the #346/#347 fix), but the display name still pins a generation. It was hand-bumped 4.7→4.8 in #347 and is now stale again under Fable 5 — proof that the display name is on a manual treadmill.

**Proposed change.** Make the row generation-agnostic so it never needs a bump again:
```
| Claude (session model) | _(inherited Claude Code session model — e.g., Fable 5)_ | Anthropic | Primary model (default for all ARS skills) |
...
**Recommended cross-verification pair:** the inherited Claude session model (primary) + GPT-5.x Pro or Gemini 3.x Pro (verifier).
```
Check `check_cross_model_verification_sync.py` for literal-string asserts before editing.

**Decision** — [ ] accept  [ ] reject  [ ] defer

---

### [F-002] `scripts/announce-ars-loaded.sh:84` — Category 1 (hardcoded model ID, injected every session)

**Excerpt**
```
Token budget reference: docs/PERFORMANCE.md (a single full pipeline run ≈ $4–6 on Opus 4.7)."
```

**Why this is debt.** This is the SessionStart hook — the line lands in **every** ARS session's context. "Opus 4.7" is two generations stale, and the $4–6 estimate was measured on that model. A user on Fable 5 reads a wrong model name and a wrong cost anchor at session start, every time.

**Proposed change.** `≈ $4–6 per full pipeline run (order-of-magnitude; measured on Opus 4.7 — see docs/PERFORMANCE.md)` — or drop the model name entirely and let PERFORMANCE.md own the measurement provenance. Sync `docs/PERFORMANCE.md` + `.zh-TW.md` in the same PR.

**Decision** — [ ] accept  [ ] reject  [ ] defer

---

### [F-003] cross-verifier lineup drift: `gpt-5.4` vs `gpt-5.5` — Category 1

**Locations**
- `shared/cross_model_verification.md` (entire file: supported-models table, env examples, the `gpt-5.4*)` case glob at :276)
- `academic-pipeline/agents/claim_ref_alignment_audit_agent.md:66` — judge default `gpt-5.5-xhigh`
- `shared/templates/codex_audit_multifile_template.md:263` — `gpt-5.5 + xhigh`
- `.claude/CLAUDE.md:202` — "GPT-5.4 Pro"

**Why this is debt.** Internal inconsistency: the citation judge defaults to **gpt-5.5**-xhigh while the cross-model verification doc teaches **gpt-5.4** everywhere — and its `gpt-5.4*)` shell glob will *not* match a `gpt-5.5` value, so a user following the judge's default into `ARS_CROSS_MODEL` hits the unsupported-model warning. Local codex CLI already defaults to gpt-5.5.

**Proposed change.** Unify on the current OpenAI lineup (verify before editing: does the Responses API `web_search` tool support the 5.5 family?). Update table, env examples, case glob (`gpt-5.4*|gpt-5.5*)` or regenerate), and `.claude/CLAUDE.md:202`.

**Iron-rule check.** Not a blind bump — the web-search-grounding path (#346) is load-bearing. Confirm tool support on the new id first.

**Decision** — [ ] accept  [ ] reject  [ ] defer

---

### [F-004] `commands/ars-full.md`, `ars-reviewer.md`, `ars-revision-coach.md` — Category 3 (model override; floor became ceiling)

**Excerpt** (frontmatter, all three files)
```yaml
model: opus
```

**Why this is debt.** v3.7.0 pinned the heavy modes to `opus` as a *floor*: "never run full/reviewer/revision-coach on something weaker than the session might be." Under Fable 5 the same pin is a **ceiling**: a Fable 5 session invoking `/ars-full` gets silently *downgraded* to Opus 4.8 for the most quality-critical paths in the suite. The three plugin agents already use `model: inherit` — the commands never got the same treatment because at v3.7.0 "opus" and "best available" were the same thing. That equivalence is what expired.

**Proposed change.** Two options, pick one after verifying command-frontmatter semantics:
1. **Delete the `model:` line** in the three opus-pinned commands → command inherits the session model (safe, no syntax risk).
2. `model: inherit` if the command frontmatter accepts it (agents do; verify for commands).

Leave the 11 `model: sonnet` light-mode commands alone — that's cost routing (a product decision), not a capability scaffold, and sonnet remains the right tier for abstract/outline/format-convert.

**Iron-rule check.** The original opus pin is documented (v3.7.0 CHANGELOG) but its premise — "opus = strongest available" — is what changed. No measurement pins the heavy modes to Opus 4.8 specifically.

**Decision** — [ ] accept  [ ] reject  [ ] defer

---

### [F-005] `tests/fixtures/issue_133_routing/README.md:21` + smoke suite — measurement gap (not a prompt edit)

**Excerpt**
```
- **100% pass on Opus 4.7** (primary model — most ARS users)
```

**Why this matters.** Tests are out of edit-scope for this skill, but the acceptance *definition* ("primary model — most ARS users") has drifted two generations, and the 8 routing smoke tests have never been run on Fable 5. The README itself warns: "A test that passes on Opus 4.7 today can regress on Opus 4.8 tomorrow."

**Proposed action.** (a) Re-run the issue-133 routing smoke suite on a Fable 5 session; (b) reword the threshold to "100% on the current primary model (tracked in cross_model_verification.md)" so the definition stops drifting.

**Decision** — [ ] accept  [ ] reject  [ ] defer

---

### [F-006] Opus 4.8 system-card premises behind #272 / #273 / #274 — re-baseline, keep the rules

**Locations.** The shipped guidance (`shared/ground_truth_isolation_pattern.md` §2A, editorial-synthesizer concise-output discipline, same-family calibration note) — none of it hardcodes "4.8" in prompt text (good design; the premise lives in issues/CHANGELOG).

**Why this matters.** All three rules were written against **Opus 4.8 system-card findings** (indirect-prompt-injection regression §4.1.4 over-caveat / multi-turn concession, rubric-aware judging §6.3.7). Fable 5's behavioral profile is different. The rules themselves are keep-worthy regardless (security depth, concision, epistemic honesty are model-agnostic virtues), but the **priority arguments** built on 4.8 regressions need re-baselining — in particular #272's runtime-enforcement urgency, which should be re-scored against the Fable 5 system card when available.

**Proposed action.** Open a small tracking issue: "Re-baseline model-behavior premises (#272/#273/#274) against the Fable 5 system card." No prompt edits.

**Decision** — [ ] accept  [ ] reject  [ ] defer

---

### [F-007] Negative-framing density — Category 6 (category-level, next minor release)

**Top files** (count of `don't / do not / never / avoid / must not`):
```
41 academic-pipeline/agents/pipeline_orchestrator_agent.md
33 deep-research/agents/socratic_mentor_agent.md
28 academic-pipeline/agents/integrity_verification_agent.md
26 academic-paper/agents/literature_strategist_agent.md
26 academic-paper-reviewer/agents/editorial_synthesizer_agent.md
```

**Why this is (partial) debt.** Most hits are hard gate/contract boundaries ("do not abort Phase 1, do not attempt schema repair") where the negative form is correct per the iron rule. But at 41 negatives in one agent, a fraction will be reframeable as shorter positive directives, which current models follow more reliably.

**Proposed action.** Not a bulk rewrite. At the next minor release, run a positive-reframe pass over the top 3 files only, one small PR each, with the full lint suite green per file (several lints pattern-match exact prose). Keep every negative that is a hard boundary.

**Decision** — [ ] accept  [ ] reject  [ ] defer

---

### [F-008] `shared/compliance_checkpoint_protocol.md:74` + `shared/agents/compliance_agent.md:113` — Category 2 (bare anti-hallucination tail)

**Excerpt**
```
... Apply [Anti-Leakage Protocol](...) — do not hallucinate.
... mark `[MATERIAL GAP]`, item auto-FAILs, tier dictates block/warn. Never hallucinate.
```

**Why this is (marginal) debt.** Both sentences sit at the end of a fully-specified MATERIAL GAP protocol that already defines the positive behavior (mark the gap, auto-FAIL, tier decides). The bare "never hallucinate" tail adds no instruction the protocol doesn't.

**Iron-rule check.** Academic compliance is high-stakes and the failure is silent — the textbook keep case. **Recommend defer** (annotate as known debt) rather than delete; revisit only with calibration evidence that the tail is inert.

**Decision** — [ ] accept  [ ] reject  [x] defer (annotate: high-stakes domain, silent failure; delete only with measurement)

---

### [F-009] `academic-paper/references/disclosure_mode_protocol.md:114` — Category 1 (cosmetic)

**Excerpt**
```
Replace `[MODEL_VERSION]` with the actual model used in this run (e.g., `Opus 4.7`, `Sonnet 4.6`).
```

**Why this is (cosmetic) debt.** The file already implements the correct placeholder pattern — the *e.g.* list is just stale and may anchor users to copy old names. Refresh to `(e.g., Fable 5, Sonnet 4.6)` opportunistically when the file is next touched.

**Decision** — [ ] accept  [ ] reject  [ ] defer

---

## Kept as debt (iron rule filtered out — do not resurface next audit)

- `shared/cross_model_verification.md:196,235` — `temperature: 0.1` on GPT/Gemini verifier calls. **Kept**: documented rationale at :261 (deterministic factual task; variance reduction), and it parameterizes non-Claude models.
- `deep-research/references/{openalex,semantic_scholar,arxiv,crossref}_api_protocol.md` — HTTP-429 backoff/retry. **Kept**: protects external API contracts, not a model scaffold.
- R-CIM-D "do NOT invent ids or rename" (draft_writer :591, synthesis :354, report_compiler :341). **Kept**: schema contract (EP-INV-3), definitional not defensive.
- `visualization_agent.md:441`, `risk_of_bias_agent.md:33`, `pipeline_orchestrator_agent.md:555`, `collaboration_depth_agent.md:75`, `synthesis_agent.md:162`, `literature_corpus_consumers.md:107` — "do not invent X" with positive counterpart in the same clause. **Kept**: negative + positive reinforce each other (Cat 6 counter-example).
- `commands/*.md` `model: sonnet` ×11 — cost routing, product decision.
- `deep-research/agents/*` `model: inherit` ×3 — already the target pattern.
- `tests/fixtures/issue_133_routing/` Opus 4.7 references *inside test fixtures* — records/pins, out of scope (the README threshold definition is F-005, separate).

## Apply log (2026-06-10 apply turn)

| Finding | Action | Notes | Verified |
|---------|--------|-------|----------|
| F-001 | accepted → applied | primary row generation-agnostic; gpt-5.4* kept accepted | lint suite 43/43 green |
| F-002 | accepted → applied | announce + PERFORMANCE ×2 provenance-labelled | lint green |
| F-003 | accepted → applied | gpt-5.5 ($5/$30) / gpt-5.5-pro ($30/$180) verified first-party (developers.openai.com, 2026-06-10); web_search-on-Responses confirmed; case glob `gpt-5.5*\|gpt-5.4*` | lint green |
| F-004 | accepted → applied | `model:` line deleted on 3 heavy commands; body "uses opus" sentences synced | grep: zero `model: opus` residual |
| F-005 | accepted → applied + run | threshold reworded; **Fable 5 smoke: 8/8 routing-class PASS** (01–08, incl. all 3 escape-hatch behaviors); 02/04 destination picks needed Routing-Rules/MODE_REGISTRY context (harness approximation, resolved on re-run with full rules) | subagent transcripts 2026-06-10 |
| F-006 | accepted → issue drafted | `audits/issues-to-file-2026-06-10.md` (gh issue create blocked by session permission; command ready) | — |
| F-007 | deferred | next minor; top-3 files sample-reframe, one PR each | — |
| F-008 | deferred (annotated) | in-file `harness-retirement` annotations added at both sites | lint green |
| F-009 | accepted → applied | e.g. list refreshed | — |

## Next audit

- Suggested: next minor release, or when the Fable 5 system card publishes (re-check F-006)
- Carry forward: F-008 annotation; re-verify `model: sonnet` cost routing still matches the lineup
