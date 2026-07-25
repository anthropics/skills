# Model tiering: judgment/execution split (#517)

**Issue:** #517 — one tiering mechanism, two explicit directions, default untouched
**Date:** 2026-07-12
**Files touched:** `shared/model_tiering.md` (new canonical), `scripts/model_tiering_manifest.json` (new), `scripts/check_model_tiering.py` + `scripts/test_check_model_tiering.py` (new), the four `SKILL.md` files (compact dispatch block), `docs/SETUP.md` + `docs/SETUP.zh-TW.md` (env table), `docs/PERFORMANCE.md` + `docs/PERFORMANCE.zh-TW.md` (routing-layer sentence reconciled), `.github/workflows/spec-consistency.yml`, `scripts/_ci_pytest_manifest.toml`, `CHANGELOG.md`
**Status:** design frozen per issue #517 (2026-07-11); classification counts corrected in this spec

## Motivation (from the issue, unchanged)

Lance Martin (Anthropic), "Cost effective harnesses with Fable" (2026-07-10): many tasks have intelligence asymmetry across their tokens. Measured: an advisor-checkpoint configuration reached ~90% of Fable-solo quality at ~34% of token cost; delegation pays only when workers absorb enough tokens to offset the fixed per-handoff coordination cost. ARS maps onto this cleanly: light slash commands are already `sonnet`-pinned, but all pipeline agents are `model: inherit` — a Fable session burns Fable tokens on mechanical formatting work, and an Opus session gets no frontier judgment at the gates.

## Design (frozen 2026-07-11, restated)

**One mechanism, two directions, default untouched:**

1. **Default (no env var):** `model: inherit` everywhere — the session model runs everything. Byte-equivalent to pre-#517 behavior; same opt-in philosophy as `terminal_policies`.
2. **`ARS_MODEL_TIERING=quality-boost`** (for sessions running BELOW the frontier tier, e.g. Opus): judgment-type agents jump to the frontier tier (however many tiers away) at the checkpoint surfaces — the Stage 2.5/4.5 integrity gates (`integrity_verification`, `compliance_agent`), the opt-in Stage 4→5 claim–ref alignment audit (`claim_ref_alignment_audit` dispatches there, not at 2.5/4.5 — round-2 codex correction), and the final review (Stage 3 full panel; Stage 3' re-review's narrow team, i.e. `eic` + `editorial_synthesizer` among judgment-type roles). Quality strictly rises vs session-solo; the extra cost is concentrated where the article shows it matters (mid-task re-ranking, not upfront planning). In a session already at the frontier tier, quality-boost is a no-op (there is nothing to upgrade to) — announce the no-op once, never downgrade anything. Tier-to-model resolution happens at dispatch time from the runtime's own model information (alias or current-generation id, existing only in the ephemeral call — round-2 codex addition; see the canonical doc's "Resolving a tier at dispatch time").
3. **`ARS_MODEL_TIERING=economy`** (for frontier-tier sessions, e.g. Fable): execution-type agents downgrade exactly ONE tier — **floor Opus, never Sonnet** (frozen: academic-prose quality tolerance is untested; the article's 90%/34% numbers came from ML tuning, not scholarly writing). Judgment-type agents stay on the session model. In a session at or below Opus, economy is a no-op (the floor is already reached) — announce once, never go lower.

**Relative tiers, never hard-pinned ids (v3.7.0 lesson).** The ladder is expressed as *relative positions* — "session model", "frontier tier of the session's model family", "one tier below the session model", "the Opus-class floor" — never as concrete model ids. A hard-pinned floor becomes a downgrade ceiling on the next model generation; the v3.7.0 `opus` floor retired in the Fable 5 harness pass is the precedent.

**Any unknown/other `ARS_MODEL_TIERING` value = ignored with a one-line warning, behave as absent** (fail-open to the safe default: session model everywhere; misconfiguration must never silently change models).

## Agent classification (frozen membership; counts corrected)

The issue header said 25 judgment + 12 execution; the frozen lists themselves enumerate **26 judgment + 13 execution = 39**, which matches the 39 `*_agent.md` files on disk exactly. Membership is unchanged from the issue — only the header arithmetic is corrected here.

**Judgment-type (26)** — session model by default; quality-boost upgrade candidates at the gates:

- deep-research (10): `socratic_mentor`, `research_question`, `research_architect`, `synthesis`, `devils_advocate`, `editor_in_chief`, `ethics_review`, `risk_of_bias`, `meta_analysis`, `source_verification`
- academic-paper (6): `socratic_mentor`, `argument_builder`, `structure_architect`, `peer_reviewer`, `revision_coach`, `literature_strategist`
- academic-paper-reviewer (6): `eic`, `methodology_reviewer`, `domain_reviewer`, `perspective_reviewer`, `devils_advocate_reviewer`, `editorial_synthesizer` (mechanical by v3.6.2 design, but emits the final decision letter — kept judgment-type conservatively until data says otherwise)
- academic-pipeline (3): `pipeline_orchestrator`, `claim_ref_alignment_audit`, `integrity_verification`
- shared (1): `compliance_agent` (holds tier-based block authority)

**Execution-type (13)** — economy-direction downgrade candidates (one tier, floor Opus):

- deep-research (4): `bibliography` (citation existence already handled by the deterministic gate; **the sha256 F2 lock on this file is untouched — tiering never edits agent files**), `timeline_extraction`, `report_compiler`, `monitoring`
- academic-paper (6): `intake`, `draft_writer` (**highest-token, highest-savings, highest-risk downgrade point — flagged in the canonical doc as the suite's most quality-sensitive downgrade**), `abstract_bilingual`, `citation_compliance`, `visualization`, `formatter` (STAMP-ONLY by design)
- academic-paper-reviewer (1): `field_analyst`
- academic-pipeline (2): `collaboration_depth` (advisory-only, never blocks), `state_tracker`

## Implementation shape

**Prose + manifest + lint — no agent-file edits.** Agent frontmatter stays `model: inherit`; the tiering decision is made by the DISPATCHING layer (the session orchestrating a skill), following the canonical doc. A different tier is physically selectable only where a role runs as a separate subagent, and many ARS roles execute inline today (`docs/PERFORMANCE.md` § v3.7.0 plugin agents) — so the mechanism is: flag unset → nothing changes (dispatch shapes included, byte-equivalent); a direction applies to a role → the session dispatches that role as a subagent pinned to the target tier, inline roles included (dispatch-as-subagent IS the mechanism for them); subagent dispatch not possible in the runtime → the role runs inline on the session model with a one-line `[MODEL-TIERING: ... tiering not applicable]` announcement (fail-open, never a silently wrong-model claim). The PERFORMANCE.md "no separate model routing layer" sentence (en + zh-TW) is reconciled with a pointer. This keeps the mechanism byte-invisible when the env var is absent and avoids touching the F2-locked `bibliography_agent.md`. *(Round-1 codex review: the original "routes at Task-tool dispatch time" claim contradicted PERFORMANCE.md's inline-execution reality; the dispatch-as-subagent mechanism + inline fallback + PERFORMANCE reconciliation close it. The same round scoped the prompt-caching guidance to active directions — the byte-equivalent default promise now covers dispatch shapes — and unified the jump-to-frontier and warn-once wording across all surfaces.)*

1. **`shared/model_tiering.md` (canonical).** Mechanism, the two directions with their no-op conditions, the full 39-agent classification table, the relative-tier rule, the unknown-value rule, and the prompt-caching guidance (route repeated same-stage calls — e.g. reviewer re-review loops — to the SAME worker so its cache accumulates; a fresh worker per call re-pays the context write and can erase the savings; article guidance item 4).
2. **`scripts/model_tiering_manifest.json`.** Machine-readable classification: one entry per agent file (repo-relative path + `tier` ∈ {`judgment`, `execution`}). Single source of truth for the lint.
3. **`scripts/check_model_tiering.py` (classification drift guard).** Fails CI when: (a) the set of `*_agent.md` files on disk ≠ the manifest's set — an agent added without a tier assignment fails — including a repo-wide sweep that rejects agent files under a NEW skill directory outside the fixed roster; (b) a manifest entry's tier is not a valid enum value or a path is duplicated; (c) the canonical doc's table does not carry EXACTLY the manifest's short-name set per (tier, skill) row — missing tokens, extra tokens, duplicate tokens, wrong per-row `(N)` counts, duplicate skill rows, and headline-count mismatches each fail. 15 mutation tests in `scripts/test_check_model_tiering.py`; wired into `spec-consistency.yml` and the local pytest manifest. *(Round-1 codex review: the first cut was subset-only and dir-hardcoded; the exact set comparison + stray sweep close both.)*
4. **Four `SKILL.md` dispatch blocks.** A compact `## Model Tiering (#517)` section (absence-is-default, the two direction rules, pointer to the canonical doc) so every skill's dispatching layer sees the rule without duplicating the table.
5. **SETUP env tables (en/zh-TW).** One `ARS_MODEL_TIERING` row each.

## Out of scope

- No schema change, no agent-file content change, no hook.
- No automatic measurement of the economy direction's quality cost (documented as quality-for-cost with the article's numbers cited; a future calibration issue can measure ARS-specific deltas).
- Per-agent overrides (`ARS_MODEL_TIERING_OVERRIDES=...`) — rejected for now: unrequested flexibility.
- The `draft_writer` downgrade remains available but flagged; if a future measurement shows academic-prose degradation, the fix is reclassification in ONE place (manifest + table).

## Verification

- New lint + tests green locally; full CI lint set + the local pytest manifest (61 entries including this PR's) green.
- Boundary: no personal/private identifiers (public repo).
- Dual-track review (codex xhigh + security review) to 0 P1/P2 before merge.
