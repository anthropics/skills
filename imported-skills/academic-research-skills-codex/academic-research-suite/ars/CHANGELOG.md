# Changelog

All notable changes to this project will be documented in this file.

## [Unreleased]

## [3.16.0] - 2026-07-12 — Model tiering, cross-model gate hardening, WP advisory sharpening

### Added

- **Model tiering: judgment/execution split with two opt-in directions, default untouched (#517).** New `ARS_MODEL_TIERING` env switch and canonical `shared/model_tiering.md`, motivated by Lance Martin's "Cost effective harnesses with Fable" (2026-07-10; advisor-checkpoint configs measured ~90% of frontier-solo quality at ~34% of token cost, with delegation paying only when workers absorb enough tokens to offset per-handoff coordination cost). **Default (unset): byte-equivalent pre-#517 behavior** — every agent stays `model: inherit` (same opt-in philosophy as `terminal_policies`). **`economy`** (frontier-tier session): the 13 execution-type agents dispatch exactly one tier below the session model, **floor Opus-class, never Sonnet** (academic-prose tolerance is untested; the article's numbers came from ML tuning) — `draft_writer` explicitly flagged as the highest-savings / most quality-sensitive downgrade point. **`quality-boost`** (below-frontier session): the judgment-type agents dispatched at the Stage 2.5/4.5 integrity gates and the final-review surfaces step up to the frontier tier; nothing is ever downgraded. Both directions have explicit no-op conditions with a one-line announcement; unknown values warn once and behave as unset (fail-open to the safe default). Tiers are **relative positions, never hard-pinned model ids** (the v3.7.0 `opus` command floor retired in the Fable 5 harness pass is the cited precedent). Because many ARS roles execute inline today (no per-role model choice), the mechanism is dispatch-shaped: when a direction applies to a role, the session dispatches it as a subagent pinned to the target tier — inline roles included — and falls open to inline-on-session-model with a one-line announcement where subagent dispatch is impossible; `docs/PERFORMANCE.md`'s (en/zh-TW) "no separate model routing layer" sentence is reconciled with a pointer. The frozen 39-agent classification (26 judgment / 13 execution — the issue header's 25/12 arithmetic corrected, membership unchanged) lives twice on purpose: a machine-readable `scripts/model_tiering_manifest.json` and the canonical doc's table, pinned to each other AND to the `*_agent.md` files on disk by new `scripts/check_model_tiering.py` — set equality with a repo-wide stray sweep (a new skill dir can't smuggle unclassified agents), tier-enum + duplicate checks, and EXACT per-(tier, skill) token-set comparison against the doc table (missing/extra/duplicate tokens, per-row counts, duplicate rows all fail; 15 mutation tests; wired into spec-consistency.yml + the local pytest manifest). Prompt-caching guidance (when a direction is active, route repeated same-stage calls to the SAME worker so its cache accumulates) documented in the canonical doc and each of the four `SKILL.md` files' compact `## Model Tiering (#517, optional)` dispatch block — scoped so the unset default stays byte-equivalent, dispatch shapes included. No agent-file edits (the sha256-locked `bibliography_agent.md` untouched), no schema change, no hook. Spec: `docs/design/2026-07-12-517-model-tiering-spec.md`.

- **Cross-model gate hardening: risk-stratified sampling, blind disagreement checkpoints, id-status allowlist, promotion bakeoff (#518).** Four upgrades to `shared/cross_model_verification.md` and its consumers, from a 2026-07-11 cross-model consult (gpt-5.6-sol, xhigh). (1) The integrity-gate cross-model sample moves from uniform random 30% (min 5, max 15) to **risk stratification** across four mutually-exclusive tiers (highest-precedence tier wins, one verification per reference): HIGH-IMPACT references (headline conclusions, numerical claims, causal claims, methods-critical, disputed) verified 100% uncapped at both gates; a 10% RANDOM sample of the remainder at Stage 2.5 (round-up, min 3, max 10); at Stage 4.5, NEW-CHANGED references (behind claims new or changed since 2.5) verified 100% uncapped plus a 10% CONTROL sample of the unchanged remainder replacing RANDOM — verification budget concentrates where the paper's weight rests, and the results table gains a Tier column (`integrity_verification_agent` updated in lockstep). (2) The two irreversible checkpoints — research-design freeze (`research_architect_agent`) and final editorial decision (`editorial_synthesizer_agent`) — gain optional **blind disagreement checks**: the primary commits its own decision in the same structured form first (the architect in a new Design-Freeze Checkpoint Audit blueprint section; the synthesizer's is its emitted decision), the cross-model then produces an independent structured decision from the same inputs (never seeing the primary's decision — same anchoring-prevention rule as the integrity samples; the editorial input is the panel's `panel_size` N usable reviewer cards, never a hardcoded five), differing enum values trigger a targeted rebuttal addressing each cross-model driver against the evidence on file, and divergence escalates to the user — a review trigger, never a vote, never averaged; under a sprint contract the check runs strictly post-Step-3 against the mechanical protocol's `editorial_decision` and its drivers never enter the scoring matrix. (3) The **"6th reviewer — Planned" section is retired, not deferred**: the consult's counterproductive-conditions list (score averaging, role duplication, findings treated as confirmed defects, majority-vote false confidence, synthesizer context burn) matches ARS's documented anti-patterns one-for-one; the blind checkpoints are the replacement design, and the live mirrors (`.claude/CLAUDE.md`, `shared/raise_framework.md`, SETUP feature tables en/zh-TW) drop the "remains planned" claim. (4) The model-detection snippet separates "which provider endpoint" from "is this id known-good": new `CROSS_MODEL_ID_STATUS=validated|provisional|unlisted` announcement with an explicit warning for unlisted first-party-prefix ids (`gpt-made-up` no longer passes silently) — routing itself is byte-identical, an unlisted id still takes the grounded route and never falls through to the ungrounded compatible branch. Plus a **§ Promotion Bakeoff** operationalizing the `gpt-5.6-sol` provisional→validated criteria: a 30-reference paired same-day run (20 real / 10 fabricated; committed as a versioned, labeled, sha256-recorded fixture before any run counts; 3 repeats with ≥2/3 majority verdict, a 1–1–1 split scored conservatively against the model that produced it) against five non-inferiority thresholds (grounded-search completion, mismatch recall, false-disagreement rate, jq-guard shape stability — a hard requirement, p95 latency), entry-gated by `scripts/cross_model_smoke_test.sh`, results recorded under `audits/` either way — and a deliberate two-step outcome: a full pass makes the id `validated`, while the recommended default flips only with an additionally stated superiority or operational-benefit reason. Spec: `docs/design/2026-07-12-518-cross-model-gate-hardening-spec.md`. Related: #517 (model tiering) will reference the checkpoint surfaces added here.

- **GPT-5.6 Sol listed as provisional cross-model verifier + explicit reasoning-effort control (#515).** OpenAI's `gpt-5.6-sol` (released 2026-07-08) joins the canonical model table in `shared/cross_model_verification.md` as **provisional pending ARS validation** — endpoint support (Responses API + hosted `web_search`), the reasoning-effort enum (`none|low|medium|high|xhigh|max`, default `medium`), and pricing (same standard rates as GPT-5.5; premium is `reasoning: {mode: "pro"}` on the standard slug, NOT a `-pro` model id) were verified first-party against OpenAI's model page and GPT-5.6 guide, but ARS-specific behavior (grounded-search completion rate, citation-mismatch recall, false-disagreement rate, jq-guard response-shape stability, p95 latency) has no operating history, so **GPT-5.5 stays the recommended default**. The documented OpenAI Responses call pattern gains an explicit reasoning-effort control via new `ARS_CROSS_MODEL_REASONING_EFFORT` — set, it is passed as `reasoning.effort` so the run's effort is visible and reproducible; unset, the field is omitted entirely and each model's own provider default applies (forcing one value would silently change behavior for existing `gpt-5.5-pro`/legacy setups, a codex-review P2) — and both SETUP quick-setup blocks (en/zh-TW, parity-linted) mirror the new example lines. New `scripts/cross_model_smoke_test.sh` — a live, manual (not CI; needs `OPENAI_API_KEY`) promotion gate asserting HTTP 2xx, a completed `web_search_call`, a single verdict token, VERIFIED-carries-source, model echo, and effort echo — is the prerequisite for ever flipping the default to Sol. The canonical doc's Chat-Completions-web-search claim was re-verified against OpenAI's current web-search guide and deliberately left unchanged (a cross-model review suggested it was stale; first-party docs confirm it is still accurate).

- **WP advisory held-out miss-rate measurement + acceptance set, Part 2 (#501; direction from the PR #468 review thread, @brycewang-stanford).** New `evals/heldout/rq_framing_offlist/`: a 48-item held-out set (32 shells outside the WP01-WP20 surface forms and the four in-prompt examples — 23 family variants + 9 off-list — plus 16 domain-native hard negatives), generated cross-model (`gpt-5.6-sol`), shell items regex-filtered (four negatives intentionally carry listed surface substrings as hard-negative material), dual-annotated with documented drops, English-only per the #468 caveat. Scored against the runtime LLM judge (isolated `claude-sonnet-5` sub-agents, verbatim advisory section only, pre-#503 vs post-#503 variants, two post replicates): overall miss rate 0.34-0.38 (above the inherited FNR < 0.30 line), concentrated in decorated compound-title off-list shells (7/9 missed, stable across replicates; judges read generic topical nouns as the exemption's "specific mechanism"), family-variant generalization under the line post-#503 (0.17-0.22), false-fire 0/16 on both variants. Verdict: miss rate HIGH → per #501's decision rule the set is now the acceptance test for any future advisory change (protocol in the set's README; report at `audits/rq-advisory-heldout-measurement-2026-07-11.md`). Deliberately outside `evals/gold/` (LLM-judged; no `target.entrypoint`, labels not reducer-reproducible). Closes #501; the measured off-list gap is tracked as a follow-up design issue.

- **Introduction & Title Rhetoric reference (#500; gap surfaced by PR #485, @lorenzo392).** New `academic-paper/references/intro_title_rhetoric_guide.md`: CARS three-move Introduction guidance (territory / niche / occupation, with a licensed-gap rule, the universal-negative trap, purpose-sentence discipline, and a common-failures table) plus a title-crafting section (anatomy, four title types with claim-level cautions, checklist, weak→stronger worked examples, and a cross-check against the WP06/WP17/WP18 wording-pattern shells). Wired as a `draft_writer_agent` Step 1 setup checklist item; `academic-paper/SKILL.md` File Structure reference list updated (stale count 20 corrected to the actual 28). The declined PR #485 skill shape (new top-level skill) stays declined; this lands the two genuinely-uncovered content areas as a reference file per the maintainer response there.

- **Korean trigger keywords + routing boundary fixtures (#452 PR 1; proposal and Korean boundary phrases by [@devCharlotte](https://github.com/devCharlotte), who also authored the native-reviewed Korean README in #469).** All four `SKILL.md` files gain a `**한국어**` trigger-keyword line plus a conservative Korean subset in the frontmatter `description` — intent-specific compounds only (논문 심사 / 논문 수정 / 초록 작성 / 체계적 문헌고찰 / 연구부터 논문까지 …), deliberately avoiding the broad standalone terms the proposal flagged (연구, 논문, 작성, 검토). The key 수정-vs-심사 disambiguation lands as two new routing smoke-test fixtures (`tests/fixtures/issue_133_routing/09_korean_revision_not_review/`, `10_korean_review_not_revision/`) using the proposer's native-authored phrases; all six boundary cases from the issue pass a routing smoke test on the current primary model (6/6, recorded in the PR). No changes to agents, IRON RULEs, integrity protocols, schemas, modes, or output-language behavior. Closes #452 (the Korean README half shipped in #469/#471).

### Changed

- **WP advisory exemption sharpening — decorated title-form shells now caught (#505; direction from the #501 Part 2 measurement).** The exemption clause in both `socratic_mentor_agent.md` files (deep-research + academic-paper) is narrowed: it now requires a *named or operationalized* specific (an actual instrument/scale name, a named theory/model/dataset/policy instrument, a named site or population, a specified causal pathway — through what mediator/condition/process A relates to B, not merely that it does — or a stated tension between two identified explanations), declares ordinary domain-flavored topic-label pairs swappable, and adds a decorated-compound-title rule (an evocative pre-colon phrase plus a generic "X and Y (in Z)" subtitle gains no specificity from the decoration — the noun-swap test applies to the part after the colon alone). This closes the failure mechanism the #501 Part 2 baseline measured: judges reading generic topical noun pairs as the exemption's "specific mechanism", which rescued 7/9 off-list shells (six decorated titles plus one interrogative). Measured against the held-out acceptance set per its README protocol in two rounds (initial wording, then a cross-model-review-driven refinement — demographic descriptors excluded from "named population", single-topic subtitles covered — re-measured from scratch; 2 replicates each, same judge model): overall miss 0.375/0.344 → **0.094 in all four post-#505 runs**, off-list 0.778 → all 9 items fired in at least one final replicate (final rep2: 9/9), false-fire 0/16 preserved in every run (including the four hard negatives carrying listed surface substrings); no shell missed in both final replicates; on-list gold set unaffected (regex detector untouched, fnr=0/fpr=0). All #505 constraints held: WP table unextended, advisory stays non-blocking and surface-phrasing-only, sentinel contract (`test_check_rq_framing_patterns.py`) unchanged; the new in-prompt example strings were substring-checked against every held-out item (zero hits) so the set stays held out. Measurement JSON `evals/heldout/rq_framing_offlist/measurement-2026-07-11-505.json` + reasoning excerpts appended; report at `audits/rq-advisory-505-exemption-sharpening-2026-07-11.md`. Closes #505.

- **Reviewer calibration protocol notes LLM-as-judge leniency direction (#484 → PR #506, merged).** `academic-paper-reviewer/references/calibration_mode_protocol.md` gains a directional-prior subsection under "Failure cases this mode does NOT fix": when the simulated panel's output is read as a pass/fail signal, assume leniency relative to human expert review until your own calibration shows otherwise, anchored to FARS (Tang et al. 2026, arXiv:2606.31651 — automated reviewer mean 5.00 over 165 papers vs 3.23 paper-level mean from 282 human expert reviews over 140 papers; a descriptive ~1.8-point gap, and the automated score functioned only as a relative ranking). The direction is a working prior (heuristic extrapolation from one measured setup, default-until-measured); the magnitude is explicitly non-portable — never a correction factor or threshold change. Docs only; the panel remains advisory infrastructure behind human checkpoints. FARS added to References.

- **WP advisory generalization, Part 1 (#501; direction from the PR #468 review thread, @brycewang-stanford).** Both `socratic_mentor_agent.md` files (deep-research + academic-paper) now state that the WP01-WP20 table is illustrative, not exhaustive, and name the operative judgment: the noun-swap test (phrasing is shell-like when it survives swapping its nouns for any other field's nouns). Off-list shells that clearly survive the swap may fire the advisory at the same high-confidence bar; domain-native phrasing that names a mechanism, instrument, site, or tension does not survive it and must not trigger. Advisory stays non-blocking and surface-phrasing-only; sentinel contract unchanged (`test_check_rq_framing_patterns.py`). Part 2 (held-out miss-rate measurement) landed separately — see the Added entry above.

- **API-first retrieval refresh: OpenAlex API-key auth, budget-aware 429 handling, arXiv ToU-aligned backoff (#495; proposed by [@pikaqiu2333](https://github.com/pikaqiu2333)).** OpenAlex's current developer docs are API-key-first (freemium daily budget; the polite pool is no longer documented): `scripts/openalex_client.py` gains `OPENALEX_API_KEY` support (query-param auth; either credential selects the authenticated 10 req/s pacing tier, `OPENALEX_POLITE_EMAIL` stays as legacy compat), distinguishes daily-budget-exhausted 429s (`X-RateLimit-Remaining: 0` → raise `OpenAlexUnavailable` immediately — the budget refills at midnight UTC, so an in-process retry cannot succeed) from transient burst 429s (exponential backoff 2s → 4s → 8s per OpenAlex's documented guidance), and strips the query string from refusal-path error messages so the key never lands in logs (`scripts/crossref_client.py` gets the same redaction — its query string carries the polite-pool `mailto` email). `scripts/arxiv_client.py`'s 429 backoff moves from the shared 2s constant to the 3s ToU pacing floor (arXiv's Terms of Use ask for at most one request every three seconds — a sub-3s retry would itself violate the pacing the 429 enforces; verified verbatim against the ToU page). Both protocol docs (`deep-research/references/openalex_api_protocol.md`, `arxiv_api_protocol.md`) updated in lockstep, plus an explicit retrieval-order boundary in each: structured APIs are the primary channel, browser/WebFetch page inspection is a bounded first-party fallback whose output is data-not-instructions (`shared/ground_truth_isolation_pattern.md` §2A), and browser retrieval is never a rate-limit bypass (no parallel browsing, no bulk PDF harvesting, no multi-machine fan-out). 5 new client tests; the two 429-behavior tests updated to pin the new backoff shapes.

### Docs

- **Third-party directory: `THIRD_PARTY.md` + README pointer (#497 → #498).** Community-submitted third-party projects that wrap or host ARS get a low-bar directory listing (visible ARS attribution + faithful description required) that is explicitly separate from endorsement — entries are not reviewed, tested, or verified by the maintainer, and the page says so up front. ClawMama listed as the first entry per issue #497. The README install section gains a neutral, non-recommending pointer to the page; the main install flow still links only to maintainer-verified paths. A separate "Getting officially recognized" track is documented for projects that want actual review.

## [3.15.0] - 2026-07-04 — Release-gate hardening, prompt-debt retirement round 2, defrift locks

### Added

- **Phase Boundary enforcement-sentence defrift lock + SETUP cross-model parity lint + local-manifest gap closure (#491 → #492).** `scripts/check_v3_9_2_phase_boundary.py` gains invariant 4: every Bucket A block's enforcement paragraph must carry the canonical sentence verbatim (`CANONICAL_ENFORCEMENT`, version-matched v3.9.2/v3.9.4; per-file tails after the sentence stay free). Motivation: the pre-#294 copy of that sentence sat factually stale across 29 surfaces for a month while this very lint iterated those exact blocks pinning only the marker prefix — the drift class now fails CI, with 7 mutation tests including the literal stale sentence as the regression case. New `scripts/check_setup_cross_model_parity.py` (+9 tests, wired into spec-consistency.yml) pins the `docs/SETUP.md` / `docs/SETUP.zh-TW.md` `ARS_CROSS_MODEL` examples to each other and to the canonical model tables in `shared/cross_model_verification.md` — membership is scoped to "API ID" table columns after a codex-review P1 (legacy ids backticked in the accepted-for-existing-setups note must not count as recommended) and excludes glob prefix tokens per the re-review P2, failing closed when extraction finds nothing. The local pytest manifest gains `test_check_v3_9_4_temporal_verification.py` (58 → 60 entries): its CI-only coverage is what made #490 local-green/CI-red on the bibliography_agent sha256 F2 ownership pin. `tests/test_helpers.py` gains `load_module_from_path()`; the enforcement-sentence mechanism is cross-referenced with the `firm_rules.md` canonical-block framework in both directions (deliberately separate: factual status prose vs behavioral firm rules).

- **Release-doc alignment gaps closed in the version-consistency lint — three new invariants + a tag-time gate (#487).** A 2026-07-03 audit of `scripts/check_version_consistency.py` against the suite-level release-doc discipline found the #357/#345 extensions had already closed the docs-version-ceiling, zh-TW-parity, and package-metadata invariants, but four sub-items had no machine check. Now enforced: invariant 9 — the latest CHANGELOG entry's body must be ≥ 100 characters (a bare heading is not release notes; historical entries stay exempt); invariant 10 — `.claude/CLAUDE.md` "Last Updated" must lie within ±7 days of the latest CHANGELOG entry's date (the CHANGELOG date is the baseline, never "today", so re-running the lint later cannot flip the result); invariant 11 — the newest `## vX.Y… Key Additions` heading must match the suite version at the heading's own precision. New `--tag` mode plus a `tag-version-match.yml` workflow (`push: tags: v*`) require the pushed tag name to equal the suite version — the one comparison nothing performed at tag time — and re-run the full lint at the moment of tagging. A fifth candidate check ("every version cited in docs/ must exist in CHANGELOG") was evaluated and rejected: ARS's spec-version naming culture (e.g. the v3.6.6-design-shipped-as-v3.6.8 note) plus component versions make it structurally unenforceable (600+ legitimate references would false-flag). The latest-entry body ends at the next release heading via a fence-aware line scan, so a `## [...]` line inside a fenced code block in the release notes can't truncate the body (even one shaped exactly like a real entry); CHANGELOG / Last-Updated dates are right-bounded and shape-gated to strict `YYYY-MM-DD` then parsed fail-closed, so a prefix like `2026-04-222` isn't mis-read as `2026-04-22` and an impossible date like `2026-02-30` reports a lint error instead of crashing. 20 new mutation tests (33 → 53), including the tag-gate hard-fail when the suite version is unreadable (a garbage tag co-occurring with a broken `.claude/CLAUDE.md` must not slip through the one gate meant to catch it).

- **Command-invariants CI gate — announce list machine-checked against the actual command inventory (#486).** Vendors release-discipline-toolkit v0.3.0 under `tools/release-discipline/` and adds `.command-invariants.toml` + a `command-invariants.yml` workflow. The lint discovers `commands/*.md` (16 today) and asserts `scripts/announce-ars-loaded.sh` lists exactly that set — missing command, stale extra, and the hardcoded `Slash commands (N)` count all fail CI — plus a version-lockstep check pinning `.claude-plugin/plugin.json` to the newest CHANGELOG release entry. Motivated by the announce list drifting twice (PR #193: 10 listed vs 12 actual; this change: 14 vs 16); the validator was verified against the live drift before installation (caught exactly the two missing commands, zero false positives).

- **CHANGELOG-covers-merges pre-tag release gate (#483).** `scripts/check_changelog_covers_merges.py` machine-checks that every release-worthy commit merged since the previous release tag is documented in `CHANGELOG.md` above the previous release's section ([Unreleased] or a release-prep-promoted newer section — spec §0.2), with conventional-prefix exemptions (`chore`/`test`/`ci`/`build`, `docs(design)`/`docs(superpowers)`/`docs(release)`/`docs(i18n)`) and fail-closed behavior on missing tags/headings. New `changelog-covers-merges.yml` workflow gates every `release/**`-headed PR into main; the CONTRIBUTING manual step covers branchless tag flows. Would have blocked the 16-entry Unreleased backlog rolled up in 3.14.0. 47 tests, registered in the CI pytest manifest.

### Changed

- **Prompt-debt retirement round 2: the 17 never-deep-scanned agents (#489 → #490).** Continuation of the #476 track — the 2026-07 audit covered only the 22 Bucket A agents and explicitly deferred the rest. This pass deep-scanned the remaining 17 (all 5 academic-pipeline agents, 5 deep-research, 5 academic-paper, field_analyst, shared compliance_agent) plus 2 new commands and 3 carry-forward re-checks, via 4 parallel sub-agent batches + an independent codex cross-model challenge (12/12 excerpts verified; +1 finding, +1 scope amendment, +2 priority upgrades). 13 findings — 2 P1, 11 P2; the user rejected 2 (recorded so the next audit does not resurface them). The two P1s were live self-contradictions: both `socratic_mentor` agents carried stale pre-v3.0 "suggest quitting after 15 rounds" copies against a documented typical run of 20-30 rounds — auto-end machinery is now a single authority per file (threshold unified at 30), with stagnation/max-round constants single-sourced. The stale "prompt-level only / deterministic hook deferred to v3.10 #134" enforcement sentence (false since PR #294 shipped the write-scope guard) was rewritten at 23 agents + 4 SKILL.md + 2 mirrors, then tightened 39 → 35 words in the /simplify pass. Few-shot and duplicated-process scaffolds trimmed across 7 agents (question-template tables, citation-form examples, resume exemplars, triple-written dispatch rules incl. a missing `view progress` row restored to the authoritative table); SETUP model-lineup drift fixed in both languages. The 2026-06-10 F-007 deferred negative-framing item closes as **verified, no rewrite needed** — zero safely-reframeable negatives across the three top-density files, confirmed by both tracks. `bibliography_agent`'s F2 baseline hash updated per the lint's documented procedure. Audit report: `audits/harness-retirement-2026-07-04.md`. Net −181 deleted / −98 substantive prompt lines excluding the report.

### Fixed

- **SessionStart announce updated to the full 16-command set.** `/ars-3w` and `/ars-rebuttal-audit` were missing from both the resume short-form list and the startup long-form listing, and the stated count said 14 — commands shipped after the list was last hand-synced were silently invisible at session start. Both forms now list all 16 with the correct count (announce script `# version` bumped 1.0.0 → 1.1.0); the new command-invariants gate prevents recurrence.

- **DOI badge served from shields.io (#482).** Zenodo's badge endpoint rate-limits GitHub's camo image proxy (HTTP 429), intermittently rendering the README DOI badge as a broken image even though the DOI resolves fine. The badge image is now a static shields.io badge in all five READMEs; the link target stays the concept DOI (`10.5281/zenodo.20696614`), which always resolves to the latest version.

## [3.14.0] - 2026-07-02 — Claude Science importability, eval-comment rendering, prompt-debt retirement

### Added

- **Claude Science / GitHub-importer compatibility — explicit skill paths in the marketplace manifest (#480).** The plugin entry in `.claude-plugin/marketplace.json` now declares `"skills": ["./academic-paper", "./academic-paper-reviewer", "./academic-pipeline", "./deep-research"]`. The repo-root `skills/` directory holds symlinks, which GitHub-API consumers cannot traverse — Claude Science's "Import from GitHub" previously reported *"Not importable: no skills/ dirs with SKILL.md"* and found zero skills (same failure class as the #413 `agents/` materialization). Per the Claude Code plugins reference, for a marketplace entry whose `source` is the marketplace root the listed paths REPLACE the default `skills/` scan, so Claude Code installs keep loading the same four skills from their real paths — no content change, no double-loading. Verified end-to-end on Claude Science (4/4 skills detected at the merge commit). New README / SETUP.md guidance documents the import flow and its limits: imported skills carry the methodology (research / writing / review protocols); Claude Code-specific machinery (slash commands, hooks, subagent orchestration) does not transfer, and imports are point-in-time snapshots that require re-import after ARS updates.
- **Eval-harness PR comments render as a verdict + per-task table (#479).** The eval-harness workflow previously pasted the whole `eval_report.json` into every PR comment as one raw fenced block. New display-layer module `scripts/render_eval_comment.py` emits a one-line verdict (`✅ N/M measured tasks passed · K pending (not wired)`), a per-task markdown table (metric / value / threshold / result; pending tasks render `—` placeholders), and folds the full JSON into `<details>`. The row verdict mirrors the gate's failure signal (aggregate AND per-class, #328), with a test pinning agreement with `scripts._eval_threshold_gate` so the mirror drifts loudly in CI instead of rendering green on a blocked run; table cells escape pipes and all line boundaries so manifest-sourced strings cannot break or spoof rows (codex review finding, fixed in-PR). Evaluation logic is untouched: `run_evals`, the threshold gate, and the `[eval-regression-acknowledged]` ack contract are byte-identical. 13 unit tests, registered in the CI pytest manifest; the workflow-honesty test suite gains a pin so the comment cannot silently regress to a raw dump.

### Changed

- **Prompt-debt retirement: expired writing-harness scaffolds removed from four Bucket A agents (#476 → #478, net −111 lines).** The 2026-07 harness-retirement audit (#477, report under `audits/`) classified prompt scaffolds that encoded assumptions about what prior models could not do. The five P2 findings plus one hands-on finding were applied to `abstract_bilingual_agent`, `citation_compliance_agent`, `draft_writer_agent` (academic-paper) and `research_question_agent` (deep-research). Three-track verification: sub-agent audit + independent codex review (two fabricated back-references caught and fixed; re-review clean) + eval harness (citation_extraction and rq_framing_patterns both at 100%).
- **Platform Port Reminder CI (#473).** A remind-don't-block workflow surfaces the "Platform ports (community-maintained only)" CONTRIBUTING.md policy when a PR adds a new top-level directory (motivated by PR #470, where a contributor could not have known the policy existed), plus a PR-template pointer.

### Docs

- **Native-reviewed Korean README (#469; contributor credit #471).** `README.ko-KR.md` contributed and translated by [devCharlotte](https://github.com/devCharlotte), with Contributors credit parity across the language READMEs.
- **GitHub Copilot repository instructions (#465).** `.github/copilot-instructions.md` orients Copilot-based contributors to the repo's structure and conventions.
- **Permission-mode guidance (#464).** Install docs now recommend Claude Code's `auto` permission mode over Skip Permissions.

### Rolled up from [Unreleased] (code landed before the v3.13.0 tag)

> Provenance note: the entries below shipped in the repository between the v3.12.0 and v3.13.0 tags, but their changelog bullets had accumulated under `[Unreleased]` across releases. They are versioned here so the release record is complete — no new code ships with these bullets in v3.14.0.

#### Added

- **Diff/patch revision mode — Slice B revision-mode adoption (#89 Item 7, spec #390, sub-issue #424).** The MVP ship-gate slice: `academic-paper` revision mode now runs **anchorize → patch → deterministic apply → finalizer** instead of full re-emission. `draft_writer_agent` gains the `## Patch-Document Revision Emission (#390)` contract (patch document as a `phase6_*/revision_patch_round<N>.json` sidecar — hashes copied from the block manifest, never computed; `[PATCH-ESCALATION-REQUIRED:]` pre-drafting escalation tag; retry-once; provisional Schema 8 items with mechanical fields left to the orchestrator). `pipeline_orchestrator_agent` gains `## Revision-Round Patch Sequencing (#390)` (five normative steps with a no-rewrite window between manifest generation and apply; two-layer escalation gate with the MANDATORY checkpoint wording; never auto-fallback to full re-emission; escalated rounds re-anchorize under a new ID generation and stamp `mode: full_reemission_escalated`; `preserved_ratio` surfaced next to the #389 round-trip count). Schema 8 `ResponseItem` gains optional `change_block_ids` (orchestrator-populated from the apply report, §3.5 role split). New protocol doc `academic-paper/references/revision_patch_protocol.md` (exact Mode B commands, exit codes, apply report as a required re-review input, marker lifecycle). Two recorded ship decisions land as a spec §0 amendment with cross-model concurrence: **`touched_ratio` threshold = 0.6** (now the apply-script CLI default, strict `>`, 1.0 disables) and the **`insert_after` heading-anchor exemption** (anchoring on a heading no longer flags when the inserted text carries no headings; heading-bearing text still flags). §10 open items closed the verified way: `formatter_agent` gains `## ARS Marker Stripping (#390)` (all marker kinds stripped from converted final outputs only AFTER marker-dependent gates; working drafts keep markers) and `word_count_conventions.md` gains the strip-`<!--...-->`-before-count rule (first-party check found NEITHER rule previously existed — the spec's "expectation" had nothing to point at); max single-op `new_text` size folded into the existing triggers (no separate cap). New lint `scripts/check_390_revision_patch_discipline.py` (8 invariants: writer/orchestrator/SKILL/Schema 8/protocol-doc/marker-rules block-scoped literals, threshold value lock, spec-example schema validation) + 30 mutation tests, wired into `spec-consistency.yml` + the pytest manifest.
- **Diff/patch revision mode — Slice A deterministic toolchain (#89 Item 7, spec #390).** First implementation slice of the DELEGATE-52 rank-1 item: the deterministic tools exist and are tested, zero prompts touched (Slice B wires revision-mode adoption). New shared parser `scripts/_block_parser.py` (fail-closed §3.1 block segmentation: fence/heading/table/list/blockquote/text + skipped YAML frontmatter; setext underlines, line-initial raw-HTML openers, and footnote definitions rejected **by name**, never swallowed; duplicate-ID / orphan-marker / marker-stack rejection; read-side-only hash normalization). New `scripts/ars_anchorize_draft.py` (script-owned `<!--block:BNNNN-->` stamping — the LLM never assigns IDs; idempotent and content-neutral; emits the block manifest `<draft>.block-manifest.json`, the ONLY legitimate hash source a patch may copy from). New `scripts/ars_apply_revision_patch.py` (two-phase fail-closed apply: validate-everything-touch-nothing then byte-span splicing, so untouched blocks are byte-identical **by construction**; structural-shape triggers gated by `--acknowledge-structural`; `touched_ratio` recorded in every report with the threshold VALUE deliberately deferred to Slice B; machine-verified `pure_move` pairs; atomic temp+rename writes; apply report with `preserved_ratio` counters). Two new schemas under `shared/contracts/patch/` (`revision_patch.schema.json` — the `DOC-BODY-START` branch is the only legal hash-less op shape; `block_manifest.schema.json`). 86 new tests across three suites incl. the §8.3 byte-identity property test (seeded randomized patches; untouched blocks + marker lines + separator bytes asserted byte-equal), wired as 3 new CI pytest manifest entries.
- **Submission-package verifier Slice 4: terminality (#394 — closes the issue; all four slices landed).** The opt-in blocking layer, shaped by a cross-model gate-1 plan review (1 P0 / 4 P1 / 2 P2, all adjudicated; the P0 resolved as maintainer Option B). New `terminal_policies.submission_package` key (closed enum `{advisory, strict}`, per-key absence = advisory via the evaluator runtime convention — the citation_existence pattern; no JSON-Schema `default`). The **§5.3 single-homed boundary is sharpened, not moved** (Option B): the orchestrator stays the sole *reader/selector* of the policy and hands the resolved value down via the new `--policy` CLI flag; the script *mechanically applies* it — stamps `header.policy_slug` (argparse default **None**: a flag-less standalone run is *unevaluated*, stamped null, and a null-stamped report never satisfies pipeline freshness — never "default advisory"), and under `strict` emits the terminal verdicts: a strict-eligible `fail` → stdout token `TERMINAL-BLOCK policy=submission_package` + exit 1; else a strict-eligible `not_checked` → `VERIFICATION-INCOMPLETE` + new exit 4 (fail-closed §5.2 — a missing parser/profile cannot waive the class the scholar opted into; `not_applicable` never composes into either verdict, keyed on status not the eligibility bit). **Terminal signals are the stdout tokens, never raw exit codes** — exit 1 also carries nonterminal heuristic fails (gate-1 P1). New `--check-freshness` mode (REQUIRES `--policy`): recomputes the package fingerprint + compares the stamped slug, mismatch/null/missing → `STALE-REPORT` + new exit 5, no checks re-run, no writes. The fingerprint exclusion set grows to report + `provenance_summary.md` (gate-1 P1: the formatter appends the advisories section AFTER stamping — fingerprinting the advisory carrier would self-stale every evaluated report). Orchestrator gains the Stage 5 post-formatter **Submission-Package Terminal Gate** section (resolve-absence-to-advisory + always-explicit `--policy`, gate-on-tokens, fix loop bounded 2 rounds then surface, strict-needs-a-venue-profile remediation stated plainly, freshness-before-reuse, recompute-each-pass C-V6(h) mirror); formatter gains the **Submission Package Advisories** `provenance_summary.md` section (mandatory and non-empty iff any fail/warn/not_checked under advisory; stamp-only Invariant 13 untouched). New `scripts/check_394_submission_policy.py` (5 invariants) + 26-test companion — invariant 4 is an **AST single-homed guard** (Subscript/`.get` access of `terminal_policies`), not a literal grep, because the verifier's docstring legitimately says the word (gate-1 P2). 17 new verifier tests (79 in the verifier file; 105 total with the lint companion) incl. an `evaluate_policy` decision-table unit pin (the advisory/strict divergence lives inside the evaluator, not at the call site), byte-equivalence by before/after hashes, and three killed mutations (eligibility gate, fingerprint exclusion, null-freshness reason token). **Gate-2 cross-model diff review (2 P1 + 1 P2, all adopted) + an independent context-reviewer pass over the two prompt sections (2 P1 + 4 P2, all adopted):** a FRESH report now re-emits its policy verdict on `--check-freshness` (same token + exit semantics as a live run — a recorded terminal verdict can never evaporate across a resume), the report header gains `inputs_fingerprint` over venue-profile/passport/join-map bytes (a report produced under one venue profile is STALE under another; legacy reports without the field never read fresh), the v3.10 `policy_hash` marker stamp is scoped to CITATION-TIME keys (`submission_package` never stamps markers — a package-only strict passport no longer forces marker re-finalization or stale-refuses legacy markers; oracle + test updated), the orchestrator gate's advisory path now explicitly re-dispatches the formatter in append-only mode (the advisories section had no named writer), TERMINAL-BLOCK's stdout-vs-marker channel reuse is disambiguated in place (the `policy=` value is the discriminator), the fix-loop round is defined (dispatch formatter → re-run verifier; never a 3rd), VERIFICATION-INCOMPLETE remediation is routed away from the formatter fix loop (a missing profile is not formatter-fixable), token matching is pinned to line-prefix, and the freshness `policy_mismatch` line reprs the stamped slug (a forged report cannot inject a fake token line into stdout). A final confirmation round (2 P2 + 1 P3, all adopted) added the reuse-side roster guard (a hand-edited `checks: []` report is `STALE-REPORT reason=roster_mismatch`, never a clean re-evaluation — the report file is outside the package fingerprint, so content validation must not be skipped on reuse), `--join-map` to the orchestrator's live verifier command (live and freshness invocations must carry the same input set or the inputs fingerprint can never match), and direct-value enum comparison in lint invariant 5 (the string "None" must not pass for JSON null).
- **Submission-package verifier Slice 3: Family A blind-review residue scan + Family D assessment (#394).** The high-embarrassment-cost class. Trigger is presence-or-declaration (§3.1): an anonymized variant in the package (filename stem token `anonymized`/`blind`/…) or a declared `blind_review: double` — untriggered packages report the new **`not_applicable`** status (additive report-schema enum), visibly distinct from `not_checked` so a single-blind package is not condemned to exit 3 forever. Checks: **A1** PDF `/Author` + XMP `dc:creator` via `pypdf` (the only new parser dependency; `defusedxml` is additionally declared in requirements-dev as XML-bomb hardening with a stdlib fallback; pypdf absent → `NOT-CHECKED(parser unavailable)`, never folded into pass per §1.4), **A2/A3** DOCX metadata + tracked-changes/comment authors read RAW from the zip parts via stdlib `zipfile` + XML (`defusedxml` hardening when available) — a refinement over the planned `python-docx`: closer to the §1.3 artifact≠rendered-view premise and the DOCX residue class has no missing-parser hole at all, **A4** acknowledgments section in the blind variant (deterministic signal, strict-eligible ONLY when the profile declares the new `acknowledgments_forbidden_in_blind: true` — the §3.1 load-bearing two-axes rule, enforced via a downward-only eligibility override), **A5** self-citation phrasing (heuristic by class; ships a first-party zh-TW draft list per §10 item 1; curated by the maintainer 2026-06-10, adding 本文作者先前), **A6** author-name tokens from the non-anonymized artifacts' metadata appearing in package filenames (heuristic; the metadata-source originals themselves are exempt), **A7** declared-double-blind with no anonymized variant = fail (the most basic residue: the blind version is missing). **Family D ships nothing**: the slice-3 deliverable is the adjudication-ready assessment (`docs/design/2026-06-10-394-family-d-repro-lock-assessment.md`, recommending no-check with the B4 `required_sections` escape hatch — the `repro_lock` gates-don't-read-it boundary stands untouched; adjudicated Option 2 by the maintainer 2026-06-10). 16 new tests (55 total; corrupt-docx honesty, parser-absence honesty, A4 conditional-strictness mutation killed).
- **Submission-package verifier Slice 2: scholar-declared venue profile + Family B limits checks (#394).** Second slice of the #394 spec. New `shared/contracts/submission/venue_profile.schema.json` (standalone, Invariant 11 pattern; `declared_by: scholar` is the only provenance value and the CLI refuses a profile without the stamp) and a `--venue-profile` flag enabling five deterministic, strict-eligible checks: **B1** manuscript word count, **B2** abstract word count (both ±2% tolerance per §3.2), **B3** keyword count range, **B4** required sections (case-insensitive heading containment), **B5** reference-count ceiling against the same machine-readable reference list Family C uses. The no-inference rule is structural (R-L3-2-D mirror): without a profile every Family B check reports `NOT-CHECKED(no venue profile)`; a partially-declared profile runs what it can and `NOT-CHECKED`s the rest with the undeclared field named; declared limits whose actuals cannot be located (no abstract section, no keywords line) report `NOT-CHECKED` with the reason, never a guess. This also makes the exit-code semantics visibly honest: a profileless run that is otherwise green exits 3 ("passed what was checkable", §8), not 0. Word counting reuses the canonical whitespace-split convention (`shared/references/word_count_conventions.md`); LaTeX counting adjudicated per spec §10 item 4 as naive detex + whitespace-split, with the method and counted file declared in the report detail. Intake Step 3 gains the optional declared-values-only venue-profile follow-up (plan mode exempt, mirroring Steps 12/13) + a PCR `Venue Profile` row. 14 new tests (39 total) incl. tolerance-boundary and provenance-gate mutations; fixture `venue_clean` passes every B check against `profiles/full.yaml`, fixture `venue_violations` fails all five against `profiles/tight.yaml` (mutation discipline). Cross-model review (codex) adopted in full: schema-strict CLI validation (closed field set, bool≠int), `word_count_scope: all` counts everything, and canonical-name manuscript selection with `NOT-CHECKED(ambiguous manuscript)` instead of silently picking the wordiest candidate.
- **Submission-package verifier Slice 1: CLI skeleton + Family C reference integrity (#394).** First implementation slice of the 2026-06-10 #394 spec (slices are dependency-ordered; Family C ships first because it needs zero new parser dependencies). New `scripts/verify_submission_package.py` standalone CLI: point it at any output package directory and it runs the two-way reference-integrity set check (orphan in-text citation = `fail`, uncited reference entry = `warn`) and writes `submission_verification_report.json` validating against the new `shared/contracts/submission/submission_verification_report.schema.json`. The deterministic **joined marker path** consumes `<!--ref:slug-->` markers plus a real prose-reference join — the passport's `citation_verification_summary[]` (`--passport`), an explicit scholar-supplied map (`--join-map`), or a package `.bib` via the documented slug==citation_key identity relation — and markers with NO join source report `NOT-CHECKED(missing prose-reference join)`, never a guessed comparison (§3.3). Non-ARS / post-converted packages fall back to format-aware **best-effort extraction** (`\cite{}` for LaTeX, author-year regex for Markdown), heuristic-classed: the schema STRUCTURALLY forbids `signal_class: heuristic` + `strict_eligible: true`, so the fallback path can never be promoted to blocking by any later policy slice. Report header carries `extraction_path`, `not_checked_count` (incompleteness is never folded into pass, §1.4), `package_fingerprint` (spec §10 open item 3 adjudicated: the audit-snapshot manifest convention — byte-sorted `path:sha256` lines, fingerprint = SHA-256 of the manifest, report file excluded), and `policy_slug` (always null until the slice-4 orchestrator hook; the script never reads `terminal_policies`, §5.3). Exit codes separate "all checked, pass" (0) from "passed what was checkable" (3) per §8. 19 tests + 7 fixture packages with mutation discipline (orphan / uncited / no-join failures proven to fire); CI-wired via the pytest manifest. Advisory-only: no manuscript byte changes, no pipeline hook yet (slice 4). #394 stays open until all slices land.
- **Design doc: deterministic submission-package verifier (#394, blindspot-audit F-5, design-first — no implementation yet).** `docs/design/2026-06-10-394-submission-package-verifier-spec.md` designs `scripts/verify_submission_package.py`, the script-layer backstop for the mechanical subset of the formatter's prompt-layer submission checklists (the #182 promotion pattern: LLM self-check → deterministic gate). Three check families in adjudicated priority order — blind-review residue (raw-structure scan: PDF/DOCX metadata authors, tracked-changes/comment authors, self-citation phrasing; **artifact ≠ rendered view** is a stated premise), venue-declared limits vs actuals (scholar-declared `venue_profile` schema, never inferred from the journal name — R-L3-2-D mirror), reference integrity (two-way set check; the deterministic path requires an explicit slug↔key join source or reports `NOT-CHECKED`) — plus a stretch *assessment* of `repro_lock` presence/shape checking that leaves the recorded gates-don't-read-it boundary untouched. Two load-bearing rules: `signal_class` and `strict_eligible` are separate axes (heuristic checks are structurally excluded from strict; A4's deterministic signal still isn't block-worthy because the de-anonymization judgment is the scholar's), and **strict fails closed on incompleteness** (`VERIFICATION-INCOMPLETE` when a strict-eligible check can't run — a missing parser must not silently waive the one class the user opted into blocking on). Terminality via a new additive `terminal_policies.submission_package` key, evaluated by the orchestrator against a fingerprint+policy-slug-stamped report (package-level freshness guard — explicitly a new post-format gate, not the ref-marker stamp path). Cross-model reviewed (codex): 2 P1 (Family C join requirement; strict fail-open on NOT-CHECKED) + 4 P2 + 2 P3, all adopted. 4 dependency-ordered slices; advisory-only until slice 4.
- **`Real-use findings` release-notes convention documented; showcase refresh tracked (#395, blindspot-audit F-9).** CONTRIBUTING.md gains a Release checklist section documenting the convention: a release's CHANGELOG entry includes a `Real-use findings` subsection when issues were discovered through actual use on a real paper — one line per issue naming the run — so lived-experience provenance has a fixed, greppable home instead of being buried in spec prose (the v3.6.7 production chapter run surfaced 17 drift patterns and nothing structural recorded that provenance class; release motivation since v3.8 has been almost entirely external papers, which is itself a per-release signal worth seeing). Omitted when empty, never padded. The showcase refresh half of F-9 (no post-v2.7 end-to-end artifact set exists) is split to tracking issue #404, blocked on the next real paper with no artificial deadline per the adjudication.
- **POSITIONING records two non-goals; cross-paper workflow guide ships (#397, blindspot-audit F-1B/F-7).** POSITIONING.md's recording discipline (five Rejected mechanisms with rationale) had two adjacent boundaries existing only as silence. A new "Recorded non-goals" section records both with the same boundary-plus-review-criterion treatment: **post-publication lifecycle** (own-paper citation tracking / errata / OA self-archiving — the front is research-to-publication; `monitoring_agent` is unaffected since it alerts on *cited* literature, not the scholar's own output) and **research-program-level state** (no cross-paper claim registry / limitations memory / reviewer-history profile — the per-paper Material Passport stays the only state carrier, a deliberate anti-leakage consequence). The supported no-mechanism path for returning authors ships as `docs/cross-paper-workflow.md`: (1) re-feed the prior paper's passport through the existing input port — a prior `ok` is a head start, not a waiver, stamps re-derive under current policies; (2) bring prior limitations / unresolved reviewer points to RQ incubation as scholar-supplied Socratic input — ARS asks about *your* reading, never derives next-RQ candidates (Kong L2 cross-linked); (3) Claude Code assistant memory may serve as a personal reminder layer with the load-bearing caveat that ARS gates never read or trust it — the workflow must work identically on a machine with no memory at all. Documentation only; no schema, flags, or cross-run mechanism.
- **Intake Step 13: citation-verification level surfaced at the configuration interview (#392, blindspot-audit F-8, adjudicated "keep default, add a prompt so the user chooses").** The v3.11 citation-existence gate's `strict` mode existed only in README prose and the v3.10/v3.11 specs — a QUICKSTART user had no signal the choice existed. The intake interview gains Step 13: "Citation verification: **mark only** (default) / **strict**", with one sentence of field guidance (strict suits DOI-dense fields; mark-only suits grey-literature-heavy fields). **Byte-equivalence is load-bearing**: a `strict` answer seeds `terminal_policies.citation_existence: strict` on the Material Passport at the point it is materialized (the finalizer stays the sole policy *evaluator*); a `mark only` or absent answer records the PCR row and **writes nothing** — per-key absence already means advisory (Invariant 7), so an unprompted run is byte-identical to pre-#392. Plan mode exempt (mirrors Step 12). No default changes anywhere. Guarded by `scripts/check_392_citation_verification_intake.py` (4 invariants, mutation-verified): Step 13 heading present (rename = fail-loud parse error), the no-handoff directive affirmatively reaches Step 13 (`then Step 13` — the exact #327 P1 orphaning that hit Step 12), PCR row present, and the advisory write-nothing rule + strict seeding target retained. 8 unit tests; wired into `spec-consistency.yml` + the CI pytest manifest.
- **Layer-5 contribution-significance probes extended into plan mode and revision coaching (#393, blindspot-audit F-2, adjudicated shape 1).** ARS quality machinery was defect-oriented end-to-end — a paper could pass every gate and still be a micro-extension, because the only constructive contribution coaching (socratic_mentor Layer 5, SIGNIFICANCE & CONTRIBUTION) lived at the RQ-incubation stage. Layer 5 now defines three **later-stage anchored forms** with stable IDs — **L5-W1** "Ten years from now, what will citers say this paper established?", **L5-W2** "Remove this paper from the literature — what is missing?", **L5-W3** "If this paper succeeds, who would make different decisions as a result?" — and two later-stage surfaces consume them strictly by ID (the question text lives in Layer 5 and only there; a Layer-5 edit propagates by reference instead of forking — the cross-model review's P1 on a first draft that carried labeled copies): **(1)** `academic-paper` plan mode gains Step 2.5 CONTRIBUTION SHARPENING between chapter negotiation and the argument stress test — the mentor asks the user to articulate the contribution their own Chapter Summaries claim, quoting only user-written text; if the user articulates one, `[INSIGHT: contribution_claim]` records it in the user's words, otherwise the open question is carried into Step 3, never filled in; **(2)** `academic-paper-reviewer` Phase 2.5 gains step 3, a contribution framing probe alongside the existing prioritization steps (5→6 steps; no external step-number references existed), anchored to what the manuscript already claims. The orchestrator's Stage 3→4 coaching sketch now explicitly defers to the reviewer SKILL.md six-step list as authoritative (net-zero line edit — the surface has 1 line of v3.6.7 budget headroom left). Boundary is load-bearing (Kong L2 verb test, per the #393 adjudication that rejected shapes 2–3): questions only — never propose, substitute, rank, expand, or select a contribution claim. Prose-layer only; no schema, scoring, or agent-roster change. Two review gates, all findings adopted: codex cross-model (1 P1 + 2 P2 + 1 P3 — ID-based single-sourcing, verb-test tightening, orchestrator deferral, conditional INSIGHT) and an independent context reviewer (1 P1 + 1 P2 — the repo has TWO same-named `socratic_mentor_agent.md` files and plan mode dispatches the academic-paper variant, which had no Layer 5 and no Step 2.5 in its own flow, so the probe would never have fired: the agent prompt gains a Step 2.5 section referencing L5-W IDs by full path, the protocol's inline reference is path-disambiguated, and L5-W3's anchor permission is tightened to noun-phrase-swap-only).
- **Interaction-count budget surfacing + Context Hygiene dispatch discipline (#388; DELEGATE-52 Items 4+5 from #89).** The two cheap, high-confidence follow-ups from the re-ranked DELEGATE-52 work order (arXiv:2604.15597), both prose-layer. **Item 4:** the v3.2 Budget Transparency block in `academic-pipeline/SKILL.md` now also presents an **interaction-count budget** at pipeline start — the paper's core result is that long-horizon corruption compounds with document round-trips, not token volume, so the block enumerates the round-trip caps the pipeline already enforces (2 revision loops, 8+5 Socratic coaching rounds, the integrity fix→re-verify loop), states the worst-case total for the chosen mode, and reports the accumulated count at every stage checkpoint. Advisory only — the per-loop caps remain the enforcement layer; exceeding the stated worst case signals an uncovered loop and must be surfaced, never silently continued. **Item 5:** `pipeline_orchestrator_agent.md` gains a **Context Hygiene at dispatch** block targeting the paper's distractor ablation (non-target documents in context measurably worsen outcomes): each handoff carries the receiving agent's declared inputs plus the Material Passport — never the accumulated pipeline as a convenience bundle; scratch output and superseded drafts do not ride forward (later stages read passport entries, not raw transcripts); supersession means dispatching the current version only, with prior versions retrievable through the versioned-artifact trail. The passport carry-forward obligations (claim/audit aggregates, `experiment_intake_declaration`, `slr_lineage`) are explicitly exempt — trimming applies to loose materials, never passport fields. Carries an epistemic-status line (dispatch-assembly discipline, not a runtime guarantee). Scope note recorded in #388: this lands the single-dispatch-point version; #89's per-downstream-agent sketch stays open under the parent. Items 1, 2, 7, 8, 9 remain tracked in #89.
- **Repository-hygiene CI (#151).** A `repository-hygiene.yml` workflow runs gitleaks over the **full git history** on every PR and main push, with the upstream default ruleset and **no custom rules**. The binary is version-pinned (8.30.1) and **checksum-verified** rather than pulled via the marketplace action (which needs an org license key; a pinned release binary keeps the supply chain auditable), and `--redact` keeps any genuine hit out of public CI logs. The only local configuration is a false-positive allowlist (`.gitleaks.toml`): the 2026-06-10 baseline evaluation found **43 findings across 518 commits — every one a bibliographic citation key** (`Becht2019UMAP`, `vaswani2017-arxiv-v1`, `forthcoming2024`) in eval gold tuples / adapter fixtures / version-family examples matching the `generic-api-key` heuristic's key-shaped-string pattern, **zero true positives** — so those literature-identifier paths are allowlisted by path, never by rule edit (a new tuple under an allowlisted path needs no config touch). A seeded-credential mutation test confirms the configured scan still exits 1 on a real-pattern secret outside the allowlist (`github-pat` hit) — and recorded a method caveat: a low-entropy dictionary-word seed does NOT clear the entropy gate, so a valid mutation check needs a real-pattern, high-entropy seed. Closes the `defer:v3.10` evaluation with an **adopt** decision: all three decision criteria pass (no infra burden — public pinned binary; bounded maintenance surface — path entries only; post-allowlist FP rate 0 on the full history).
- **Field-norm severity calibration across the reviewer surfaces (#215, Kim et al. 2026 arXiv:2605.20668v1 §5.1 W1 + §F.3.4).** Closes the paper's largest documented AI-reviewer failure class: a critique that is content-correct against a discipline-neutral standard but **severity-miscalibrated** because the reviewer lacks the subfield's accepted-practice prior (W1, n=54 — the CERN/LHCb reproducibility example), plus the sibling significance-boundary error from the "would addressing this change the core result?" formula (§F.3.4, 56 errors). Three reviewer surfaces are hardened, each at severity-assignment time and applying to **every** field-norm-dependent finding (not only CRITICAL): **`domain_reviewer_agent.md`** gains a Step 5 hard rule — a severity that rests on a field norm MUST be grounded in an external checkable source (a reference, venue/data policy, community standard, reporting guideline, or documented expert practice — explicitly **not** limited to a literature citation, and **not** model knowledge), else down-rate to advisory + `[FIELD-NORM UNVERIFIED]`; **`devils_advocate_reviewer_agent.md`** gains a 9th challenge dimension (the DA turns the lens on its own findings, since adversarial intensity amplifies an ungrounded norm into a CRITICAL) plus two required CRITICAL/MAJOR output columns `field_norm_boundary` + `evidence_crossing_rationale`; **`calibration_mode_protocol.md`** gains a Phase 3.5 severity-miscalibration measurement + a low/med/high histogram in the Calibration Report — a signal the binary FNR/FPR matrix cannot show, where the classifier rates whether the reviewer **supplied external grounding**, not whether the norm is factually correct (guessing norm-correctness would repeat the very W1 failure under audit). A **first-party regression fixture** ships at `evals/gold/field_norm_severity/` (10 cases — 5 W1 field-norm-boundary + 5 §F.3.4 significance-boundary — extracted verbatim from the paper with section/example-ID + paper-citation-token + verbatim-anchor provenance; the SAR 11.7T case flagged `exception: true` because experts concurred with the AI there). Because there is no deterministic detector for field-norm severity miscalibration, the fixture is a regression set, not a calibration set: `scripts/check_field_norm_severity.py` validates data integrity + first-party provenance (no FNR/FPR ritual), and `scripts/check_215_field_norm.py` asserts all three reviewer surfaces carry their blocks with **block-scoped** keyword checks (fence-aware) so a stray keyword cannot mask a missing rule. The two lints survived a three-pass cross-model (codex xhigh) review that drove finding count 4 → 2 → 0; every fix is mutation-tested (28 tests). Additive and backward-compatible; CI-wired via the spec-consistency workflow + pytest manifest. (#216 — the §F.3.6 reviewer-type parity half — was split out: it needs a different gold set of human-phrased vs AI-phrased paired cases.)
- **Surface-Form Parity self-check (#216, Kim et al. 2026 arXiv:2605.20668v1 §F.3.6).** Closes the paper's reviewer-type asymmetry: an AI meta-reviewer applying **two standards keyed off prose style** — demanding literal precision from informal/vague (human-typical) wording, so it over-rejects correct concerns (29 of 41 correctness false negatives involved human reviewers), and crediting technical specificity in precise (AI-typical) wording, so it over-accepts incorrect ones (10 of 13 false positives involved AI reviewers). The root cause the paper names is a learned prior that *specificity correlates with correctness*. **Key design call (after a codex xhigh consult): the hook is prose style, NOT the author label** — so the mitigation is a *Surface-Form Parity* self-check (not "authorship parity"), and authorship is kept **out** of the runtime reviewer-item schema entirely (not merely audit-only). **Two verdict-time surfaces** carry the parity self-check (a codex review found the editorial synthesizer also arbitrates reviewer sub-claims and down-ranks "too vague" criticisms — exactly where §F.3.6 fires): **`devils_advocate_reviewer_agent.md`** gains a verdict-time parity self-check (a marker block, distinct from #215's severity-time gate) and **`editorial_synthesizer_agent.md`** gains a Step 1c arbitration-time check + a reworded "reduce weight if too vague" rule that fires only when vagueness makes a sub-claim unevaluable. The DA check: extract the checkable claim → judge it against the paper not the polish → do **not** down-rate informal/vague wording unless ambiguity changes truth conditions → do **not** credit technical specificity without checking → run the opposite-style counterfactual and revise / mark ambiguous on a flip. A **mixed-provenance regression fixture** ships at `evals/gold/surface_form_parity/` (7 cases: 4 `paper_verbatim` §F.3.6 examples + 2 maintainer-authored `counterfactual_rewrite` paired variants carrying `derived_from` + `semantic_equivalence_rationale` + 1 `maintainer_boundary` documenting the "unless unevaluable" clause). Because there is no deterministic detector for the surface-form bias and the 29/10 split is directional (§H), the fixture is a regression set, not a calibration set: `scripts/check_surface_form_parity.py` validates integrity + **provenance honesty** (paper_verbatim quotes the paper; maintainer-authored items never claim paper-verbatim) + **pair invariants** (paired items hold claim + verdict constant, differ only in framing) + no rotting pdftotext line anchors — no FNR/FPR ritual. The **schema decision is enforced at runtime** by `render_judge_view()`, a whitelist projection (judge sees only an index-derived opaque `handle` + `review_item_text`) proven by a serializer-strip test to leak no blind field — including the nested `provenance.reviewer_source` author label and the answer-encoding fixture `id` itself (`-cf` / `-ambiguous` suffixes, per codex review). `scripts/check_216_surface_form.py` asserts the DA carries every load-bearing clause **block-scoped + fence-aware** (six-class mutation suite). `run_evals` discovers the fixture and marks it `pending` (no native measurer, by design — pinned by a `test_run_evals` test so it cannot false-green through the eval gate). **Negative scope: #273 (rubric-aware calibration) is NOT folded in** — it is a different mechanism (an interpretive caveat with no detection claim); #216 carries a cross-reference only (design note + PR body + `manifest.yaml` `related_issues`), with no shared prompt / gold / lint / runtime wiring. Additive and backward-compatible; CI-wired via the spec-consistency workflow + pytest manifest. Design note: `docs/design/2026-06-09-216-surface-form-parity-design.md`.

#### Changed

- **Plugin-root `agents/` symlinks materialized as real byte-identical copies (#413, external audit).** The three `agents/*_agent.md` files were relative symlinks into `deep-research/agents/` (v3.7.0 Phase 2.1) — on Windows checkouts without developer mode / `core.symlinks`, and in zip-download installs, they materialise as one-line text files containing the link path, silently breaking the three plugin agents. Maintainer-adjudicated fix: real copies, with the single-source guarantee the symlinks provided (the v3.7.0 Pattern C3 rationale for symlinks-not-copies) taken over by a new CI lint, `scripts/check_agents_mirror_sync.py` — a hard-pinned mirror roster enforcing set equality (a deleted mirror silently un-ships an agent; an unrostered addition has no declared source), regular-file-never-symlink (the regression itself, checked *before* byte-equality because a symlink trivially byte-matches its own target), and byte-equality with the canonical source (fix hint names the copy direction: edit the source, re-copy, never edit the mirror). The two lints that leaned on symlink resolution adapt: `check_version_consistency.py` invariant 8 now excludes the mirror dir from the unique-agent count outright (real copies no longer dedup via `resolve()`; the exclusion is sound because the mirror lint pins every file there as a pure alias), and `check_v3_10_134_write_scope.py` I5 maps a root-`agents/` file BY NAME to its `deep-research/agents/` source before the roster check — with a negative test pinning that the mapping is not an allowlist (a name with no rostered source still flags as fail-open). 10 new mirror-sync tests (3 mutations killed: symlink-branch, byte-equality, unrostered-extra) + 5 adapted/added tests across the two existing suites; lint + pytest companion wired into spec-consistency CI. Cross-model review round (1 P2, adopted with an empirical repro): the I5 remap is restricted to DIRECT children of root `agents/` — a nested `agents/sub/agents/<rostered-name>.md` no longer remaps to the deep-research source (which would have silently reopened the fail-open case the recursive glob exists to catch), pinned by a negative test. The `skills/` directory symlinks are unchanged — materializing those means duplicating the four skill trees, a separate decision if Windows source-checkout support is ever pursued. (2026-06-10 audit; follows the #301/#347 4.7→4.8 pattern).** Trigger: the primary session model moved to Fable 5, which inverts the v3.7.0 `model: opus` frontmatter floor on the three heavy commands (`/ars-full`, `/ars-reviewer`, `/ars-revision-coach`) into a **silent downgrade ceiling** — those commands now inherit the session model (the 11 light-mode `sonnet` pins are deliberate cost routing and stay; the plugin agents were already `model: inherit`). Display-name drift retired at the remaining pin sites: the `shared/cross_model_verification.md` primary-model row is now generation-agnostic ("the inherited Claude Code session model" — it stops needing a per-release bump), the SessionStart announce + `docs/PERFORMANCE.md`(+zh-TW) cost anchors are provenance-labelled ("measured on Opus 4.x", order-of-magnitude) instead of asserting a two-generations-stale "$4–6 on Opus 4.7", and the disclosure-protocol e.g. list is refreshed. OpenAI verifier lineup unified gpt-5.4 → **gpt-5.5 / gpt-5.5-pro**: the citation judge already defaulted to `gpt-5.5-xhigh` while the verification doc still taught 5.4 — and the availability case-glob `gpt-5.4*)` rejected 5.5 ids outright; web_search-on-Responses support and pricing were verified first-party 2026-06-10, legacy `gpt-5.4*` ids remain accepted, and the cost table is re-anchored on gpt-5.5 ($5/$30 per 1M). Routing smoke recalibration (#133 fixtures): **8/8 routing-class pass on Fable 5** (clarify/proceed plus all three escape-hatch behaviors — byte-0 honored, mid-message rejected, case-insensitive accepted); two destination picks additionally required the Routing-Rules/MODE_REGISTRY context the manual protocol provides. The acceptance threshold in `tests/fixtures/issue_133_routing/README.md` is reworded from "100% on Opus 4.7" to "100% on the current primary model" so the definition stops drifting per release. Two bare anti-hallucination tails on the compliance surfaces are kept as annotated debt (high-stakes domain, silent failure mode — in-file `harness-retirement` annotations added). Deliberately out of scope, tracked separately: re-baselining the #272/#273/#274 model-behavior premises against the Fable 5 system card, and a negative-framing sample-reframe of the top-3 agent files at the next minor.

## [3.13.0] - 2026-06-18 — Hook portability, provider-agnostic verification, guard correctness

### Fixed

- **Write-scope guard: `CLAUDE.md` dropped from infra-protected globs (#459).** Closes the residual half of #448/#449. #449 anchored infra self-protection on `plugin_root` (fixing #448 for the plugin install layout), but under the traditional git-clone + symlink-into-`~/.claude/skills` layout there is no `CLAUDE_PLUGIN_ROOT`, the `plugin_root` fallback resolves to the cloned repo root, and a user working IN that repo has `plugin_root == workspace_root` — so the bare `CLAUDE.md` / `.claude/CLAUDE.md` infra globs matched the user's own `CLAUDE.md` and re-denied it (the #448 bug, on a layout #449 cannot distinguish: home turf and clone-as-user are the same runtime condition). Fix (codex-consulted, Option 2): remove `CLAUDE.md` and `.claude/CLAUDE.md` from `INFRA_PROTECTED_GLOBS`. Unlike every other infra entry, `CLAUDE.md` is NOT load-bearing — it documents the guard binding, it is not the binding, so editing it cannot fail the guard open. The load-bearing enforcement files (guard script, manifest, hooks, plugin metadata, agent frontmatter, lint) stay protected on home turf; protecting ARS's own instruction doc from agent edits belongs in review/CI, not the write-scope guard. 3 new tests + 1 retargeted, mutation-verified (re-adding the globs fails the new tests); 73 guard tests pass.
- **Windows Python hook portability + graceful no-Python degradation (#454).** The `PreToolUse` write-scope guard was wired as a bare `python3 ".../ars_write_scope_guard.py"`. On Windows `python3` is commonly a 0-byte Microsoft Store App Execution Alias stub, so the hook errored before the guard's own fail-safes could run and spammed the hook log every call. A new cross-platform launcher `hooks/run_guard.sh` (POSIX sh; `hooks.json` now invokes it via `bash`) finds a REAL interpreter — `py -3` / `python3` / `python`, each verified by a marker probe that must exit 0 AND print the marker (a stub that prints then exits non-zero is rejected) — then runs the guard as a supervised, time-bounded subprocess. **Plan A graceful degradation** (the guard is optional v3.10 hardening; ARS core needs no Python): if no real interpreter is found OR the guard subprocess misbehaves (non-zero, timeout, empty, or non-JSON / missing-key output, validated by a real `json.load` not a substring grep), the launcher emits a valid pass-through hook JSON and exits 0 — it never exits non-zero and stays silent on stderr on these degraded paths (PreToolUse is a hot path; per-call stderr is the spam #454 is about). Healthy-guard stderr advisories are relayed. New `scripts/test_run_guard_launcher.py` (21 tests, run from a temp plugin layout so the guard is always resolved from the launcher's own `../scripts/` — no production env back door); the `hooks.json` CI assertion now requires a line-anchored non-comment guard assignment AND the `GUARD_OUT=$(... | run_bounded ... "$GUARD")` exec call site rather than a bare filename substring (a comment or an `echo`-wrapped decoy no longer false-passes). New `.gitattributes` pins `*.sh eol=lf`. README documents the Git Bash prerequisite (without it Claude Code falls back to PowerShell, which cannot run the `.sh` launcher, so the guard is inactive and the hook logs per call instead of no-opping quietly).
  - **Real-use findings**: a two-model dual-track implementation review (codex + gemini, both POSIX-reproduced) hardened the launcher far beyond the original wiring fix, and the cross-model split was load-bearing — each model caught real bugs the other missed. Round 5 (codex) found the marker probe ignored exit status, the guard ran unbounded, and the JSON check was a substring grep. Round 6, once the tests exercised the REAL watchdog on a host with neither `timeout` nor `setsid`, found three fail-open bugs the back-door tests had masked: the no-`timeout` fallback fed the guard an EMPTY stdin (a real `deny` was silently lost — the guard was dead on any timeout-less host), an un-reapable orphan grandchild could wedge the `$(...)` capture, and the watchdog could false-report a timeout for a command that finished within the bound. The independent **gemini track** then refuted codex's first race fix (a successful `kill` does NOT prove the child is still alive — after `wait` reaps it the pid can be RECYCLED, so a blind kill could hit an innocent process and still false-flag a timeout) and added two fail-open findings codex missed: a predictable `/tmp` fallback when `mktemp` fails is a symlink-attack surface whose redirect failure reads as a broken guard, and the CI exec assertion was still gameable by an inline comment or an `echo`-wrapped call. Final state: stdin stashed on fd 3, stdout captured via a private temp file, timeout decided by a **done-file handshake** (the parent disarms the watchdog before reaping it; the watchdog kills/flags only while the done-file is absent — no pid-reuse race), `mktemp` failure degrades to pass-through instead of a guessable path, and the CI assertion is line-anchored. Orphan-grandchild leakage in the doubly-degraded no-`timeout`/no-`setsid` path, and a multi-megabyte payload held in a shell variable, are documented as accepted trade-offs (the real probe and guard spawn no grandchildren and ordinary hook payloads are small; the robust alternatives add temp-file lifecycle / symlink surface to a hot path).
- **`draft_writer` dual-phase static union documented + POSIX-safe Windows path matching (#451, #330).** Documentation + portability fix for the draft writer's dual-phase static union; path matching made POSIX-safe for Windows checkouts.

### Added

- **Provider-agnostic cross-model verification (#455).** The cross-model verification layer now accepts OpenAI-compatible endpoints (MiMo, DeepSeek, self-hosted) alongside first-party OpenAI via a normalized compatible-verdict path (`scripts/cross_model_verification/normalize_compat_verdict.py` + `check_cross_model_verification_sync.py`). The grounded first-party OpenAI path is preserved and deliberately NOT routed through the standard `OPENAI_BASE_URL` (so an existing proxy user is never silently downgraded to the ungrounded compatible path — the grounded-proxy gap is tracked separately in #456). Design: `docs/design/2026-06-16-453-provider-agnostic-cross-model-verifier-spec.md`.
- **Opt-in Socratic adjacent-framing probe (STORM-borrowed perspective expansion) (#461; `deep-research` 2.10.0 → 2.11.0).** When `ARS_SOCRATIC_ADJACENT_PROBE=1` is set, the Socratic Mentor may, in **exploratory** sessions during **Layer 1 (Problem Framing)**, surface ONE adjacent research framing the user has not raised — as a pure question ("an adjacent facet you haven't raised: <category phrase> — include it, or set it aside?"), never a proposed idea. Borrows the *intent* of Stanford OVAL STORM / Co-STORM (https://github.com/stanford-oval/storm): STORM's perspective discovery and Co-STORM's moderator inject framings adjacent to — but not directly answering — the current question to break local stagnation. ARS anchors framings in **LLM internal knowledge (zero retrieval)**; majority-favour is a deliberate tradeoff for the novice target (mainstream-facet visibility helps researchers who haven't seen enough), with external-TOC retrieval left as a pluggable forward note. Hard-bounded by the Kong L2 verb test — never propose/substitute/rank/expand/select; surface-and-ask only, one facet at a time, max 2 per session ≥3 rounds apart. S4 (Scope Stability) is repurposed as an intensity knob (early scope-lock raises the tendency), reusing existing state — no new counter. One-push-then-retreat on decline; `[ADJACENT-PROBE: ...]` log tag flows into Stage 6 self-reflection (a high decline rate is the bias-visibility signal). Default OFF. No new agent / mode / schema — prose-layer only, same shape as the v3.5.1 Reading Probe. Gate fires **exploratory** (opposite of the goal-oriented Reading Probe). Two review gates, all findings adopted: a spec-compliance pass (✅) and an independent semantic red-line reviewer that caught a Critical — the canonical GOOD example originally used "the teacher's mediating role," a hypothesis disguised as a category word (semantically identical to the BAD-propose row, and contradicting the agent's own WP14 flag); replaced with a true perspective phrase so the GOOD/BAD boundary is semantic, not grammatical. New lint `scripts/test_adjacent_framing_probe_lint.py` (10 tests, mutation-verified; adding the sibling env var also exposed and fixed an over-broad regex in `test_reading_probe_lint.py` that mis-flagged it as drift). See `deep-research/agents/socratic_mentor_agent.md` §"Optional Adjacent-Framing Probe Layer" and `docs/design/2026-06-18-socratic-adjacent-framing-probe-spec.md`.

### Chore

- **Zenodo DOI added (#443, #434).** `CITATION.cff` + README DOI badge wired to the Zenodo concept DOI.

## [3.12.1] - 2026-06-15 — Reviewer-response triage modes (PR #433 integration)

### Added

- **`deep-research` `three-way-scan` mode** — a lightweight WHY/HOW/WHAT paper-comparison triage that sits between `quick` and `lit-review`. Produces a per-paper WHY/HOW/WHAT shortlist plus a cross-paper synthesis (common WHY, divergent HOW, strongest WHAT, unresolved gap), and escalates to `lit-review` / `systematic-review` for full coverage. (`deep-research` 2.9.4 → 2.10.0)
- **`academic-paper` `rebuttal-audit` mode** — standalone advisory QA of an author's existing rebuttal/response draft against the reviewer comments (per-comment coverage table + gap list + risk flags for tone/evidence/misread). It generates nothing and, because a standalone invocation runs outside the pipeline, it **explicitly suppresses** Schema 11 emission / Material Passport writes / `ready_to_submit` status — enforced by a new `check_rebuttal_audit_guard()` lint with mutation coverage. Routed by input shape: both reviewer comments AND an existing draft → `rebuttal-audit`; comments only → `revision-coach`.
- **`revision-coach` scope extension** — its trigger/docs now cover pushback/disagreement posture and non-journal scopes (conference rebuttal, grant-panel response, transfer-after-review).
- **`/ars-3w` and `/ars-rebuttal-audit` slash commands.**

### Credit

Integrated from [@Yaobin29](https://github.com/Yaobin29)'s [PR #433](https://github.com/Imbad0202/academic-research-skills/pull/433). The original PR proposed a standalone `reviewer-response` skill; this release folds its genuinely-novel parts into existing skills as modes, per ARS's mode-based architecture. The `rebuttal-audit` mode rescues that PR's `audit` concept. Suite mode count 25 → 27 (still 4 skills).

## [3.12.0] - 2026-06-08 — Kong auto-research feature track: experiment provenance, figure fidelity, cross-paper contradiction, partial-evidence decomposition

### Added

- **Experiment Provenance Intake + claim→experiment alignment — a schema-first evidence-ledger layer for experiment-backed claims (#260, Kong et al. 2026 §3.3 + §7.4.3).** ARS deliberately keeps experiment *execution* outside the pipeline; the scholar runs experiments externally and brings results back. This change adds the **intake + alignment** layer only — it does **not** run experiments, judge whether one was correctly designed/run/statistically-adequate/reproducible, auto-fill provenance, or require provenance for literature-only pipelines. Two blocks ship together. **Block A — `experiment_provenance[]` intake array:** a new optional Material Passport aggregate (`shared/contracts/passport/experiment_provenance_entry.schema.json`) where each scholar-entered entry carries a **nested `repro_lock`** (the same inline-object shape as the passport-level lock, re-declared not `$ref`'d because the source is inline prose, not a schema file), a `planned_vs_executed[]` record (each `executed:false` unit carries a gate-checked `skip_reason`), and `negative_results[]` / `known_limitations[]` arrays whose **key must be present** (an empty `[]` is well-formed and routes to a disclosure advisory; an *absent* key is malformed → gate FAIL, the absent-key rule ported from #261's C3). **Block B — claim→experiment alignment:** the claim manifest gains an optional per-claim `planned_experiment_ids[]` join field (parallel to `planned_refs`, minItems 1, optional-absent), and a new **fourth ref_slug-less claim-finding aggregate** `experiment_alignment_results[]` (`experiment_alignment_result.schema.json`) — alongside the existing `uncited_assertions` / `claim_drifts` / `constraint_violations` siblings — with an experiment-specific MECE verdict enum `{ALIGNED, OVERSTATED, NOT_SUPPORTED_BY_PROVENANCE, PROVENANCE_INSUFFICIENT}`. The verdict is **produced by the integrity verification agent AT the gate** (Stage 2.5 sampling / Stage 4.5 full), not by the citation-audit agent at the Stage 4→5 boundary — mirroring #261's Phase C3, so the row is emitted and gated in the same pass and the stage-ordering race (a verdict landing *after* the gate ran) cannot occur. A **mixed-evidence claim** carrying BOTH `planned_refs` and `planned_experiment_ids` is audited by both paths and the gate decision is **worst-verdict-wins** (an OVERSTATED experiment path blocks even when the citation path is SUPPORTED). **`experiment_id` is frozen at intake** (a post-intake rename is a re-intake event, not a silent edit). Seven new cross-array invariants land in `scripts/check_claim_audit_consistency.py` (JSON Schema cannot express cross-array integrity): **EP-INV-1** (experiment_id unique/passport), **EP-INV-2** (planned_experiment_ids resolve — doubles as the rename + forward-reference dangling-pointer guard), **EP-INV-3** (experiment ids ⟹ empirical kind; mixed literature+experiment allowed), **EP-INV-4** (declaration↔provenance symmetry), **EP-INV-5** (declaration well-formedness when present: `status` enum / `declared_by: scholar` / non-empty `declared_at` — so a malformed declaration like `status: "garbage"` FAILs deterministically instead of slipping past the symmetry check), **EA-INV-1** (finding_id unique), **EA-INV-2** (alignment-row references resolve; a dangling `experiment_id` is a structural FAIL, **never** a `PROVENANCE_MISSING` verdict — that value is deliberately absent from the enum, so no fake judge fields are forced for a row where no judge ran). A persisted passport-level **`experiment_intake_declaration`** closes the anti-skip circularity with a fail-closed legacy boundary, split across two enforcement layers (stated precisely, not conflated): the **lint deterministically enforces** declaration↔provenance *symmetry* (EP-INV-4) and declaration *well-formedness* (EP-INV-5); the **integrity gate (a Stage-1/Stage-4.5 check, NOT the lint) owns the `ars_version` numeric legacy decision and the declaration-presence FAIL** — a passport is `legacy_unknown` (advisory) only with positive `repro_lock.ars_version < #260-constant` proof, everything else (including a passport with no `repro_lock`, or one with no `ars_version`) is treated as post-#260 so the declaration is REQUIRED and its absence FAILs at the gate, meaning a new run cannot dodge it by making its version unprovable. The `ars_version` numeric half is deliberately left at the gate layer (not promoted to a lint constant) because the #260 release version it compares against is frozen at ship time, not at intake. Literature-only pipelines therefore still emit a one-line `no_experiments_declared` declaration (no `experiment_provenance[]` needed). Producers taught in lockstep (schema-first writer-binding discipline): the three manifest emitters (`synthesis_agent` / `draft_writer_agent` / `report_compiler_agent`) emit `planned_experiment_ids` when an experiment backs a claim; the integrity agent gains a new disclosure-only Phase (D6) carrying the POSITIONING non-goal verbatim ("does not judge whether the experiment was correctly designed, run, statistically adequate, or reproducible by ARS"); the orchestrator carries `experiment_alignment_results[]` + the declaration forward; README intake detection sets the declaration. **Drift guard:** the repro_lock field set is single-sourced in `scripts/repro_lock_validation.py` (imported by both `check_repro_lock.py` and the new standalone `check_experiment_provenance.py`), with a drift test asserting the nested schema's required keys equal the shared constants. **Three documented departures from the issue's literal text** (each corrected after a first-party tracked-repo read): `repro_lock` is an inline-prose object, not a schema file, so "inherit repro_lock" means nesting the shape, not `$ref`'ing a non-existent file; the claim manifest had no experiment pathway, so the join is *added*, not assumed; and "Path X / Tier-1 required / writer-binding" are not named conventions in the tracked repo, so the discipline is *described* rather than cited by a name a reader cannot find. Schema + manifest edit + 7 lint invariants + standalone shape validator + drift guard + integrity/writer/orchestrator agent prompts + README mirrors + `examples/passport_with_experiment_provenance.yaml` (2 experiments, a mixed-evidence claim, an OVERSTATED alignment row) + full TDD suite (schema ±, fail-closed symmetry, declaration well-formedness, mixed-evidence two-row, verdict-derivation, mutation-verified non-vacuous invariants, reverse-invariant producer pins, drift, literature-only regression). The new schemas, the manifest field, and all seven invariants are additive and backward-compatible. Spec: `docs/design/2026-06-08-260-experiment-provenance-intake-spec.md`.
- **Cross-paper contradiction inventory — structured, inspectable enumeration in the synthesis layer (#262, Kong et al. 2026 §7.4.2).** `synthesis_agent` already had prose-level contradiction handling (Anti-Pattern 3, the Step 3 Contradiction Resolution procedure, and the Contradictions & Resolutions table), but that prose narrative-discussed contradictions (including reconcilable-vs-irreconcilable verdicts) without making the *set of assessed paper-pairs* and the *unresolved / checked-clear* pairs enumerable for the scholar to confirm — the multi-paper relational-reasoning gap Kong et al. 2026 (arXiv:2605.18661 §7.4.2) document for research-synthesis systems. A new **Step 3b — Cross-Paper Tension Inventory** is added **additive to** (not a replacement of) the existing Step 3 prose: the agent emits a `cross_paper_tensions[]` markdown block — one entry per assessed candidate pair carrying `pair_id`, `paper_a`/`paper_b`, `candidate_basis`, `overlap_topic`, `a_finding`/`a_evidence_pointer`, `b_finding`/`b_evidence_pointer`, `pair_assessment`, `resolution_status`, an iff-resolved `resolution_pointer`, and `scholar_confirmation`. **Prose-layer only — no JSON Schema, no lint invariant, no gold fixture** (mirroring the #214 / #261 prose-layer decision, NOT the #213 schema-layer one): the producer (`synthesis_agent`) and the readers (the scholar plus the report/integrity LLM agents) all read prose, there is no deterministic downstream parser, and the judgment that matters — "is this a genuine contradiction vs. a conditional difference" — is irreducibly semantic, so machine-validating the YAML shape would prove field presence, not contradiction fidelity. **This deliberately departs from the issue's literal acceptance** (which read "schema adds `contradiction_pairs[]` block" + "calibration gold set accuracy ≥ 0.75"): the named "downstream consumers" (formatter, integrity_verification) are themselves LLM agents reading markdown — there is no machine consumer — so a schema would be the exact false rigor #261 rejected, and 20 LLM-judged pairs are too few and too nondeterministic across runs to wire as a hard CI gate (**no calibration artifact ships** in this change — any future or manual calibration should be recorded out-of-band with its model/date/prompt + a confusion matrix and stay non-blocking, never a pass/fail gate). The **field model is corrected from the issue's non-MECE draft**: the issue's single `conflict_type ∈ {contradictory, conditional_difference, resolved_in_synthesis}` folded conflict *nature* and resolution *status* into one enum and referenced an `insufficient_overlap` value not in it — these are split into orthogonal axes (`pair_assessment ∈ {contradiction, conditional_difference, no_material_conflict, insufficient_overlap}` × `resolution_status ∈ {resolved_in_synthesis, flagged_unresolved, not_applicable}`), and each side gains an `evidence_pointer` so a finding cannot be stated as free text the paper does not support. **Candidate-pair scoping is a recall-limited heuristic, not an algorithm:** an LLM agent does not execute an O(K²) enumeration, so the design states it as bounded candidate-edge generation (include a pair on shared RQ subtopic / shared construct / opposite finding direction / bibliographic coupling / scholar flag) with two honesty rules — bibliographic coupling is an *inclusion* signal only, never an *exclusion* rule (same-camp papers cite the same priors and tend to agree; cross-camp contradictions have low coupling), and cross-neighborhood pairs can be missed, so every inventory carries a mandatory **Coverage Note** stating the denominator and the explicit recall limitation and the agent must never write "all contradictions addressed." Inherits `synthesis_agent`'s narrative-side discipline unchanged (advisory-only: the scholar makes the final call; the agent emits `scholar_confirmation: pending`, never self-confirms, simulates no audit step, and reads no entry frontmatter). No `#111` dependency (that is a single boolean, per the issue's own correction). Adds `examples/contradiction_pairs_example.md` (6-paper remote-work synthesis covering a genuine unresolved contradiction, a resolved conditional difference, an *un*resolved conditional difference (so both resolution states of one assessment are shown), a no-material-conflict pair, an insufficient-overlap pair, and a Coverage Note that names the still-unpaired cross-neighborhood paper). Agent-prompt + output-template + doc example only; no schema, lint, or executable change.
- **Figure/Table Fidelity Gate — the visual analog of the §F.3.2 partial-evidence trap (#261, Kong et al. 2026 §3.4).** The VLM Figure Verification Protocol checked *"does the rendered figure match the source data?"* (a faithful-rendering check) but could not check *"does the caption's interpretation follow from the data, and does the manuscript cite this artifact for a claim it actually supports?"* — a figure can render perfectly while its caption overstates the data or the manuscript cites it for an unsupported claim (Kong et al. 2026, arXiv:2605.18661 §3.4). This is the visual counterpart of the prose partial-evidence trap addressed for citations in #213 and for review synthesis in #214; same trap, different artifact type, separate implementation. **Prose-layer only — no JSON Schema, no lint invariant, no gold fixture** (mirroring the #214 prose-layer decision, NOT the #213 schema-layer one): the `figure_table_trace[]` producer (`visualization_agent`) and consumer (`integrity_verification_agent`) are both LLM agents reading a markdown Figure Package, so there is no deterministic downstream parser and machine-validating the YAML shape would be false rigor. `academic-paper/references/vlm_figure_verification.md` gains a **Figure/Table Trace** section defining a `figure_table_trace[]` block — one entry per figure (or manuscript table that has an entry) carrying all six required keys — `artifact_id`, `source_data`, `transformation` (`{script, hash}` OR a precise manual-derivation pointer — vague values like "computed manually" are treated as untraceable), `caption_claim`, `supported_manuscript_claims` (each as claim text + optional locator, not a bare id, since the visualization agent can run before the draft's claim manifest exists), and `limitations` (present even when `[]`). `visualization_agent.md` emits the block in the Figure Package (new Step 6.6) and `integrity_verification_agent.md` Phase C gains **C3. Figure/Table Caption Fidelity** running at Stage 4.5: entry well-formedness (a malformed entry missing any of the six keys short-circuits to FAIL) plus four fidelity checks — trace completeness, caption-claim support (does the *interpretation* follow from data+transformation, with compound captions decomposed into atomic sub-claims using the #213 idea **as prose guidance only**, no `PARTIAL` verdict / `sub_claim_breakdown` imported; an entry takes its weakest sub-claim's verdict), bidirectional manuscript-claim linkage (each listed claim must reference the artifact and not overstate it, AND every substantive manuscript use of the artifact must be listed — incidental/structural mentions exempt), and limitation visibility (a known limitation must reach caption/Discussion/Limitations). **Severity is split, not blanket-advisory:** a caption that contradicts the data, an untraceable claim-bearing artifact, a missing/overstated manuscript link, or a dropped known limitation **FAIL (block)**; only uncertainty signals are advisory — an empty `limitations: []` emits a named `[FIGURE-LIMITATIONS-EMPTY]` note (never a silent pass) and a legacy figure with no trace surfaces a trace-unavailable note. At Stage 4.5, an updated Figure Package with no `figure_table_trace[]` (or one omitting an entry for a figure it contains) is a FAIL ("caption fidelity not verified"), so the check is not trivially skippable; a legacy figure with no Figure Package at all is the advisory case. C3 **inherits** the existing C1 data-cross-referencing layer (it does not re-render figures — that is VLM — or re-verify raw data — that is C1); its new coverage is interpretation and linkage. Adds `examples/figure_table_trace_example.md` (3-figure + 1-table ML ablation walkthrough covering a normal trace, a decomposed compound caption, and the empty-limitations advisory). Reference + agent-prompt/protocol text + doc example only; no schema, lint, or executable change.
- **Sub-claim decomposition before citation judgment — the citation-layer half of the §F.3.2 partial-evidence trap (#213).** The unified citation judge (`academic-pipeline/agents/claim_ref_alignment_audit_agent.md`) emitted exactly one verdict per citation, so a compound claim ("X rose AND the effect held across Y") whose source supported one sub-claim but not the other was collapsed to a single binary check and the unsupported sub-claim was silently lost — the largest correctness-error class documented in AI meta-review (Kim et al. 2026, arXiv:2605.20668v1 §F.3.2). The judge now runs a required **Step 0**: decompose the claim into atomic sub-claims and judge each independently before choosing the citation-level verdict. A new **prompt-layer `PARTIAL` verdict** (supports some sub-claims, not all; no active constraint violated) is normalized at Step 6 to `judgment=UNSUPPORTED, defect_stage=source_description`, routing the unsupported sub-claim through the same gate-refuse path a fully-unsupported claim takes so partial support is never accepted as full resolution. **Baseline correction:** the issue body proposed adding `PARTIAL` to the schema `judgment` enum; first-party reading showed that is the wrong baseline — `PARTIAL` (like the existing `VIOLATED`) lives at the prompt layer, NOT in the schema enum, so the 18 cross-field invariants and the allowed-(judgment, audit_status, defect_stage)-matrix stay untouched (the normalized triple was already in the matrix). The decomposition is persisted in a new additive optional schema field `sub_claim_breakdown[]` on `claim_audit_result` (pre-#213 entries validate unchanged); its **presence — not the defect_stage value — is the machine-readable partial-support signal** for downstream consumers. A new lint invariant **INV-19** pins the full normalization (breakdown present ⟹ `judgment=UNSUPPORTED` AND `defect_stage=source_description` AND true-partial: ≥2 items with ≥1 SUPPORTED AND ≥1 valid non-SUPPORTED sub_verdict), mutation-verified to discriminate. **Malformed `PARTIAL`** (breakdown absent / <2 items / not true-partial) takes the `audit_status=inconclusive [partial_breakdown_malformed]` path, never a silent bare `UNSUPPORTED`. Calibration gains **5 partial-support gold fixtures + a `partial_support` subset metric** (`scripts/claim_audit_calibration.py`): because partial fixtures carry `expected_judgment=UNSUPPORTED`, a judge that stops decomposing and emits bare `UNSUPPORTED` passes the aggregate FNR gate; the subset metric counts a partial fixture as passed ONLY when the judge emits `UNSUPPORTED` AND a well-formed true-partial breakdown, so the regression surfaces as `miss_rate > 0` while the aggregate stays green. The synthesis-layer sibling (#214) is out of scope. Schema + lint + judge-prompt + calibration + protocol-doc; the schema field and INV-19 are additive and backward-compatible.
- **Sub-claim inventory before consensus in the editorial synthesizer — the synthesis-layer half of the §F.3.2 partial-evidence trap (#214).** The synthesis-layer sibling of the citation-layer #213. The editorial synthesizer (`academic-paper-reviewer/agents/editorial_synthesizer_agent.md`) aggregated consensus over a whole weakness bundle, so a compound weakness whose sub-claims carried different reviewer support was collapsed to one verdict and the minority sub-claim was lost — the single largest correctness-error class in AI meta-review (Kim et al. 2026, arXiv:2605.20668v1 §F.3.2). **Prose-layer only:** the synthesizer emits a human-facing decision letter + revision roadmap, not machine-readable judge rows, so there is no deterministic consumer for a #213-style schema field / lint invariant / gold fixture — adding one would be unrequested abstraction. The `sub_claim` vocabulary aligns with #213; its architecture is not imported. **Step 1 splits** into `Step 1a — Reviewer Summary Matrix` (retained) + `Step 1b — Weakness Sub-Claim Inventory` keyed on `sub_claim_id` (only weakness bundles decompose; recommendation/confidence/counts stay in the 1a matrix). **Step 2 computes consensus per sub-claim** over an absolute denominator of the 4 non-DA reviewers (`position ∈ {raised, corroborated, not-mentioned, disputed}`; `not-mentioned` is silence, never opposition or agreement). **Mutually-exclusive dispositions with explicit precedence:** `conflict ≥ 1 → SPLIT` first, otherwise by `agree` count (`4→CONSENSUS-4`, `3→CONSENSUS-3`, `2→corroborated finding`, `1→single-reviewer finding`); every `(agree, conflict)` cell maps to exactly one disposition and `agree = 0` is unreachable by construction. `disputed` covers existence OR action/severity conflict, so reviewers agreeing a problem exists but recommending incompatible remedies route to SPLIT → EIC arbitration. A `Sub-Claim(s)` column is added to the roadmap tables in both the agent output format and the standalone `editorial_decision_template.md` so the decomposed granularity survives to the output boundary. DA-CRITICAL flow and the v3.6.2 sprint-contract arithmetic path are untouched; scoped to the general Synthesis Protocol only.
- **Concise output discipline + pressure-stable boundary reinforcement across the report-producing reviewers (#274).** A guidance-layer follow-up to the Claude Opus 4.8 system card §4.1.4, which documents two behavioral signals: refusals/responses trend longer and more over-caveated than 4.7, and a small number of multi-turn cases where a correct refusal was retracted under sustained pressure — both quality issues a user feels directly in a review tool. **Guidance layer only; no claim of having proven 4.8's runtime behavior.** A **concise output discipline** block is inlined (before `## Output Format`) into the report-producing reviewers — `domain` / `methodology` / `perspective` / `eic` / `devils_advocate` / `editorial_synthesizer` reviewers and `academic-paper/peer_reviewer`: state findings and verdicts directly, don't pad with repeated qualifiers; **concise explicitly does NOT mean under-caveated** — preserve every material uncertainty, cut only redundancy. A **"pressure is not evidence"** rule is added to the Devil's Advocate Anti-Sycophancy Rules and the editorial synthesizer's arbitration discipline: repeated pushback / authority appeals / bare softening requests do not change a finding. In the Devil's Advocate, this is bound to the existing numeric concession threshold (≥4 normally, 5/5 after a prior concession); in the editorial synthesizer's arbitration, a finding changes only on substantive new evidence or reasoning that addresses the arbitration basis (no numeric threshold lives there). Both are framed by evidence standard, not as an attack catalogue (public-repo safe). Every block carries an **epistemic-status line**: these are prompt-surface instructions; they cannot prove the model stays pressure-stable at runtime — that would need a separate non-deterministic behavioral eval. The issue's acceptance "confirm boundaries hold under 4.8 after pushback" is reframed as a *prompt-surface confirmation* (the instructions are present and explicit), not ticked by self-simulating a pushback dialogue (theater, not verification) and not pinnable by a deterministic CI test — mirroring the #272 guidance-layer ≠ runtime-enforcement discipline. No lint / mutation test (style guidance is not a contract invariant with a downstream consumer). Agent-prompt text only.
- **Retrieved-content instruction/data boundary stated as a standing principle (#367, guidance layer for #272).** Retrieved external content is *data*; imperative-looking text inside it is not auto-promoted to a user instruction. The authoritative statement lands as a canonical §2A in `shared/ground_truth_isolation_pattern.md` (marked distinct from the eval-leakage concern) and is inlined verbatim into the two highest-surface retrieval agents — `deep-research/source_verification_agent` and `bibliography_agent` — so the principle is present where a fetch happens. A new `scripts/check_instruction_data_boundary.py` lint guards against silent removal or anchor-preserving gutting (presence / verbatim-sync / section-anchoring / contiguous-backpoint), proven not-accept-all by an 11-mutation test plus a positive control; a strict-xfail pebble (`scripts/test_runtime_injection_boundary_xfail.py`) marks the unbuilt runtime defense so the deferred structural layer is not treated as done. **Commit-time documentation consistency only — no runtime gate, no injection-mitigation claim.** The originating trust-boundary issue (#272) stays open by design (the structural layer is deferred, bound to #134 Slice 3+). Lint + CI wiring (`spec-consistency.yml` + pytest manifest); no schema change.
- **Version-consistency lint extended to the README badge, docs forward-reference, and zh-TW heading invariants (#357, invariants 5-7).** `scripts/check_version_consistency.py` covered invariants 1-4 (CLAUDE.md table, suite version, pipeline tracking, plugin manifests); it now also enforces the three release-doc invariants previously caught only by manual checklist: **inv 5** — the README shields.io version badge tracks the suite version; **inv 6** — no `docs/*.md` cites a `vX.Y.Z` *above* the suite version (forward-reference guard); **inv 7** — version-bearing H2 headings stay in lockstep between `docs/<name>.md` and `docs/<name>.zh-TW.md` (plain headings may differ; only version tags pair, compared as multisets so a dropped one-of-a-pair heading is caught). Version-token regexes use a trailing negative lookahead so prerelease / 5-segment tokens (`v3.12.0-alpha`, `v3.11.1.2.3`) are dropped rather than partial-matched. Also removes the `docs/PERFORMANCE.md` cross-model onboarding section (en-only; aligns the en/zh-TW pair). TDD with 11 new test methods plus broadened aligned-fixture coverage, each invariant mutation-tested (stub to accept-all → matching test fails).
- **ARCHITECTURE.md component-version markers now policed by lint (#345, invariant-4 gap).** `scripts/check_spec_consistency.py` policed version markers in the README (×4 langs), `.claude/CLAUDE.md`, `MODE_REGISTRY.md`, and `SKILL.md` — but not `docs/ARCHITECTURE.md`, where six "current academic-pipeline component version" strings were missed by the v3.11.1 bump and caught only by a manual first-party sweep (#343/#344). A new `check_architecture_component_version()` parses the suite version from `.claude/CLAUDE.md` and asserts the six current-component markers equal it (the mermaid orchestrator node + the component table row + the four stage rows). It anchors on the `academic-pipeline <ver>` component pattern and never inspects the `timeline` block, so a stale current-component marker fails while a feature-history marker (`vX.Y.Z : <feature>`, which records *which* version shipped a gate and must not be bumped on a patch) is left alone — the distinction a naive `v3.x` grep would corrupt. The version regex captures the repo's full 4-component grammar (the suite shipped v3.9.4.2) with a hard right boundary so a 3-component marker can't partial-match inside a longer one, and the component/stage row scan is anchored to markdown table rows so a narrative provenance mention isn't wrongly policed. Wired into `spec-consistency.yml`; 7 tests (aligned passes / stale component fails / stale timeline marker does NOT fail / missing markers fail / 4-component edge cases).
- **Same-family / rubric-aware calibration epistemic note (#273, Claude Opus 4.8 system card §6.3.7 / §6.6.3).** An interpretive, doc-only follow-up to the system card's report of modest, partly-unverbalized **grader-awareness** signals (the model sometimes optimizes toward what a rubric appears to reward). ARS leans on rubric / gold-set judging (reviewer calibration, the citation-claim judge), so this affects how calibration numbers should be *read* — not what the suite does. **Zero detection / mitigation claim:** ARS does not and cannot detect or correct grader-awareness (the system card's own point is that it can be unverbalized); the only honest claim is interpretive. All changes land in `calibration_mode_protocol.md` "Failure cases this mode does NOT fix" plus a one-line pointer in `integrity_verification_agent.md`. An **umbrella "same-source evaluation risk" framing** names two forms — the existing *factual* form (same-source hallucination — fabricated references; canonical in the Anti-Hallucination Mandate, unchanged) and a new *behavioral* form (same-family rubric optimization), cross-referenced both ways; the integrity block's WebSearch counter-rules are explicitly scoped to the factual form only and are not edited to imply they mitigate rubric-aware judging. An **epistemic note** states that under same-family / rubric-aware judging the measured calibration error is a *possible under-estimate, not a ceiling*. A **cross-model positioning** clarification resolves the doc's own opt-in-vs-default-on tension (cross-model is opt-in "for best results" in ordinary reviewer / judge paths; calibration mode is the explicit default-on exception once invoked; absent cross-model is warn-and-continue, never a gate; the consent / privacy boundary for sending a manuscript to another provider is preserved). A **single-model paraphrase spot-check** is documented but honestly de-powered — reword the rubric and re-judge, stated plainly to reveal only *surface wording sensitivity*, unable to detect unverbalized grader-awareness, and no proof the judgment is correct (no score, no threshold, no gate). No schema, no lint, no gate, no calibration-threshold change.
- **Kong auto-research META closeout — negative scope + Tier D design lessons (#255, Kong et al. 2026).** Closes the Kong et al. auto-research survey META after every feature sub-issue (Tier A #256–#259, Tier B #260–#262, Tier C #263, Schema follow-ups #266/#268/#269) had merged; the two remaining closing conditions were documentation-only and defined the project's *negative scope*. `POSITIONING.md` gains a **"Rejected mechanisms (autonomous-research anti-patterns)"** section placed after "What this is not", enumerating the five autonomous mechanisms ARS does not do — end-to-end pipeline, idea-generation agent, Paper2X auto-generation, autonomous experiment execution, wet-lab automation API — each with a Kong anchor and, for the three that abut shipped features, an operationally-checkable CONSIDER-vs-REJECT line (idea-generation ≠ shipped #257 wording advisory; Paper2X auto-gen ≠ fidelity audit; autonomous experiment execution ≠ shipped #260 provenance intake). Two **Tier D design-lesson docs** land under the existing `docs/design/…lX…` convention (not a new directory): **L1** frames copilot-vs-auto-research as a research-state-authority review test ("does this let ARS create / select / execute / advance a research object of record without a scholar-authored seed or confirmation?"), and **L2** sharpens the advisory-vs-idea-generation line for research questions with a verb test, cross-linked from POSITIONING.md and from #257. Verification notes split a verifiable claim (no autonomous mechanism in first-party ARS today; #257 / #260 are advisory / provenance gates) from a design commitment (a recorded boundary and review criterion, not a runtime guarantee). Documentation only — no schema, agent, or lint change.

### Fixed

- **Originality weight reconciled to 20% across reviewer reference docs; rubric weights now lint-policed (#396).** `review_criteria_framework.md` stated Originality at 15% (plus a 7-dimension weighted formula and its own score-to-decision mapping) while the operative scoring source — `quality_rubrics.md`, which the peer-review report template instructs reviewers to score against — and `academic-paper/SKILL.md` rule 14 both say 20% with a 5-dimension aggregate. The framework doc no longer restates any number: its dimension headers drop the weight suffixes (qualitative level descriptors stay) and §4 defers weights, formula, and decision mapping to `quality_rubrics.md` by name, noting that Literature Integration and Significance & Impact are reviewer-specific optional dimensions outside the numerical aggregate. Recurrence is guarded by a new lint, `scripts/check_rubric_weight_consistency.py`: quality_rubrics dimension-header weights must match its own aggregation-formula terms, the weights must sum to 100%, SKILL.md rule 14 must agree, and the framework doc must not restate a weight (`Weight NN%` / `(NN%)` both fail). Mutation-verified on all four invariants; wired into `spec-consistency.yml` + the CI pytest manifest. Surfaced by codex during cross-model review of the 2026-06-10 researcher-blindspot audit (F-14).
- **Score-trajectory scale contradiction reconciled to 0-100 (#399, found during the #396 reconciliation).** `shared/handoff_schemas.md` declared score_trajectory scores as "1-5 scale" while every producer and consumer is 0-100: the report template scores 0-100 per `quality_rubrics.md`, and the canonical Early-Stopping Criterion is explicitly "delta < 3 points **on the 0-100 rubric**" (`academic-pipeline/SKILL.md`). The 1-5 comment is a pre-v1.4 fossil — the reviewer changelog (2026-03-08) records "Dimension Scores upgraded from optional 1-5 to required 0-100". Schema comments now say 0-100 (scale sourced from `quality_rubrics.md`; dimension *names* still from the framework doc), and the trajectory protocol's Stage 6 example — which mixed both scales in one table (1-5 scores, a "-0.2 within tolerance" verdict, and an "overall delta = 4" that matched neither) — is rebuilt on 0-100 with internally consistent deltas and verdicts. **Exposure note (per the #399 acceptance):** the thresholds themselves were never wrong — they were always defined against 0-100 in SKILL.md; the risk was a consumer reading only `handoff_schemas.md`, whose 1-5 trajectories would make regression detection (delta < -3) near-unreachable and early-stop (delta < 3) near-always-on. No evidence either check ran on 1-5 data (no real re-review artifact set exists post-v2.7; see #395). The reviewers' Confidence Score `[1-5]` is a deliberately separate axis and is unchanged.
- **Cross-model verifier now actually grounds its lookups, and an ungrounded result can no longer be laundered into `VERIFIED` (#346).** `shared/cross_model_verification.md` told the cross-model verifier to "search the web to confirm," but the shipped OpenAI / Gemini API call patterns wired in no web-search tool — so a copied example produced a verifier that was *told* to search but *could not*, answering from parametric memory and confidently returning `VERIFIED`. For a hallucinated-citation gate that is the worst failure (a false `VERIFIED` manufactures confidence), and it shares the generating model's exact failure mode — fluent-but-wrong from memory — for the one task (existence lookup) where grounding is the entire point. Two-part fix, both at the API-pattern layer: (1) the OpenAI pattern moves to the Responses API with the hosted `web_search` tool and the Gemini pattern enables the `google_search` grounding tool, so "search the web" is executable; (2) both patterns **gate the verdict text on proof a search ran** — they emit `NOT_SEARCHED` and discard the text when the API returns no grounding evidence (an OpenAI completed `web_search_call` item / a Gemini response whose `groundingMetadata` carries `webSearchQueries` *and* `groundingSupports` tying the verdict text to retrieved chunks), and a `VERIFIED` carrying no supporting source URL/DOI is downgraded to `NOT_SEARCHED`. The protocol moves from batched (≤5 refs/call) to **one grounded call per reference** so the grounding evidence maps 1:1 to each verdict (a single grounding trace on a 5-ref response proves *something* was searched, not that *each* reference was) — a deliberate cost-for-provenance trade (a 60-ref paper samples 30% capped at 15, so ~15 grounded integrity calls, documented in the cost table). `NOT_SEARCHED` is a new status distinct from a transport failure: a transport failure (non-2xx HTTP — `[CROSS-MODEL-ERROR]`) means "no cross-model opinion" (fall back to single-model); a `NOT_SEARCHED` (2xx, but no grounding evidence) means "an opinion we have decided not to trust," counted separately and surfaced for re-run or human review, never as agreement with a Claude `VERIFIED`. `academic-pipeline/agents/integrity_verification_agent.md` (the consumer) is aligned in lockstep: its behavior summary drops the stale "batches of 5", adds the `NOT_SEARCHED` / ungrounded handling, and splits transport-failure graceful-degradation from the `NOT_SEARCHED` path. Surfaced during the 2026-06 harness-retirement audit (#301) by a second-model cross-check pass and filed as a live correctness gap, not a harness-retirement item. Documentation + agent-prompt/protocol text only; no executable script or schema change.
- **Cross-model grounding guards are now behavior-tested, and a fail-open in the Gemini source extractor is closed (#349, follow-up to #346).** The #346 grounding guards shipped as bash/jq inside `shared/cross_model_verification.md` with no automated test — a future edit to the jq, or a provider response-shape change, could silently stop it failing closed (the exact silent-false-`VERIFIED` class the guard exists to prevent). The contract-bearing jq is extracted into canonical files under `scripts/cross_model_verification/` (5 filters: OpenAI search-guard / text / sources, Gemini grounded-guard / sources), the documented bash now loads them via `jq -f` instead of inlining, and `scripts/test_cross_model_verification_guards.py` runs each filter against synthetic fixtures (grounded → extracts supported sources; from-memory / non-grounded → `NOT_SEARCHED` with blank sources), with two mutation tests proving the fixtures discriminate a working guard from an accept-all / naive one. **Fail-open fix (malformed-response hardening):** the source extractors trusted the shape and types of the model's grounding metadata. Several malformed-but-well-formed-JSON responses could fabricate a source (defeating the blank-source downgrade and resurrecting a false `VERIFIED`) or crash jq: a negative `groundingChunkIndices` silently selected a chunk from the *end* of the array; a string index, a `groundingChunks`/`groundingSupports` arriving as a string/object instead of an array, a Gemini chunk `uri` or an OpenAI `url_citation.url` that is a number/bool/object — each either crashed or surfaced a non-URL value as a "source". The canonical filters now fail closed on all of these: indices must be in-range non-negative numbers (`select(type=="number" and . >= 0 and . < ($chunks|length))`), the grounded-guard requires `webSearchQueries`/`groundingSupports` to be non-empty *arrays* (not merely truthy `length`, which strings/objects also have), every container on each extraction path is array-normalized before it is iterated or indexed (OpenAI `output` → `content` → `annotations`; Gemini `candidates` → `groundingChunks` / `groundingSupports` / `groundingChunkIndices`) so a container arriving as an object can't have its values surfaced, and extracted URLs are filtered to non-empty strings — so any malformed response yields blank sources → `NOT_SEARCHED` rather than a fabricated or crashing result. A doc-sync lint (`scripts/check_cross_model_verification_sync.py`) pins that the doc keeps wiring every canonical filter via `jq -f` and retains the `NOT_SEARCHED` / `CROSS-MODEL-ERROR` branches (with `REQUIRED_FILTERS` cross-checked against the on-disk `.jq` set so a new filter can't escape the lint). Both the test and the lint are wired into the CI pytest manifest + `spec-consistency.yml`, which now also ensures `jq` is present on the runner. Documentation + test/lint/CI only; no agent-prompt or schema change.
- **Cross-model Gemini guard is rederived from the source extractor; malformed array elements no longer crash the OpenAI filters (#351, post-ship review of #349).** The post-squash review of #349 surfaced that the Gemini guard and the source extractor were two parallel jq programs asserted to agree, so each round found a new input where they diverged: a `groundingSupports` linking to no valid chunk (empty / negative / string / out-of-range / fractional index), a multi-candidate response where the guard's `any`-candidate scan passed on a grounded candidate while the extractor read the unsupported `candidate[0]`, or a non-string `uri`. In each, the guard passed while the extractor returned blank — and the blank-source downgrade only rescues `VERIFIED`, so an ungrounded `NOT_FOUND` / `MISMATCH` could be trusted as grounded. The fix is structural: `gemini_is_grounded.jq` now **embeds the exact same `candidate[0]` extraction `gemini_sources.jq` performs** and passes iff it yields ≥1 source AND a real `webSearchQueries` signal is present — so the safety invariant **guard-pass ⟹ at least one source extractable** holds by construction for every input shape, not by two predicates kept in sync by hand. (The guard is intentionally *stronger* than "has a source": a chunks-but-no-search response fails it.) Separately, `openai_text.jq` no longer crashes `join` on a non-string `text`, and all OpenAI filters type-check each array element as an object before reading `.type`, so a malformed element (`output: [5]`) is skipped rather than crashing. +17 behavior tests across the new invariant, multi-candidate / fractional / non-string-uri cases, and the array-element-crash paths (guards 27→44). Every hole and fix verified first-party.
- **Judge-verdict cache key partitioned by prompt version so a prompt revision invalidates stale entries (#361).** The judge-verdict cache key included `judge_model` but no prompt-version component, so a judge-prompt revision (e.g. #213's Step-0 sub-claim decomposition) did not invalidate stale entries — a verdict cached under the old prompt was still served until the TTL expired, silently bypassing the new prompt logic (a pre-existing cache-key design gap surfaced as P2#1 in the #355 post-squash review; affects every prompt revision, not just the decomposition path). `_cache_key` gains a `prompt_version` component kept separate from `judge_model` (independent axes), and invalidation keys on **`JUDGE_PROMPT_SHA256`** — the SHA-256 of the canonical judge-prompt section, the single source of truth — so any prompt edit changes the key and invalidates stale entries with no reliance on a human bumping a label (`JUDGE_PROMPT_VERSION` is a decoupled human-readable label for logs/diffs only). **Fail-CLOSED on unknown version:** when the caller declares the prompt version `None`, the pipeline binds a run-local component (`__unknown__:<audit_run_id>`) so a stale entry is never served across an unknown-version boundary (cross-run hits disabled; within-run dedup for repeated citations preserved). A CI backstop `scripts/check_judge_prompt_version.py` hashes the canonical section (between the `JUDGE-PROMPT-CANONICAL` markers) and fails if it drifts from the pinned hash, forcing a re-pin in the same change (wired into `spec-consistency.yml` + the pytest manifest). The agent-prompt contract and lint docstring — which described invalidation as keyed on the `JUDGE_PROMPT_VERSION` label while the pipeline already falls back to the SHA256 — are re-attributed to the SHA256 fingerprint so a downstream implementer following the contract can't re-open the bug. RED→GREEN + mutation-verified.
- **Judge-supplied rationale bounded on success-path rows + null rationale guarded (#360).** Judge-supplied rationale on success-path rows (`completed` + `constraint_violation`) is now bounded to the schema `maxLength=2000` via a shared length-budgeting choke point, and a non-string (null) rationale degrades to the default instead of aborting the audit run. RED→GREEN + mutation-verified.
- **Failure-rationale bounding + PARTIAL gold-fixture requirement — two #213 sub-claim-decomposition gaps (#359, #213 follow-up).** Two correctness gaps in the new PARTIAL machinery (neither reachable on pre-#213 inputs), surfaced by the #355 post-squash integration review and confirmed first-party. (1) The malformed-PARTIAL fallback could emit a schema-invalid row: the parse error embedded the offending breakdown's repr in `detail`, which became the fallback row's rationale and could exceed the `claim_audit_result` `maxLength=2000`. Fixed by bounding `detail` at a single choke point — a shared `_AuditInvocationError` base whose `__init__` clamps `detail` so the `"{fault_class}: {detail}"` rationale always fits (budgeted against the widest fault-class prefix); `JudgeInvocationError` / `RetrievalInvocationError` inherit it. (2) Calibration could silently skip the atomic-decomposition metric: `validate_gold_set` did not require an `expected_prompt_verdict=PARTIAL` fixture to carry non-empty `expected_sub_claims`, so `_breakdown_covers_expected` early-returned `True` and scored `miss_rate=0` for any generic breakdown; a new rule (e) rejects such a fixture at ingestion (fail-closed). RED→GREEN + mutation-verified for both.
- **Eval gold tuple 052 removed — a fabricated citation was mislabeled as a genuine unindexed paper (#250).** Gold tuple `052-valid-unindexed-regional-paper` was labeled `fabrication_intent: false` and its expert-verdict notes asserted it was a "GENUINE … real regional, non-English-indexed agronomy paper" (Sembiring & Ginting 2023, *Jurnal Penelitian Pertanian Regional*). First-party verification across all four resolvers (Crossref / OpenAlex / Semantic Scholar / arXiv) plus DOAJ, OpenAlex Sources, Crossref Journals, and general web search found no evidence the paper or the journal exists — a fabrication labeled as genuine, exactly the failure this repo exists to detect, and a direct violation of #250's closing condition (which requires a *first-party-verifiable* real-but-unindexed source). Functionally the tuple was redundant: the harness reduces pre-recorded `resolver_outcomes` (it does not live-query), and tuple 051 (the OQ-5 by-design false-negative, a no-identifier fabrication) already exercises the identical title-only-unmatched → unresolvable reducer path. Removes the tuple; `expected_outcomes.json` drops the 052 entry (51 entries); `manifest.yaml` `sample_n` 52→51 + drops the `valid_unindexed` distribution row; `check_evals_gold_set.py` drops `valid_unindexed` from `KIND_ENUM`; `citation_verification_summary.py` + test comments drop 052 references (expert-concordance 12→11, unresolvable support 7→6), realigning manifest/tests/summary with the gold-set README's already-described 51-tuple set. **#250 stays open** — the verified-real-but-unindexed canary is still genuinely unfilled; only a mislabeled synthetic proxy was removed.
- **ACL/EMNLP disclosure rows regrounded to the ACL Admin Wiki canonical source (#242).** The ACL disclosure row pointed at the 2023 conference blog (still live, HTTP 200) but its content had drifted from ACL's current Exec-approved policy. The Admin Wiki — which ARR / EMNLP 2026 link to for current paper-integrity guidance — places disclosure in the Acknowledgements section and graduates it by use type, contradicting the old row's "dedicated Use of AI Assistance subsection". First-party verification: the Admin Wiki returns HTTP 200 via browser navigation with the full "Guidelines for Generative Assistance in Authorship" section present (the 418 reported in #242 was a curl-UA challenge, not a stable block; the repo has no CI link-checker, so the humans-vs-tooling URL tension recorded in #242 does not apply). The ACL row's Source URL → Admin Wiki anchor (access date 2026-06-07) with summary / required phrasing / disclosure location / prohibited uses / authorship / notes regrounded from the first-party wiki text and graduated per its clauses a–f (language-only and short-form input not disclosed; literature search needs no special disclosure but normal citation-accuracy rules apply; low-novelty text and AI-suggested ideas disclosed); the EMNLP sibling row → the EMNLP 2026 Paper Integrity Policy page (which defers to ACL's guidelines) and is consolidated to "see ACL row"; `disclosure_mode_protocol.md` prose aligned to Acknowledgements. An independent cross-model faithfulness pass against the first-party pages corrected two fluent-wrongness overstatements (the literature-search no-disclosure bucket; an EMNLP "adopts wholesale" claim).
- **Stale Opus 4.7 primary-model strings retired + repro_lock run-time fields documented as placeholders (#347).** The 2026-06 harness-retirement audit (#301) found the agent prompts carry zero expired scaffolds, but two `shared/` files still pinned Opus 4.7 as the primary model after the 4.7→4.8 migration, and a `repro_lock` example hard-coded run-time snapshot values that readers copy verbatim. `shared/cross_model_verification.md`: primary model → Opus 4.8, with the primary "API ID" cell now reflecting that it is the inherited Claude Code session model rather than asserting an unverified `claude-opus-4-8` id string (cross-verifier ids `gpt-5.4*` / `gemini-3.1-pro-preview` confirmed current and left concrete), plus a note documenting why temperature is 0.1 (deterministic fact-check), closing the "undocumented sampling override" read. `shared/artifact_reproducibility_pattern.md`: the `repro_lock` example block uses placeholders for the three run-time snapshot fields (`ars_version`, `model.id`, `s2_api_protocol_version`) so a copy-paste records the actual run, not a stale literal (feature-introduction labels like `v3.3.5+` stay concrete). `examples/passport_with_repro_lock.yaml` left unchanged — a self-consistent historical snapshot, not a stale current-marker.

## [3.11.1] - 2026-06-06 — Post-ship correctness, hardening, and provenance fixes (#182 follow-up)

A patch release rolling up the post-ship advisory fixes surfaced after v3.11.0: a
cross-model consent-gate extension to the integrity + collaboration paths (#322), a
per-entry backfill parallelization (#138), and seven correctness/hardening fixes across
the citation-existence gate, the v3.10 policy layer, the eval harness, the domain
evidence profiles, and the #310 security-boundary edge cases (#323/#327/#328/#329/#331/#332/#333).
No new features and no breaking schema changes. One API note: the #332 `verify_citation`/
`verify_passport` signature gains required keyword-only parameters. This is a fix to a
contract-violating code path that first shipped in v3.11.0, not a deliberate signature
revision — the old signature emitted a schema-invalid `ref_slug: null`, so any v3.11.0
caller relying on it was already producing contract-invalid output. The only in-repo
callers (the CLI + the internal `verify_passport`→`verify_citation` call) are updated in
lockstep; see the #332 entry below for the full C-V4 rationale.

### Security

- **Cross-model consent gate extended to the integrity-verification and collaboration-depth paths (#322).** The explicit-consent gate that fronts every `ARS_CROSS_MODEL` upload — established for the two Devil's Advocate paths in #310 — now also fronts the two remaining agent paths that send user-derived material to an external provider on the env var alone: `integrity_verification_agent` (sampled citation/reference metadata) and `collaboration_depth_agent` (raw dialogue turns, which can carry the user's private reasoning and unpublished material). The gate is also added at the `pipeline_orchestrator_agent` re-dispatch point so the observer's agent-internal gate cannot be bypassed at the orchestration layer (defense in depth). All three mirror the #310 wording: no automatic send, explicit user consent identifying provider + model + content class, `[CROSS-MODEL-SKIPPED]` + single-model fallback when consent is declined, and a backpointer to `shared/cross_model_verification.md`. The `collaboration_depth_agent` advisory-only / never-blocks contract is preserved — the gate gates only the upload, never the observer's scoring role. Agent-prompt text only; no schema or script change.

### Performance

- **Parallelize the OpenAlex + Crossref backfill lookups per entry in `migrate_literature_corpus_to_v3_9_0.py` (#138).** When both `openalex_unmatched` and `crossref_unmatched` are missing for an entry, the two independent resolver calls (different hosts, per-instance throttle state, monotonic timing) now run concurrently via a 2-worker `ThreadPoolExecutor` instead of one-after-the-other, roughly halving per-entry network wait on a full backfill. Scope is deliberately bounded: only the two calls within one entry overlap — the corpus loop stays sequential (cross-entry parallelism is out of scope; the clients' per-instance throttle assumes serial use), all passport mutation / report bookkeeping / degradation logging stays single-threaded on the orchestrator thread, and an already-set field still never consults its client. A single missing field skips the pool and calls directly. Behavior is otherwise byte-equivalent to the sequential version, including the omit-on-`Unavailable` partial-degradation contract (now surfaced via `Future.result()`). Adds 2 tests (barrier-verified parallel dispatch + the previously-untested API-down degradation path); the 6 existing migration tests pass unchanged.

### Fixed

- **Two edge-case correctness fixes from the #310 post-merge review (#323, closes #324).** Post-merge `codex` review of #310 (security-boundary hardening) surfaced two issues #310's happy-path/crash-free tests did not catch, both verified first-party before fixing. (1) In `scripts/adapters/folder_scan.py`, a symlink escaping the input root wrote `reason: symlink_outside_input_root` to `rejection_log.yaml`, but that value is not in the `rejection_log.schema.json` `reason` enum — so the rejection log was contract-invalid exactly in the new symlink-rejection path. It now uses `other` + `detail` (schema-valid; the schema's `allOf` requires `detail` when `reason == other`). (2) In `scripts/bootstrap_timeline_yaml.py`, the lookup queried `…/works/{quote(doi)}` (encoded) but `source_locator` recorded `…/works/{doi}` (raw), so provenance named a URL that was never queried — affecting every DOI, not only reserved-character ones (`/` encodes to `%2F`). It now records the encoded DOI to match the queried URL. Tests strengthened to assert emitted content (the rejection log is `jsonschema.validate()`d; a new test pins `source_locator` to the encoded lookup URL), not just exit code.
- **Domain evidence profiles wired end-to-end (#327).** Three feature-logic gaps from the #259 post-ship review that survived on `main` because `check_domain_evidence_profile.py` only verified documentation-surface presence (C1–C7), never the control-flow bound, the consumer parse logic, or the date-gate semantics. **[P1]** Step 12 (the profile producer) was orphaned from the no-handoff flow directive (bounded at "Step 1-11"), so the profile silently never activated on the common path; `intake_agent.md`'s directive now affirmatively reaches Step 12 (new lint C8). **[P2]** The reserved-fallback row `unknown_user_defined (requested: <reserved>)` was misparsed as case (c), emitting a wrong `[PROFILE-UNRESOLVED]` malformed signal; the consumer now parses the effective token + parenthetical and emits a new `[PROFILE-RESERVED-FALLBACK]`, with (c) narrowed to genuinely unresolvable rows (new lint C9). **[P2]** The currency (time-range) node was not profile-aware, so a canonical humanities source admitted at the peer-review node was re-excluded at the currency node (INVARIANT 5 violation); the currency node gains a humanities admit branch (purely additive — union/loosen-only, continues through the universal relevance + methodology gates, never short-circuits to Include) (new lint C10). TDD with a RED mutation fixture per defect.
- **Eval-harness gates honor binding per-class thresholds and exclude non-measured tasks (#328).** Two correctness holes in the #263 eval-harness CI gates, invisible to the suite because no fixture exercised them. **[P1]** `scripts/_eval_threshold_gate.py` `failed_tasks()` inspected only `aggregate_metric.passed`, but manifests declare binding per-class thresholds distinct from the aggregate (e.g. citation_extraction aggregate `accuracy ≥ 0.90` **and** per_class `accuracy ≥ 0.85`); a PR regressing `citation_extraction.false.accuracy` below 0.85 while the aggregate stayed ≥ 0.90 passed the gate when it should block. `failed_tasks()` now also iterates `per_class`, keyed `<task>.<class>.<metric>`. **[P2]** `scripts/check_ranking_lift.py` `_flatten_report()` flattened any task carrying an `aggregate_metric` with no status filter, so a not-yet-landed task's placeholder `value: 0.0` entered the lift baseline as a real metric — once the task landed, its real value hit the zero-baseline branch and was spuriously flagged as a regression. Both consumers now share the same positive `status == "measured"` skip-guard so a future status (e.g. `"error"`) is excluded consistently. Adds `scripts/test__eval_threshold_gate.py` (11 cases) + 5 `_flatten_report` status-filter tests.
- **v3.10 policy layer: laundering guard wired to real entries + per-block terminal-marker validation (#329).** Two P2 enforcement/grammar gaps in the shipped v3.10 triangulation policy layer; the 45 policy-layer tests passed because each guard was only exercised in isolation, never wired to the surface it protects. **[P2]** `assert_venue_type_source_clean` (rejects a `venue_type_source` naming a lookup index under `trusted_source_declared`) had no production caller — the entry schema's own description promises *"enforced by check_v3_10_policy.py"* but nothing ran it over real entries, so a passport laundering a k=3-unmatched signal into a declared-trust signal passed both validators. It is now wired into `check_literature_corpus_schema.validate_passport`'s entry loop (a laundered source fails; a legitimate publisher/registry feed name still passes; string-guarded so a non-string `venue_type_source` surfaces as a clean schema error, not a `.strip()` traceback). **[P2]** `is_well_formed` accepted a terminal `TERMINAL-BLOCK` marker missing the mandatory `policy`/`reason`/`mode`/`policy_hash` fields; `_parse_inner` now keeps per-block metadata and `is_well_formed` validates each block independently plus the marker-level `policy_hash`, so a complete later block can no longer mask an earlier block's stripped metadata (C-V6(g) multi-policy co-emission handled correctly).
- **arXiv resolver no-ID skip + non-Atom 200 guard + miss-safe cache decode (#331).** Three post-ship defects in the #182 Delta 1+2 citation-integrity data layer (arXiv resolver + verification cache), all verified first-party; the 106 PR tests never exercised these paths. **[P2]** `resolve_arxiv_unmatched` ran a title search for citations with no `arxiv_id` (e.g. a DOI-keyed journal article) and returned `true` on a title miss — inflating triangulation `k` (k=3→k=4, rendering `CONTAMINATED-QUADRANGULATION-UNMATCHED` on a clean journal citation) plus a wasted ~3s request; it now skips the resolver when `arxiv_id` is absent, matching the spec's ID-gated `skipped` rule and the guard already in `verification_gate._run_arxiv`. **[P2]** A well-formed non-Atom 200 body (e.g. a proxy/CDN HTML error page) parsed cleanly and its empty entry list was cached as a real 90-day miss; `arxiv_client._get` now validates `root.tag == {atom}feed` and raises `ArxivUnavailable` (omit-on-degradation, not cached) on a non-feed root, while a genuine empty Atom feed still resolves to a miss. **[P3]** `VerificationCache.get`'s bare `json.loads` aborted verification on a corrupt/non-dict payload; it now treats `JSONDecodeError`/`TypeError`/non-dict as a miss (clean recompute), honoring the documented "malformed cache payload = miss" contract. Two tests that codified the buggy behavior were reversed.
- **`verification_gate` reads `ref_slug` from the prose join, not the corpus entry (#332).** `verify_citation`/`verify_passport` previously wrote `summary.ref_slug = entry.get("ref_slug")`, but `literature_corpus_entry.schema.json` is `additionalProperties: false` with no `ref_slug` property — so the normal (schema-valid) passport path emitted `ref_slug: null` and violated the summary contract (a required string). Two non-schema-conformant test fixtures masked it. `ref_slug` is now an explicit prose-sourced parameter parallel to `anchor`: `verify_citation(entry, clients, *, ref_slug, anchor=None, …)` and `verify_passport(passport, clients, *, ref_slug_by_key, anchors=None, …)`, with a `ValueError` on any invalid join — a missing key, or a present-but-empty/non-string slug (validated once at the `verify_citation` emission point via a shared `_is_valid_ref_slug` so the per-citation and passport layers can't drift; the passport layer re-checks only to name the offending `citation_key`) — rather than a contract-invalid summary. The standalone `verify_passport.py` CLI (which has no prose document) now refuses by default with a clear error and offers an explicit `--synthetic-ref-slug citation_key` diagnostic escape hatch instead of silently fabricating a slug. **API-stability note (C-V4):** these are new *required* keyword-only parameters. The spec's C-V4 freeze names v3.10.0, but #182 was specced-but-not-implemented in v3.10 (spec §0 amendment) and first shipped in the v3.11.0 minor release — so no v3.10.0 caller can depend on the old signature, and C-V4 itself permits a minor release to add required fields. The only in-repo callers (the CLI + the internal `verify_passport`→`verify_citation` call) are updated in lockstep.
- **`check_evals_gold_set` enforces `status`↔`queried_by` coherence via the shipped schema (#332).** The gold validator's flat `queried_by ∈ {id, title, null}` enum check under-enforced the conditional coherence the summary schema requires (a ran resolver must carry `id`/`title`, a skipped/unreachable one must carry `null`, and `queried_by` must be present). It now validates each `resolver_outcome` against `citation_verification_summary.schema.json`'s `$defs.resolver_outcome` — single source of truth, matching the existing I9b reduce-and-compare philosophy — and the now-dead `STATUS_ENUM`/`QUERIED_BY_ENUM` constants are removed. The shipped gold set already satisfies the stricter check.
- **Citation-existence advisory visibility + terminal-marker grammar reconciliation (#333).** Two P2 self-consistency issues in the #182 citation-existence gate, neither a gate hole (the formatter's generic `severity=HIGH-BLOCK` refusal catches the strict token regardless). **Item 1 (#342):** the spec was internally self-contradictory — C-V6(b) claimed an advisory `lookup_verified == false` is BOTH "byte-equivalent to v3.9.x" AND "co-emitted in the ref marker", impossible for a firing row, and a second advisory marker token has nowhere to go (the v3.7.3 grammar caps one advisory slot, already taken by contamination's `CONTAMINATED-*` suffix). Resolved by a third path: the marker stays byte-equivalent (no new suffix, no grammar churn), and the advisory's visibility is carried in the **output package** instead — `formatter_agent.md` now requires a mandatory `provenance_summary.md` `Citation Existence Advisories` section listing every advisory `false` row, and `provenance_summary.md` is added to the Output Package Files Delivered table so the carrier can't be dropped. Every "co-emitted in/alongside the advisory annotation" claim was removed from spec §0 / C-V6(b)/(c)/(e) / Rule 12 (the contamination strict clause, which legitimately does co-emit a suffix, is untouched); new C-V6(b) lint in `check_v3_10_policy.py` + 3 mutation tests. **Item 2 (#338):** the canonical "Two marker grammar shapes" terminal enumeration in `pipeline_orchestrator_agent.md` listed `policy=<contamination_triangulation|temporal_integrity>`, omitting `citation_existence` even though the finalizer prose just below emits `policy=citation_existence` tokens; the enumeration is extended and the `mode=` clause reconciled per-policy (`citation_existence` is `strict`-only), + 2 parser fixtures.

## [3.11.0] - 2026-06-04 — Deterministic citation verification gate (#182)

The v3.11.0 minor release ships **#182 — a deterministic citation-existence verification gate**
that runs independently of LLM peer review. It cross-checks every cited reference against up to
four bibliographic indexes (Semantic Scholar + OpenAlex + Crossref + the new arXiv resolver) and
surfaces a per-citation `lookup_verified` status, so a fabricated citation with a provably-bogus
DOI/arXiv ID is caught by deterministic lookup rather than by hoping a reviewer agent notices.
The gate **inherits the v3.10 `terminal_policies` opt-in model** — default advisory, opt-in
`strict` — rather than introducing a second hard-block philosophy: detection always runs and
populates the summary, but a `lookup_verified == false` row is terminal only under
`terminal_policies.citation_existence == strict`. **Default behavior is non-blocking** (advisory,
`/ars-mark-read`-acknowledgeable); a user must opt into `strict` to make existence-failure
terminal. The `false` definition is deliberately **narrowed to ID-keyed unmatched** (an exact
DOI/arXiv lookup that provably fails), so a legitimately-unindexed humanities / non-English /
regional citation with only a title-unmatched stays `unresolvable` and never blocks (C-V6(a); an
acknowledged precision-over-recall tradeoff documented in the spec, mirroring `strict_articles_only`).

**Five delta items (#182):**

- **Delta 1 — arXiv API resolver + four-index contamination rendering.** New `scripts/arxiv_client.py`
  verifies citation existence against `export.arxiv.org` (metadata + existence; no API key, no
  polite-pool email — built-in rate-limit pacing per arXiv ToU; accepts both old-style
  `hep-th/9711200` and new-style `2605.07723` IDs). `scripts/contamination_signals.py` extends the
  v3.9.0 cross-index triangulation advisory matrix from three indexes (k=0..3) to four (k=0..4) with
  an `arxiv_unmatched` signal, and the orchestrator finalizer + formatter render the four new
  advisory suffixes (`CONTAMINATED-ARXIV-UNMATCHED` at the k=1/k_max=1 arxiv-only carve-out;
  `CONTAMINATED-QUADRANGULATION-UNMATCHED` at k=4/k_max=4; plus their two `PREPRINT` compositions).
  All advisory — the terminal gate / refusal list is unchanged (R-L3-2-E). `arxiv_unmatched` field
  added to `literature_corpus_entry.schema.json`.
- **Delta 2 — persistent verification cache.** New `scripts/verification_cache.py` — a local SQLite
  store (`~/.cache/ars/verification.db`, override via `ARS_VERIFICATION_CACHE_PATH`; WAL mode;
  90-day TTL) keyed by `(citation_key, resolver_name, query_form)`, so the same paper cited across
  drafts is verified once. Each resolver entry point (crossref / openalex / S2 / arxiv) gains an
  optional `cache` parameter. New `/ars-cache-invalidate <citation_key>` command removes every
  cached row for a key (idempotent no-op when absent).
- **Delta 3 / C-V6 — citation-existence terminal policy.** New `terminal_policies` key
  `citation_existence` (closed enum `{advisory, strict}`, per-key absence = advisory) in
  `terminal_policies.schema.json`, alongside `contamination_triangulation`. This replaces the
  original Delta-3 `ARS_CLAIM_AUDIT` default-flip as the gate's on/off control. The finalizer is the
  sole policy evaluator; `formatter_agent.md` rule 12 refuses on a `lookup_verified == false` row
  **only under `strict`**, co-emitting `[UNVERIFIED CITATION — lookup_verified=false: ...]` alongside
  the advisory annotation. `HIGH-BLOCK` is terminal — not `/ars-mark-read`-clearable. Manual entries
  structurally exempt.
- **Delta 4 — unified per-citation status surface.** New
  `shared/contracts/passport/citation_verification_summary.schema.json` +
  `scripts/citation_verification_summary.py` write a `lookup_verified` (enum `{true, false,
  unresolvable}`) + `anchor_present` + `resolver_outcomes` (per-resolver `{matched, unmatched,
  unreachable, skipped}`) row per citation. The classification is anti-fabrication-biased (one
  ID-keyed `unmatched` is positive evidence of non-existence; a single transient outage does not
  cancel it) and the `false` form is narrowed to ID-keyed unmatched per C-V6(a).
- **Delta 5 — standalone `verification_gate` API.** New `scripts/verification_gate/__init__.py`
  extracts the gate logic into a callable API composing the four resolvers + the unified summary
  writer (a second caller of the same lower-layer infrastructure as the v3.8 audit, not a
  duplicate). New `scripts/verify_passport.py` CLI runs the gate over a Material Passport
  standalone.

**Lint + CI:**

- `scripts/check_v3_9_0_triangulation.py` (the canonical cross-version contamination-suffix oracle)
  rule 1 upgraded from subsection token-presence to a **matrix-row oracle**: each Delta-1 token must
  sit on the finalizer suffix-table row carrying its exact `(k, k_max)` cell, so deleting or
  mistokening an operational row fails even when the same token survives in surrounding prose. The
  formatter pass-through allowlist set-equality oracle extends 9 → 13 tokens.
- `scripts/_ci_pytest_manifest.toml` backfills 5 data-layer test entries (citation-verification-summary
  / verification-gate / arxiv-client / verification-cache / verify-passport-cli) that shipped with
  the data layer but were not wired into the manifest runner at the time.

Spec: `docs/design/2026-05-21-v3.10-182-promote-citation-gate-spec.md` (§0 v3.11 amendment +
INVARIANT C-V6).

## [3.10.0] - 2026-06-01 — Triangulation policy layer, Kong et al. survey adoptions, eval harness, scoped-write guard

The v3.10.0 minor release bundles the opt-in contamination-triangulation **terminal policy
layer** (#127 PR-B — default behavior byte-equivalent to v3.9.0), several **Kong et al. 2026
survey adoptions** (Rebuttal Commitment Ledger #256/#266/#268/#269, discipline-relative
domain evidence profiles #259), the **v3.10 measurement infrastructure** (generalized eval
gold set + ranking-lift gate, #184), the **#134 scoped-write guard MVP** (a deterministic
`PreToolUse` hook fencing the 23 single-phase agents to their own phase directory; all Bash
denied for those agents), the `/ars-mark-read` plugin commands (#190) + a broken-on-arrival
fix (#195), a Simplified-Chinese README (#185), and CI hardening (#156/#155). Default
*citation-policy* behavior is byte-equivalent to v3.9.0 unless a user opts into a strict
mode (#127). The one default-on behavior change is #134's `PreToolUse` write-scope guard:
the 23 single-phase agents are now fenced to their own phase directory and denied Bash —
this constrains those subagents, not the user-facing skill outputs.

**v3.10 triangulation policy layer (#127 PR-B — opt-in terminal modes, default behavior byte-equivalent to v3.9.0):**

- **#127 PR-B — terminal policy layer.** Ships the contamination-triangulation policy layer deferred by v3.9.0 (#102): opt-in `strict` modes that promote the advisory k=3 triangulation signal to a non-acknowledgeable terminal `HIGH-BLOCK` at the citation-emission boundary. **Default behavior is byte-equivalent to v3.9.0** — an absent or all-`advisory` `terminal_policies` block changes nothing (Invariant 7). Built on PR-A's canonical firm-rules + sync-lint base.
  - **Schema.** New passport-level `shared/contracts/passport/terminal_policies.schema.json` (standalone, NOT inside the entry schema — Invariant 11): `contamination_triangulation` ∈ {`advisory`, `strict`, `strict_articles_only`}; `temporal_integrity` accepts **only** `advisory` (forward-reserved namespace — a schema-accepted temporal `strict` with no wired behavior would be a false-safety bug, Invariant 3). `literature_corpus_entry.schema.json` gains `venue_type` (closed enum incl. explicit `unknown`), `venue_type_provenance` (closed enum; the API-`_inferred` values are deliberately absent per R-L3-2-D), and `venue_type_source` (required iff `trusted_source_declared`). Pair dependencies: type ⟺ provenance (bidirectional); `venue_type == unknown ⟹ provenance == unknown` (one-way — a known type may carry `unknown` provenance, no data loss). All adapter-declared only; never inferred from free-form `venue`. `check_literature_corpus_schema.py` extended to validate a passport-level `terminal_policies` block before iterating entries.
  - **Finalizer (sole policy evaluator).** `pipeline_orchestrator_agent.md` gains a `## Cite-Time Provenance Finalizer — v3.10 extension` section. Under a non-advisory passport it stamps `policy_hash=<slug>` on every ref marker (a fully-encoded human-readable canonical token of the non-advisory `terminal_policies` keys — sorted `key.value` join — so two distinct configs never collide). Under an all-advisory passport NO stamp is emitted: the marker is the bare v3.9.0 shape (byte-equivalent, Invariant 7) — the absence of a stamp is the advisory signal. Under `strict`, a k=3 ref co-emits a `TERMINAL-BLOCK severity=HIGH-BLOCK policy=... reason=... mode=... policy_hash=...` token ALONGSIDE (not replacing) its advisory `CONTAMINATED-*` suffix, so the "why" survives. `strict_articles_only` is a deliberate PRECISION mode — k=3 promotes only when DOI present ∧ `venue_type ∈ {journal-article, conference-paper}` ∧ declared provenance; a DOI-less or unknown-venue journal article stays advisory by design (humanities / non-English / regional coverage gap). Audit trail gains a `terminal_blocked[]` bucket; aggregate counts dedupe by ref slug across advisory + terminal buckets (non-additive). Manual-entry exemption preserved (k=3 structurally unreachable). `HIGH-BLOCK` is terminal — `/ars-mark-read` does NOT clear it.
  - **Formatter (STAMP-ONLY two-gate).** `formatter_agent.md` gains refusal rule 11 (generic `severity=HIGH-BLOCK` inside a `<!--ref:...-->`, NOT a per-subtype list) plus a `## Cite-Time Terminal Policy Gate (v3.10)` section. Two ordered gates, never short-circuited: Gate 1 freshness (stamp mismatch / missing-stamp-under-non-advisory → `[STALE-POLICY-EVALUATION]`; missing-stamp-under-advisory passes, Invariant 7), Gate 2 HIGH-BLOCK refusal applied to every gate-1-passing marker (a stripped-stamp marker still carrying `TERMINAL-BLOCK` is still refused). The formatter never re-evaluates `strict_articles_only` logic (Invariant 13 — the finalizer is the sole evaluator). A bare-prose `HIGH-BLOCK` outside any ref marker never refuses (Invariant 12). v3.9.0 advisory pass-through allowlist unchanged.
  - **Firm rule.** R-L3-2-A reworded in `firm_rules.md` to the broad default-advisory + opt-in-strict form (covering contamination AND the forward-reserved temporal namespace; the wording explicitly states no temporal strict path exists yet, no over-promise). Contamination mirrors stay intentionally by-ID references (not full-block copies); the wording is single-sourced in the canonical block. `check_firm_rules_sync.py` gains a contradiction guard scoped to the R-L3-2-A reference sentence in each contamination-context file (rejects unqualified "advisory only / never block" claims now that strict can block) — deliberately NOT scanning the whole file, so the Collaboration Depth Observer's legitimate "never blocks" wording is not false-flagged.
  - **Migration + adapters.** `scripts/migrate_literature_corpus_to_v3_10.py` seeds passport-level `terminal_policies` (deep-merge — only absent keys, idempotent, dry-run; never backfills `venue_type` from free-form `venue`; clear error on a non-mapping `terminal_policies`; pre-v3.9.0 passports reported out-of-scope, not silently skipped). The three reference adapters (`folder_scan` / `zotero` / `obsidian`) now declare `venue_type` + `venue_type_provenance` (Zotero item type → `adapter_declared`; folder_scan → `unknown`/`unknown`; obsidian honors a frontmatter `venue_type` as `user_declared`, else `unknown`/`unknown`).
  - **Lint + CI.** New `scripts/check_v3_10_policy.py` (runs ALONGSIDE `check_v3_9_0_triangulation.py`, not a rename) covers the schema fields, the `_inferred`-rejection, the pair dependencies, the trusted_source laundering guard, the standalone schema home, the marker grammar (with a reusable parser + the five required fixtures: terminal co-emit / non-terminal advisory / non-terminal clean / legacy-no-stamp / bare-prose-no-refuse), the generic rule-11 shape, the formatter STAMP-ONLY two-gate, and the closed enums. Wired into `spec-consistency.yml` + `_ci_pytest_manifest.toml`. Spec: `docs/design/2026-05-31-ars-v3.10-policy-layer-rescope-spec.md`.

### Added
- **#134 Slice 1 — scoped-write guard MVP (the Active Conductor rescope).** New `PreToolUse` hook `scripts/ars_write_scope_guard.py` fences the 23 single-phase (Bucket A) subagents to their own phase directory: for `Write`/`Edit`/`MultiEdit` it normalizes the single top-level `file_path` (`realpath`, so `..`/symlink traversal resolves in true filesystem order), denies workspace escapes, unconditionally protects the enforcement surface (`hooks.json`, the hook/manifest/lint, agent definition files, `.claude/CLAUDE.md`), then enforces the agent's `allowed_write_globs` with a segment-aware iterative glob matcher (`*` never crosses `/`; `dir/**` is descendants-only; no recursion-limit crash on deep paths). **All Bash is denied for a Bucket A agent** — it uses the Grep/Glob tools to search and the structured editing tools to write. (The spec's "best-effort literal-target Bash" was taken to its sound conclusion: neither "this Bash writes a file" nor "this Bash is read-only" can be decided reliably from a command string without a sandbox, so all-deny is the only zero-fail-open Bash policy; spec carries an Implementation-outcome note + aligned §3.2/§3.3 wording.) Backed by `scripts/ars_phase_scope_manifest.json` (machine-readable scope for the 23 agents) and the fail-open guard lint `scripts/check_v3_10_134_write_scope.py` (three-way name cross-check: classification roster == manifest keys == on-disk frontmatter names, + filesystem exhaustiveness at any nesting depth, so rename/typo/new-agent drift can't silently fail the hook open). `hooks.json` PreToolUse wiring + CI steps (lint + hooks.json wiring assertion) + pytest manifest entries; TDD throughout with lint mutation tests. The structured-tool determinism is the load-bearing win; the Bash deny closes the direct-shell-write path for fenced agents entirely. Slices 2-5 (write-provenance ledger, task envelopes, return contracts, persistent conductor) remain forward-scope. Spec: `docs/design/2026-06-01-ars-134-conductor-rescope-deterministic-write-guard-spec.md`. Closes #134.
- Kong A4 (#259): Discipline-relative domain evidence profiles. New `academic-paper/references/domain_evidence_profiles.md` defines 4 ship-ready profiles (`cs_ml`, `general_social_science`, `humanities_interpretive`, `unknown_user_defined`) + 5 reserved. `intake_agent` Step 12 emits a scholar-selected `Domain Evidence Profile` PCR row (never auto-selected; reserved selections fall back to neutral with a surfaced advisory). `literature_strategist_agent` resolves the row and applies **loosen-only** gate + upstream-filter changes — monotonic admit-only, and profile-admitted sources still flow through the universal relevance + methodology gates. New `scripts/check_domain_evidence_profile.py` (C1–C7 documentation-surface lint, including a SHA-256 pin of the `source_quality_hierarchy.md` Field-Specific Adjustments block) + mutation suite, wired into `spec-consistency.yml` + the pytest manifest. Advisory only. Closes Kong et al. 2026 §7.4.6 domain-evidence-standards gap.
- Kong A1 (#256): Schema 11 R&R Traceability Matrix gains `commitment_extracted` / `fulfillment_status` / `unfulfilled_rationale` optional fields. `revision_coach_agent` Step 3.5 extracts commitments; `re_review_mode_protocol` step 5 verifies + surfaces `COMMITMENT_GAP` advisory. Worked example at `academic-paper/examples/commitment_ledger_example.md`. Calibration seed at `evals/calibration/commitment_ledger_seed.yaml` (10 cases). Advisory only — author retains final responsibility. Closes Kong et al. 2026 §7.4.3 commitment-fulfillment gap.
- Kong A1 follow-up (#269): Schema 11 `required_evidence_type` enum widened from 7 to 9 values, adding `prose_edit` and `other`. `prose_edit` is a seventh **manuscript-evidence** type for sentence-/paragraph-level changes too granular to bucket structurally (typo fixes, terminology clarifications, equation formatting, citation-style corrections); it verifies at `revision_location` like the other manuscript types. `other` mirrors the existing `commitment_type` escape hatch for genuinely uncategorizable evidence and triggers a new soft `EVIDENCE_TYPE_UNSPECIFIED` advisory at re-review (orthogonal to `COMMITMENT_GAP`; fires whenever `required_evidence_type == other`, regardless of fulfillment status). The prior 7-value closed set forced typo-level comments into wrong buckets (`methods_paragraph`) or out of the ledger entirely, violating the every-comment extraction rule. Synced across `shared/handoff_schemas.md` Schema 11, `revision_coach_agent` Step 3.5, `re_review_mode_protocol` Commitment Ledger Verification, and `revision_tracking_template.md`; worked example and calibration seed (now 12 cases, +E1/E2) extended. Advisory only. Surfaced by Gemini R3 review of PR #264, Finding 3. Closes #269.
- Kong A1 follow-up (#268): Schema 11 Commitment Ledger refactored from three index-aligned **parallel lists** (`commitment_extracted` objects + top-level `fulfillment_status[]` + `unfulfilled_rationale[]`) to a **nested-object** shape — `fulfillment_status` and `unfulfilled_rationale` now nest INSIDE each `commitment_extracted` object. This makes length-mismatch / index-desynchronization structurally impossible, closing the Gemini R3 (PR #264) Finding 1 fragility where a dropped Markdown `<br>` or numbering error silently mispaired a status with the wrong commitment and produced a false `COMMITMENT_GAP` advisory. **REPLACE, not coexist** (spec §2): the parallel-list shape is removed entirely — no executable consumer, lint, or fixture carried it (the #263 calibration harness is unshipped; the seed is a non-runnable seed), so coexistence would only preserve the failure mode. Lifecycle fields are absent at extraction time (`revision_coach_agent` Step 3.5) and appended per-object during revision execution; the old `unfulfilled_rationale: ""` placeholder for fulfilled commitments is dropped (omitted, not empty-string). The equal-length validation invariant is retired (now structurally impossible); a legacy-normalization note instructs zipping any pre-#268 top-level arrays onto the nested objects before re-review. Synced across `shared/handoff_schemas.md` Schema 11 (incl. the #266 `residual_action` coherence prose, reworded from `unfulfilled_rationale[i]` index notation to object-field notation), `revision_coach_agent` Step 3.5, `re_review_mode_protocol` Commitment Ledger Verification, `revision_tracking_template.md` (three fragile `<br>`-separated columns collapsed into one per-commitment nested YAML ledger), worked example, and the 12-case calibration seed. `author_fulfillment_claim` (Gemini's promised-vs-claimed-vs-verified split) deferred — not required for the structural fix (spec §2). New `scripts/check_268_nested_commitment_ledger.py` (N1-N5 + N3b: seed extraction-field presence, no retired parallel-list keys, per-commitment lifecycle coherence via a `_blank_rationale` helper that treats missing/null/whitespace uniformly, case-level `expected_commitment_gap` oracle coherence with a real-boolean guard, no surviving index notation) + 18 mutation tests, wired into `spec-consistency.yml` + the pytest manifest. Advisory semantics unchanged. Surfaced by Gemini R3 review of PR #264, Finding 1. Spec: `docs/design/2026-05-31-ars-268-schema11-nested-commitment-ledger-spec.md`. Closes #268.
- Kong A1 follow-up (#266): Schema 11 `residual_action` (concern-level) vs `unfulfilled_rationale` (per-commitment) coherence. Documented their semantic relationship (different granularity and tense — `unfulfilled_rationale[i]` is backward-looking and per-commitment, `residual_action` is forward-looking and concern-level, so a row may carry both without redundancy or contradiction), the multi-commitment single-string shape convention (`residual_action` stays one concern-level string, not expanded into a list), and a `re_review_mode_protocol` note that a populated `residual_action` alongside some `fulfillment_status[i] == fulfilled` is not a contradiction, cross-referencing the `shared/handoff_schemas.md` Schema 11 convention. Doc-only; advisory semantics unchanged. Closes #266.

**Bug fixes (no version bump — corrects a broken-on-arrival behavior from #190):**

- **#195 — `/ars-mark-read` crashed on real YAML passports.** `scripts/ars_mark_read.py:_load_corpus_keys` used `json.load()` to read the Material Passport, but every adapter (folder_scan / zotero / obsidian) and every other ARS tool produces / consumes `passport.yaml`. The existing 11-test fixture in `scripts/test_ars_mark_read.py` wrote JSON-formatted passports, so the suite was green while real-world `/ars-mark-read smith2024 --passport-path ./passport.yaml` exited with `json.JSONDecodeError` before reaching citation-key validation. Two new TDD tests pin the adapter-format expectation (YAML happy path + YAML invalid-key hard error); `_write_passport` helper switched to `yaml.safe_dump`. Companion P2 also closed: existing-but-unwritable read-log file now surfaces the canonical `[ARS-MARK-READ ERROR: ...]` fail-fast rather than a bare `PermissionError` traceback, via an extra `os.access(log_path, os.W_OK)` check after the parent-W_OK gate. 14 ars_mark_read tests pass (was 11), full suite 1623 / 3 skipped. Surfaced by post-squash codex review of PR #191 (issue #192).

**Plugin commands (prep for v3.10 — no behavior change to existing skills):**

- **#190 — `/ars-mark-read` + `/ars-unmark-read` plugin commands.** v3.6.8 spec §3.6 + Step 7 (round-2 R2-002, round-5 R5-003 amends) designed these commands as the user-facing affordance for the human-read signal, but the command surface itself was never shipped — `commands/` carried only the 10 `/ars-<mode>` skill triggers. New `scripts/ars_mark_read.py` deterministic CLI implements the four §3.6 R5-003 fail-fast modes (no active passport / passport not found / parent unreadable / read-log unwritable), the §3.6 firm-rule-2 hard error on invalid `citation_key`, batch-level all-or-nothing semantics (any invalid key rejects the whole batch), and the §3.6 firm-rule-3 append-only write to `<passport-stem>_human_read_log.yaml` next to the active Material Passport. `/ars-unmark-read` writes `rescinded_at: <ISO 8601>` to the matching entry, never deletes. Two new thin markdown command files (`commands/ars-mark-read.md`, `commands/ars-unmark-read.md`) invoke the CLI via Bash; both declare `model: sonnet` routing per `feedback_no_haiku.md`. New `scripts/check_v3_6_8_mark_read_commands.py` CI lint per spec Step 7 acceptance: 2 commands exist, carry the `literature_corpus[]` validation reference, reference the `human_read_log.yaml` peer-file write target (NOT entry frontmatter, per §3.1 firm rule 3), and declare `model: sonnet`. 11 unit tests for the CLI + 6 unit tests for the lint. `/ars-list-read` and `commands/ars-mark-read.zh-TW.md` were spec-marked optional and remain deferred. Closes #190.

**v3.10 measurement infrastructure (prep for v3.10 — no behavior change to existing skills):**

- **#184 Phase 1a — citation-extraction gold subset.** New top-level `evals/` directory holds v3.10 generalized gold-set corpora for `verification_gate.verify_citation` measurement targets. Ships `evals/gold/citation_extraction/` with 50 hand-curated tuples (all populated in this PR) + `manifest.yaml` + `expected_outcomes.json`. v3.10.0 binding thresholds: aggregate `accuracy >= 0.90` across 50 tuples, per-class `accuracy >= 0.85` for each of `true` / `false` / `unresolvable` (changing requires spec amendment per #184 §3.1.1 / E-V2). Distribution: 20 valid_doi + 10 valid_arxiv + 5 manual_exempt + 15 fabricated (= 50). The original `valid_unresolvable` source class was removed as unbuildable — no stable first-party-verifiable real-but-unmatched citation exists under current index coverage; tuples 031-040 were reassigned to `fabricated`; coverage gap tracked in #250. Tuple shape (locked per codex consult Q1-Q5): self-contained `corpus_entry` mirroring `literature_corpus_entry`, `arxiv_id` as tuple-level field (forward-looking — see #234 for #182 implementation alignment), `human_expert_verdict` optional (10/50 = 20% per Delta 5), `fabrication_intent` boolean enforced on fabricated tuples. New `scripts/check_evals_gold_set.py` enforces 9 invariants (I1 set equality / I2 tuple_id ↔ filename / I3 kind distribution / I4 no-dup-JSON-keys / I5 label ↔ kind / I6 arxiv_id placement / I7 fabrication_intent marker / I9 resolver_outcomes shape / I10 corpus_entry schema) via 17 mutation tests on a 3-tuple clean fixture. CI step wired into `.github/workflows/spec-consistency.yml`. Spec: `docs/design/2026-05-21-v3.10-184-extend-eval-harness-spec.md`.
- **#184 Phase 1b — eval harness + ranking-lift gate.** New `scripts/run_evals.py` multi-task harness (`python -m scripts.run_evals [--task <name>] [--baseline <path>] [--compare <path>] [--output <report.json>]`): discovers every `evals/gold/<task>/manifest.yaml`, measures each task, and emits a report shaped by the new `shared/evals_lift_report.schema.json` (required `harness_version` / `run_id` / `gold_set_version` / `per_task[]` / `caveats[]` with the v3.8 honesty-disclosure `minItems:1` convention). For `citation_extraction` the harness computes the predicted `lookup_verified` 3-class enum itself from each tuple's `resolver_outcomes.*.status` via the #182 Delta 4 reducer (`verification_gate.verify_citation` has not shipped — reconcile when it does); the metric is symmetric 3-class accuracy, `unresolvable` is never collapsed into `false`. For `rq_framing_patterns` it dispatches to the existing `scripts/check_rq_framing_patterns.py` runner and adapts its FNR / FPR / balanced-accuracy output into the per-task lift shape. `--baseline` + `--compare` produce a side-by-side report carrying `lift_pre` / `lift_post`; `expert_concordance` is emitted per class over the 10 `human_expert_verdict`-labeled tuples (advisory, never gates per E-V3). Missing entrypoint module / Phase-2 gold set yields a `pending`/`skipped` notice, never a traceback. New `scripts/check_ranking_lift.py` lift gate: pure `compute_signed_lift(baseline, compare, direction)` (higher-is-better `(compare-baseline)/|baseline|`, lower-is-better numerator inverted, zero-baseline `+inf`/`-inf`); blocks on any `signed_lift < -0.05` or zero-baseline change unless the PR body carries `[ranking-regression-acknowledged]` + an OPEN issue URL and the declared `Affected metric: <task>.<class>.<metric>` matches the observed change (E-V4); OPEN-issue check via a monkeypatchable `_issue_is_open` seam (never networks in tests). New CI workflow `.github/workflows/eval-harness.yml` (Delta 3 path filter; concurrency group includes `github.event_name`; OQ-3 skip-guard for absent Phase-2 gold sets; deterministic `[eval-regression-acknowledged]` + OPEN-issue PR-body gate) and net-new `.github/pull_request_template.md` Eval-impact section. Tests: `scripts/test_run_evals.py`, `scripts/test_check_ranking_lift.py`, `scripts/test_evals_citation_extraction.py`, `scripts/test_evals_lift_report_schema.py` (incl. trivial-accept-all schema mutation). Spec: `docs/design/2026-05-21-v3.10-184-extend-eval-harness-spec.md`.

**Localization (no version bump — no behavior change to skills):**

- **#185 — Simplified Chinese README.** New `README.zh-CN.md` (630 lines, mirroring `README.zh-TW.md` structure) translated by external contributor [@xpfo-go](https://github.com/xpfo-go) ([PR #181](https://github.com/Imbad0202/academic-research-skills/pull/181)). Language switcher updated across the four READMEs (en / zh-CN / zh-TW / ja-JP); `CONTRIBUTING.md` README sync guidance extended to four locales. `scripts/check_spec_consistency.py` refactored to share zh-TW / zh-CN logic via `ZH_README_CONFIGS` tuple; both locales covered by `test_aligned_zh_cn_readme_passes` + `test_stale_zh_cn_badge_fails` regression tests (symmetric with the ja-JP tests added in #170).

**CI / infrastructure (no version bump — no behavior change to skills):**

- **#156 — Unified pytest invocation manifest.** Twelve `pytest scripts/test_*.py` invocations in `.github/workflows/spec-consistency.yml` are now declared in `scripts/_ci_pytest_manifest.toml` and run via `scripts/run_ci_pytest_manifest.py`. Drift guard `scripts/check_ci_pytest_manifest.py` rejects (a) missing `path`, (b) duplicate `id`, (c) duplicate `(path, args)`, (d) malformed `args`, (e) any `pytest scripts/test_*.py` re-introduced in the workflow outside the runner. `pip install pytest` consolidates from 12 redundant installs to one. 17 unit tests for runner + lint. `python3 -m unittest scripts.test_*` invocations stay inline (out of scope for #156). 41 disk `test_*.py` files that the manifest does not list remain unclassified — separate follow-up.

- **#155 — Re-attempt F4: harden `test-count-monotonic.yml` to fail on pytest collection errors.** Both head and base count steps now capture pytest's exit code separately from the pipe, treat exit 5 (no tests collected) as a tolerable degenerate case, and fail the gate on any other non-zero exit. Previously, a `2>/dev/null | grep -c '::' || true` swallow on the base step would silently set BASE_COUNT to 0 on a broken-import or fixture-missing error in the base commit, making the head-vs-base monotonic check vacuously pass. The original F4 fix landed in PR #153 commit 8121dfa during the v3.9.4.2 cycle but was reverted in 4abf9de when it surfaced #154 (now closed by PR #158). With #154 fixed and #156 keeping CI test discovery clean, F4 v2 ships symmetrically across head and base.

---

## [3.9.4.2] - 2026-05-19 — Post-ship hotfix for PR #149 CI discipline gates

**Trigger:** Codex post-ship review of PR #149 (7 CI discipline gates mechanizing the release-cycle review chain) surfaced 4 P2 findings. v3.9.4.2 hardens 3 of 4; the 4th (test-count-monotonic harden) was reverted because it surfaced a pre-existing `scripts/` package issue, tracked as #154 (since fixed by PR #158) and re-attempt #155.

**CI gate hardening (PR #149 + #153):**
- **F1 — harness-retirement scheduler context:** `harness-retirement-monthly.yml` adds `GH_REPO` so scheduled runs have repo context for `gh issue create` (workflow was silently failing on cron without it).
- **F2 — release-cooldown tag filter:** `release-cooldown.yml` filters `PREV_TAG` lookup to `v*` tags so non-release tags (e.g., legacy plugin tags) cannot bypass the cooldown gate.
- **F3 — release-cooldown hot-fix detection:** `release-cooldown.yml` also reads annotated tag subject + accepts the `hot-fix` spelling variant; v3.9.2 was previously a false-negative hotfix under the old detector.
- **F4 (reverted):** `test-count-monotonic.yml` harden landed in 8121dfa and reverted in 4abf9de when it surfaced `scripts/` package import errors (`ModuleNotFoundError: No module named 'scripts'`) — pre-existing latent defect masked by the prior `2>/dev/null | || true` pattern. Tracked as #154 (now closed by PR #158) and re-attempt #155.

**Release-cooldown symmetry follow-up (PR #157):**
- Override token `[skip-cooldown]` now read from both the commit message AND the annotated tag message. This v3.9.4.2 tag itself is the self-bootstrapping fix — the gate correctly identified v3.9.4.1 (3h prior) as the previous hotfix and fired the 24h cooldown, proving F2+F3 work end-to-end. The override symmetry patch makes the tag shippable.

**Closes:** #152. **Follow-ups:** #154 (closed by PR #158), #155, #156.

---

## [3.9.4.1] - 2026-05-19 — Post-ship hotfix for v3.9.4 temporal verification

**Trigger:** Codex post-ship review of v3.9.4 squash commit `af09cf5` surfaced 4 real bugs that per-task subagent reviewers missed during v3.9.4 implementation. v3.9.4 tag remains immutable; v3.9.4.1 patches the verifier and schema layer + brings docs in alignment.

**Bug fixes:**
- **#135 P1 (audit wiring):** `audit()` now passes `citation_provenance` through to `_pass_2_anachronism` and `_pass_4_causal`. When a ref slug has `confidence: low` or `conflict` in citation_provenance.yaml, the verifier emits `TEMPORAL-METADATA-MISSING` instead of using timeline dates as arithmetic ground truth. v3.9.4 dropped citation_provenance on the floor — spec §3.4 first-party safety check was structurally broken.
- **#135 P1 (date parser):** `_date_to_interval()` now parses all schema-valid date shapes including `YYYY-MM` (Crossref month-precision output) and `YYYY-MM-DD..YYYY-MM-DD` (interval precision used by effective_date_range). v3.9.4 only handled day/year/prose-month forms — schema-valid month/interval shapes raised ValueError and P2/P4 silently skipped the check via the existing `except ValueError: continue` guard.
- **#135 P2 (P4 direct-date binding):** P4 now binds each side of a causal trigger to either a `<!--ref:slug-->` marker OR a direct date capture in the sentence. v3.9.4 required refs on both sides, silently dropping sentences like "The 2026 policy enabled the 2020 rollout." `bound_dates.source` distinguishes `timeline_ref` from `draft_capture`; `bound_refs` is empty when both sides came from direct date capture.
- **#135 P2 (schema absent-property bypass):** `citation_provenance.schema.json` `confidence:high` allOf branch now requires both `crossref_issued` and `pdftotext_cover_first_line` to be present in addition to non-null (`then.required` added). v3.9.4 used `then.properties` only, which doesn't fire when a property is absent — so entries with `confidence:high` and both source fields omitted silently passed validation.

**Documentation:**
- `docs/ARCHITECTURE.md` updated from stale v3.8.0 baseline to v3.9.4.1; Section 8 Evolution Timeline filled in v3.8.1 / v3.8.2 / v3.9.0 / v3.9.1 / v3.9.2 / v3.9.3 / v3.9.4 / v3.9.4.1 entries; Section 9 Skill Modes table aligned to current versions.
- Suite-version needles aligned across MODE_REGISTRY.md, README.md badge + tag URL + section heading, README.zh-TW.md badge + tag URL + section heading, academic-pipeline/SKILL.md frontmatter, `.claude-plugin/plugin.json`, `scripts/check_spec_consistency.py` expected-text constants, `.claude/CLAUDE.md` skill suite table.

**Test count:** 1549 → **1561** (+12 net new tests covering all 4 fixes, 0 regression).

---

## [3.9.4] - 2026-05-18 — Temporal Verification Layer (advisory)

**External motivation:** Issue #135 — LLM next-token objectives are systematically blind to deterministic factual classes including temporal ordering. v3.9.4 adds a deterministic advisory verifier at the Phase 4 → 5 boundary covering 5 failure modes.

**Mechanisms:**
- M1: new Phase 2 sibling `timeline_extraction_agent` owning `phase2_investigation/timeline.yaml` + `phase2_investigation/citation_provenance.yaml`
- M2: Phase 4 → 5 deterministic verifier `scripts/temporal_integrity_audit.py` (5 passes)
- M3: Temporal Integrity Iron Rule in `report_compiler_agent` + `draft_writer_agent`
- M6-minimal: First-party Crossref `issued` + pdftotext cover verification
- M7-minimal: Date provenance + comparator materialization
- M5-stub: User-declared `version_family_id` only

**Zero modification** to `literature_corpus_entry`, `claim_audit_result`, `claim_intent_manifest`. `bibliography_agent` unmodified (F2 invariant). 3 new sidecar schemas (aggregate-level with `$defs`).

**Coverage estimate:** 55-70% baseline / 65-75% with M7 minimal (LLM extractor blindness on tuple extraction is structural; advisory architecture acknowledges this).

**Out of v3.9.4 scope** (deferred to v3.10): M4 reviewer integration, M5 full version discovery, M6 full PDF audit, M8 relation manifest, CC5 catalog-completeness semantics, hard-block policy, OpenAlex lookup.

Spec: `docs/design/2026-05-18-ars-v3.9.4-temporal-verification-spec.md`.

---

## [3.9.3] - 2026-05-18 — Housekeeping (#128 §1-3, §5-6)

Pure refactor + one latent-bug fix carrying over from the v3.9.0 `/simplify` review backlog. The v3.9.0 cross-index triangulation client family (Semantic Scholar + OpenAlex + Crossref) shipped intentionally byte-equivalent across 3 client modules for code locality; now that the family is stable, the dedup prevents sibling drift when threshold tuning, normalization rules, or throttle measurement need adjustment.

### Refactor — extracted helpers (no behavior change)

- **`scripts/_text_similarity.py`** — extracts 4 helpers + 4 constants previously triple-implemented byte-equivalent in `semantic_scholar_client.py` / `openalex_client.py` / `crossref_client.py`: `_PUNCT_TRANSLATION`, `_normalize_title`, `_similarity`, `_TITLE_SIMILARITY_THRESHOLD = 0.70`, `_BACKOFF_SECONDS = 2.0`, `_MAX_RETRIES = 3`. 14 new tests on the shared module.
- **`scripts/_passport_yaml.py`** — extracts ruamel.yaml round-trip config (`preserve_quotes = True`, `indent(mapping=2, sequence=4, offset=2)`) + `load_passport` / `dump_passport` functions previously duplicated byte-equivalent in `migrate_literature_corpus_to_v3_7_3.py` + `migrate_literature_corpus_to_v3_9_0.py`. 7 new tests on the shared module.
- **`contamination_signals._resolve_by_doi_then_title`** — private helper for the identical DOI-then-title control flow shared by `resolve_openalex_unmatched` (§3.4) + `resolve_crossref_unmatched` (§3.5). Both public wrappers preserve the v3.9.0 spec API surface; exception-type differentiation stays at the wrapper. 10 existing resolver tests verify byte-equivalent behavior.

### Latent-bug fix — throttle measurement standardized on `time.monotonic`

- OpenAlex + Crossref clients now use `time.monotonic()` for `_throttle()` elapsed measurement + `_last_request_at` anchor refresh, matching Semantic Scholar (which had standardized on monotonic per #115 R5-2). NTP / manual clock adjustments could push `time.time()` backward, producing negative elapsed and either inflated sleep (negative compared less than min_interval) or zero sleep — latent throttle-bypass / API-spam bug. Documented as a "maintenance smell" in #128 §6.
- New tests (`test_openalex_client::test_throttle_uses_monotonic_clock` + `test_crossref_client::test_throttle_uses_monotonic_clock`) lock NTP-safe semantics: throttle reads `time.monotonic` and never reads `time.time`.

### Dual-path import infrastructure

- All 5 module-level cross-imports in `openalex_client.py` / `crossref_client.py` / `semantic_scholar_client.py` / `migrate_literature_corpus_to_v3_7_3.py` / `migrate_literature_corpus_to_v3_9_0.py` use the dual-path try/except pattern (sibling-first, namespace-package fallback). Follows `scripts/slr_lineage.py` precedent but inverted for class-identity preservation (pytest uses sibling-path imports; `SemanticScholarUnavailable` from `scripts.contamination_signals` is a different class instance than `contamination_signals.SemanticScholarUnavailable`).
- Latent fix: `scripts.semantic_scholar_client` + `scripts.migrate_literature_corpus_to_v3_7_3` are now `import scripts.X`-clean from repo root (were silently broken on main due to pre-existing absolute cross-imports). Caught by codex round-1 reasoning trace.

### Deferred from #128

- **§4 — parallelize OA + CR per-entry calls in v3.9.0 migration tool** carried to #138 (target v3.9.4 or v3.10). Introduces new behavior + ThreadPoolExecutor + test-rebuild scope; incompatible with v3.9.3 patch boundary.

### Regression status

- 1482 → **1505 passed** + 3 skipped + 111 subtests (+23 new tests, 0 regression).
- `scripts/check_spec_consistency.py` + `scripts/check_version_consistency.py` green.
- 6/6 `import scripts.X` paths verified clean from repo root (3 from-OK-to-OK, 2 latent-broken-now-OK, 1 OK throughout).
- Cross-model review: codex round 1 + 2 both 0 explicit findings (one P1 self-caught from R1 trace, closed pre-R2). Gemini 3.1-pro-preview round 1: 0 findings.

---

## [3.9.2] - 2026-05-18 — Phase boundary hot-fix (#133)

Hot-fix for issue #133 (phase scope inflation). A user incident showed that ARS auto-dispatched a single-phase agent (`bibliography_agent`) when given ambiguous cross-phase input (pre-written abstract + pre-collected literature), and the dispatched agent then autonomously executed Phases 3-6, skipping mandatory independent crosschecks (DA / EIC / Ethics).

This release ships the prompt-discipline + advisory-verifier hot-fix. The deterministic gate (PreToolUse hook + multi-phase task envelope schema + author provenance) is tracked separately as **v3.10 active conductor (#134)** — long-term architectural fix.

Design history: 4 design rounds (v1-v4) + mid-impl review. Triple-track reviewer use cases (codex `review --base main` + inline opus subagent + self-review). Codex 0.130 broke on this repo context 5x consecutive per memory `feedback_codex_0_130_docs_review_broken.md` (49 files / 1529 lines on full branch is firmly in the broken corner); inline opus was the substantive reviewer throughout. Net effect: design has been challenged thoroughly; honest framing applied where prompt-only mitigation is known insufficient.

### Added

- **Routing Discipline (Phase L1)** — `.claude/CLAUDE.md` gains a new "Routing Discipline (v3.9.2)" section before existing Routing Rules 1-5. 3 routing classes: explicit intent → proceed directly; cross-phase materials → clarify with a-d options; no-materials ambiguous → clarify. `[direct-mode]` byte-0 escape hatch (case-insensitive; bracket-form strict). Anti-pattern explicitly named.
- **Intent clarification protocol** — new `shared/references/intent_clarification_protocol.md` (~200 lines): trigger condition table, pipeline phase reference (Phase 0-7 marker conventions), clarification message template (a-d options, no AskUserQuestion tool), `[direct-mode]` mechanism spec with 5 worked examples, v3.10 carry-over notes.
- **Phase Boundary block on 22 Bucket A agents (Phase 1)** — single-phase agents (deep-research × 9, academic-paper × 7, academic-paper-reviewer × 6) gain a `## Phase Boundary (v3.9.2)` block customized per agent: phase number, deliverable type, MUST-NOT cross-phase writes, MAY-READ upstream context (Phase 5 reviewers granted explicit cross-phase READ for review), explicit coexistence with skill-specific protocols (v3.6.2 / v3.6.5 / v3.6.6 / v3.6.7 / v3.7.1). 16 Bucket B/C/D agents (multi-phase / phase-orthogonal / cross-phase-meta) intentionally NOT fenced — honest framing per opus HIGH-2 (placebo prose creates false-enforcement illusion).
- **Phase-by-phase invocation contract (Phase 3)** — 4 SKILL.md files gain a "Phase-by-phase Invocation Contract (v3.9.2)" section: Mode A (orchestrator-driven, default) vs Mode B (phase-by-phase cross-session resume), Bucket A enforcement scope, coexistence with skill-specific protocols.
- **Advisory verifier (Phase 4)** — new `scripts/check_pipeline_integrity.py`: scans working directory for `phaseN_*/` (N=1-6), flags STRUCTURAL finding when phase5 dir lacks DA/EIC/Ethics filenames (the #133 pattern). HEURISTIC adjacent-phase-mtime rule (`--strict`, default OFF). Cross-platform, user-invokable, advisory output (exit 0 on findings), JSON + text output modes. Normative filename convention documented; v3.10 envelope provenance replaces filename matching.
- **Phase Boundary coverage lint (Phase 5)** — new `scripts/check_v3_9_2_phase_boundary.py`: enforces 22 Bucket A agents have block, 16 Bucket B/C/D agents don't, and each Bucket A block contains 4 load-bearing phrases (Phase Boundary v3.9.2, MUST NOT, MAY READ, Enforcement v3.9.2). Wired to `.github/workflows/spec-consistency.yml`.
- **Classification spec** — new `docs/design/2026-05-18-ars-v3.9.2-agent-phase-classification.md`: canonical 38-agent table with 4-bucket model (A=22, B=4, C=8, D=4) + per-agent out-of-scope inflation risk column.
- **8 behavioral smoke test fixtures** — `tests/fixtures/issue_133_routing/`: cross-phase abstract+lit (the #133 root case), single-phase explicit, no-materials ambiguous, /ars-slash command, `[direct-mode]` byte-0 honored, mid-message NOT honored, case-insensitive accepted, full draft+abstract+lit+reviews. Honestly framed as LLM-behavior assertions with cross-model spot-check criterion (100% Opus 4.7, ≥75% Sonnet 4.6 + GPT-5.5).
- **Plugin metadata bump** — `.claude-plugin/plugin.json` version 3.8.2 → 3.9.2 (was stale; also catches v3.9.0 + v3.9.1 deferrals); description updated for 38-agent ensemble and v3.9.2 phase boundary feature.

### Fixed

- **`.claude/CLAUDE.md` Suite version was stale at 3.9.0** — v3.9.1 ship missed bumping it (latent lint bug surfaced during v3.9.2 work). v3.9.2 atomic bump fixes this.

### Tests

- 12 new tests in `scripts/test_check_pipeline_integrity.py` (verifier).
- 3 new tests in `scripts/test_check_v3_9_2_phase_boundary.py` (boundary coverage lint).
- 4 additional tests after Phase 6 mid-impl review absorption (dotfiles ignored, multiple phase5 dirs independent, Unicode stem matching, nested subdir recursion).
- Regression baseline: 1463 → 1482 passed (+19); 3 skipped + 111 subtests unchanged; 0 failures.

### Out of scope (carry to v3.10 conductor, issue #134)

- PreToolUse hook (Phase 0.1 verified Claude Code payload includes `agent_type` field; hook implementation requires multi-phase schema first — both deferred to v3.10).
- Multi-phase `ars_phase_writes` + `ars_phase_reads` envelope schema (scalar `ars_phase` cannot represent agents like `devils_advocate_agent` at Phases 1/3/5 or `report_compiler_agent` at Phases 4/6 — design correctly with envelope, not retrofit scalar).
- Deterministic verifier with author provenance (advisory v3.9.2 filename-heuristic version flagged FP-prone in docstring).
- Orchestrator cross-phase intake capability (`pipeline_orchestrator_agent` currently keyword-matches user phrasing; cannot reconcile cross-phase artifacts without explicit user signal — this is the conductor's core feature).

### Migration notes

Existing in-flight projects: no break expected. v3.9.2 only adds prompt sections and an opt-in advisory verifier. Existing slash commands (`/ars-*`) continue to work without change.

User-facing behavior change: if you previously dropped pre-existing materials (abstract + literature) into a fresh session without invoking a specific slash command, ARS may now clarify with a-d options instead of silent dispatch. To bypass clarification for direct agent dispatch, prefix your first message with `[direct-mode]`. To run the full pipeline on pre-existing materials, invoke `/ars-full`.

If you see a Bucket B multi-phase agent (devils_advocate, report_compiler, argument_builder, visualization) producing out-of-scope content, this is a known v3.9.2 limitation — recurrence is expected for these 4 agents until v3.10 envelope ships. Remediation: switch to orchestrator-driven Mode A via `/ars-full` or report the case to issue #134 with transcript excerpt.

---

## [3.9.1] - 2026-05-18 — v3.9.0 client hardening (#129 + #130)

Two-bug hotfix surfaced by codex review of `ars-codex` PR #13 (vendor sync to v3.9.0 `74413a4`). Both bugs exist in v3.9.0 main: #129 violates the v3.9.0 §3.7 per-API degradation contract; #130 crashes a defensive lint on malformed input. Neither changes the spec or schema.

### Fixed

- **#129 — OpenAlex / Crossref response-read failures now translate to `*Unavailable`.** In `scripts/openalex_client.py:_get` and `scripts/crossref_client.py:_get`, `urlopen` succeeded but `resp.read()` / `body.decode("utf-8")` / `json.loads()` failures (socket drop mid-stream, truncated body, garbled UTF-8 body, HTML 503 page returned with 200 status) escaped the client as raw `OSError` / `http.client.IncompleteRead` / `UnicodeDecodeError` / `JSONDecodeError`. `scripts/migrate_literature_corpus_to_v3_9_0.py` only catches `OpenAlexUnavailable` / `CrossrefUnavailable`, so one transient response failure during a 500-entry backfill aborted the whole migration instead of dropping just the affected field. Narrow except block around read+decode+parse now catches `(OSError, http.client.HTTPException, UnicodeDecodeError, json.JSONDecodeError)` — `HTTPException` covers `IncompleteRead` (canonical mid-stream socket drop, inherits HTTPException not OSError, R1 codex P2 closure). Mirrors the existing 5xx-skip pattern: per-API tolerant per the v3.9.0 spec §3.7 documented degradation contract and `bibliography_agent.md` "Triangulation Extension".

- **#130 — `check_claim_audit_consistency` non-string `manifest_id` guard.** `_build_manifest_index` (line 644) and `_build_manifest_constraint_index` (line 675) used `manifest_id` as a dict key via `setdefault(mid, set())` / `out[mid] = bucket` before checking type. For malformed passports where the schema validator already noted `manifest_id` as `array` / `object`, the index builder raised `TypeError: unhashable type: 'list'` and terminated lint with a traceback before `validate_passport()` could return the schema finding cleanly. Added `isinstance(mid, str) and mid` guard at both sites, matching the surrounding `_check_inv_17_for_manifest` / `claim_id` invariant-walker pattern. Schema validator still records the type mismatch — the guard just lets the lint surface findings cleanly instead of crashing.

### Tests

- `scripts/test_openalex_client.py`: +4 tests covering OSError on `resp.read()`, invalid UTF-8 body, invalid JSON body, and `http.client.IncompleteRead` (R1 codex P2 closure).
- `scripts/test_crossref_client.py`: +4 symmetric tests.
- `scripts/test_claim_audit_schema.py`: new `TSManifestIdNonStringGuard` class with 2 tests (`manifest_id` as list / dict).
- Regression baseline: 1453 → 1463 passed (+10), 3 skipped + 111 subtests unchanged, 0 failures.

### Out of scope

- Spec / schema / CHANGELOG narrative not touched — the degradation contract is already documented in spec §3.7; this just makes code honor it.
- `ars-codex` adapter sibling: the same two fixes will surface on next vendor sync (v3.9.1 → ars-codex v0.1.8). No action needed in this release.

---

## [3.9.0] - 2026-05-17

### Added
- Cross-index triangulation as v3.7.3 contamination_signals Vector 3 (issue #102). Two new optional boolean fields (`openalex_unmatched`, `crossref_unmatched`) inside `literature_corpus_entry.schema.json`. Manual-entry not-rule extended symmetrically to forbid all three lookup fields (preprint flag remains exempt — heuristic, not lookup).
- OpenAlex API protocol (`deep-research/references/openalex_api_protocol.md`) + production client (`scripts/openalex_client.py`).
- Crossref API protocol (`deep-research/references/crossref_api_protocol.md`) + production client (`scripts/crossref_client.py`).
- `bibliography_agent.md` Triangulation Extension subsection — parallel S2/OpenAlex/Crossref lookups, per-API degradation, manual exemption, R-L3-2-D constraint, per-entry ingest log format.
- Finalizer 4-tier advisory annotation in `pipeline_orchestrator_agent.md`: k=1 → `CONTAMINATED-COVERAGE-NOISE` (or legacy `CONTAMINATED-UNMATCHED` for k_max=1 S2-only), k=2 → `CONTAMINATED-PARTIAL-UNMATCH`, k=3 → `CONTAMINATED-TRIANGULATION-UNMATCHED`. All tiers advisory; gate refusal list unchanged.
- `formatter_agent.md` pass-through allowlist extends from 3 v3.7.3 suffixes to 9 (3 legacy + 6 v3.9.0). Refusal rules 1-10 unchanged.
- v3.9.0 lint (`scripts/check_v3_9_0_triangulation.py`): set-equality on formatter allowlist, refusal-list-unchanged guard. Exact-token extraction prevents substring collisions (R3 P2 closure).
- Migration tool (`scripts/migrate_literature_corpus_to_v3_9_0.py`): backfill v3.7.3 → v3.9.0; stable-fields idempotency; per-API degradation tolerant; dry-run mode; daisy-chained migration scope (pre-v3.7.3 entries require v3.7.3 migration first).
- 3 new firm rules in spec §3.3: R-L3-2-C (k computed over present fields, absent ≠ false), R-L3-2-D (no OpenAlex `primary_location.source.type` / Crossref `type` used for v3.9.0 classification logic), R-L3-2-E (refusal list unchanged; pass-through allowlist extends).

### Design philosophy
- v3.9.0 is the **measurement layer** for cross-index triangulation. The **policy layer** (strict modes, hard-block tier, venue-type-scoped strict, `triangulation_policy` field, `venue_type` field) is deferred to v3.10 per spec §2.3.
- The k=3 marker is `CONTAMINATED-TRIANGULATION-UNMATCHED` (describes observable condition), not `CONTAMINATED-LIKELY-FABRICATED` (would infer cause unsupportable on humanities / non-English / dissertation references where coverage gaps are real).
- R-L3-2-A preserved verbatim: contamination signals never block emission on their own.

### Migration path
- v3.7.3 corpora: run `python scripts/migrate_literature_corpus_to_v3_9_0.py PATH` to backfill the two new fields.
- Pre-v3.7.3 corpora: run `python scripts/migrate_literature_corpus_to_v3_7_3.py PATH` FIRST, then v3.9.0 migration (daisy-chained per spec §3.7).

### Review trail
- R1 (commit `d9280bf`): 15 findings (3 P0, 8 P1, 4 P2) — closed.
- R2 (commit `7d51215`): 12 findings (0 P0, 3 P1, 9 P2) — closed.
- R3 (commit `4297c27`): 4 P2 findings — closed in Task 1 of impl plan.
- Both tracks (codex gpt-5.5 xhigh + Gemini 3.1-pro-preview) READY-FOR-IMPL after R3.

---

## [3.8.2] - 2026-05-17 — #118 uncited audit_tool_failure surface

Fixes the #118 carry-over from #103 R3 codex P2 #5. The `ARS_CLAIM_AUDIT=1` uncited constraint-judging path used to silently substitute `{"judgment": "NOT_VIOLATED", "rationale": "..."}` on `JudgeInvocationError`, suppressing HIGH-WARN constraint checks on transient judge outage (judge timeout, API 5xx, network error, etc.). v3.8.2 routes those failures through a dedicated `uncited_audit_failures[]` aggregate at MED-WARN advisory tier, mirroring INV-14 semantics on the cited path but using a separate schema because `claim_audit_result.ref_slug` is required and the uncited path has no ref to bind.

The #118 issue body listed four candidate options. Option 1 (extend `constraint_violation.schema.json`) would have broken the `judge_verdict: const VIOLATED` invariant and re-derived every CV-INV. Option 3 (overload `uncited_assertions[]` with a `fault_class` field) would have polluted the D4-c LOW-WARN advisory channel with audit-time infrastructure signal. Option 4 (re-raise `JudgeInvocationError` and abort the audit pass) would have dropped audit coverage for the entire run on a single transient outage — bad UX for N>50 papers running against flaky judge endpoints. Option 2 (new aggregate) ships here: structural honesty, schema integrity preserved, audit coverage preserved.

### Added

- **`shared/contracts/passport/uncited_audit_failure.schema.json`** — new aggregate per spec §3.6. Required fields: `finding_id` (`UAF-NNN`), `claim_text`, `section_path`, `scoped_manifest_id`, `fault_class` (closed enum mirroring INV-14), `rationale` (MUST begin with fault_class prefix), `judge_model`, `judge_run_at`, `rule_version: D4-c-v1-uaf-v1`. Optional `manifest_claim_id` (non-null when failure was against an NC-C claim-level constraint, null when against MNCs only).
- **UAF-INV-1..UAF-INV-6** lint coverage in `scripts/check_claim_audit_consistency.py` rule 4d:
  - UAF-INV-1: finding_id uniqueness across the aggregate
  - UAF-INV-2: scoped_manifest_id cross-array integrity
  - UAF-INV-3: (scoped_manifest_id, manifest_claim_id) pair integrity when manifest_claim_id non-null
  - UAF-INV-4: per-(sentence, manifest) dedup with key `(scoped_manifest_id, section_path, claim_text_hash)`
  - UAF-INV-5: rationale fault_class prefix matches the row's own `fault_class` field
  - UAF-INV-6: cross-aggregate exclusivity vs `constraint_violations[]` (VIOLATED and audit_tool_failure are mutually exclusive verdict states at per-(sentence, manifest) level)
- **Finalizer §5 MED-WARN advisory row**: annotation `[CLAIM-AUDIT-TOOL-FAILURE-UNCITED — <fault-class>]` next to the offending sentence. Always advisory; gate passes — retry on next pipeline pass is the remediation. Formatter REFUSE list unchanged (UAF is advisory, not gate-refuse).
- **`UAF_RULE_VERSION = "D4-c-v1-uaf-v1"`** constant in `scripts/_claim_audit_constants.py` for shared use by pipeline runtime and lint.
- **18 new tests** keeping the regression baseline 0 (694 → 712 tests):
  - 15 schema + lint tests in `scripts/test_claim_audit_schema.py::TSUAFUncitedAuditFailureInvariants`
  - 3 pipeline integration tests in `scripts/test_claim_audit_pipeline.py::TP23UncitedJudgeOutageEmitsUAF` proving the swallow is replaced with UAF emit and no synthetic NOT_VIOLATED leaks into any aggregate

### Changed

- **`scripts/claim_audit_pipeline.py`**: swallow site at line 1211-1224 (the synthetic `NOT_VIOLATED` substitution) replaced with `_uncited_audit_failure_entry(...)` emission + `continue`. Pipeline return now includes `uncited_audit_failures` alongside the other five aggregates.
- **`docs/design/2026-05-15-issue-103-claim-alignment-audit-spec.md`**: amended with new §3.6 (schema + UAF-INV-1..6 + co-emission rules), §4 step 5 stream (d) routing clause, §4 step 9 fourth error-handling bullet, §5 finalizer outputs list + advisory paragraph, §6 lint rule 4d + precedence rule 6 cross-aggregate exclusivity reference.
- **`academic-pipeline/agents/claim_ref_alignment_audit_agent.md`**: Output emission table grows seventh row for `uncited_audit_failures[]`. Error handling table grows from 3 failure surfaces to 4 (the new uncited-path UAF row mirrors the cited-path `audit_tool_failure` row).

### Fixed

- **#118**: uncited judge failure no longer swallowed as NOT_VIOLATED; the HIGH-WARN constraint check path is now observable on transient outage. Pre-v3.8.2 a flaky judge endpoint could silently pass a draft with a real MUST-NOT violation; v3.8.2 surfaces the operational failure at MED-WARN advisory tier so a retry pass picks it up.

### Review trail

Single-PR ship after spec → TDD → impl. UAF schema design followed the design-phase brainstorming rule: option 1-4 trade-off analysis happened in conversation with the user before any code, captured in a local gitignored decision memo. Implementation followed strict TDD RED → GREEN — 15 schema/lint tests + 3 pipeline tests all failed in their intended way (no schema file, no lint logic, swallow site still active) before the schema, lint, helper, and pipeline change landed. No regression on the 694 pre-existing tests.

---

## [3.8.1] - 2026-05-17 — claim_audit lint hardening (#119 + #120 4×P2 closure)

Defense-in-depth patch on `ARS_CLAIM_AUDIT=1` opt-in lint paths. Five fixes carried over from #103 R6 + R8 independent review, consolidated into one v3.8.1 release. No schema semantic change, no behavior change for well-formed payloads — pre-fix surfaces all crashed the CLI with `TypeError` / `AttributeError` instead of returning actionable lint findings or routing through the INV-14 `audit_tool_failure` translation boundary.

### Fixed

- **#119 / #120 P2-2 — nested schema-invalid shapes no longer crash invariant walkers.** Added `_iter_dicts` helper and narrow `isinstance(str)` guards in `_check_inv_17_for_manifest`, `_check_manifest_invariants`, `_build_manifest_index`, `_build_manifest_constraint_index` so that nested `claim_intent_manifests[].claims` as string, `claims[].claim_id` non-string, or `audit_sampling_summaries[].audited_indices` mixed types now surface as clean schema findings instead of crashing on `for claim in "broken":`, regex against non-string, or `int <= str` comparison. The schema validator still records the type mismatch separately — narrow walker guards prevent the second-stage crash without masking schema-vs-invariant double coverage (option 2 refined, not aggregate-level skip).
- **#120 P2-1 — CV-INV-4 dedupe scoped by `scoped_manifest_id`.** Dedupe key extended from `(section_path, claim_text_hash, violated_constraint_id)` to `(scoped_manifest_id, section_path, claim_text_hash, violated_constraint_id)`. Per M-INV-4, `manifest_id` is unique across the passport but constraint ids (`MNC-*` / `NC-*`) are only unique WITHIN a manifest — two manifests in the same passport may legitimately carry colliding constraint ids, and the same sentence may then violate both. Pre-fix, the dedupe false-positived these as duplicates. Spec wording in §3.5 + §7.1 4b updated.
- **#120 P2-3 — judge `judgment` `isinstance(str)` guard before set membership.** `_validate_judge_dict` now rejects a non-string judgment (e.g. malformed `{"judgment": [1, 2], "rationale": "..."}`) as `judge_parse_error → audit_tool_failure` via the INV-14 translation boundary instead of bubbling `TypeError("unhashable type: 'list'")` out of the set-membership test.
- **#120 P2-4 — retrieve `ref_retrieval_method` `isinstance(str)` guard before set membership.** Symmetric to P2-3 on the retrieval boundary. `_invoke_retrieve` rejects a non-string method as `retrieval_api_error → audit_tool_failure` instead of crashing on set membership.

### Tests

- `scripts/test_claim_audit_schema.py`: 3 new tests in `TS9MalformedPassportGuard` (nested string / non-string claim_id / mixed-type indices) + new test class `TSCVDedupeManifestScope` with 2 tests (cross-manifest collision must keep both; within-manifest true duplicate still caught).
- `scripts/test_claim_audit_pipeline.py`: 2 new tests in `TP12JudgeFailureAuditToolFailure` (non-string list + dict judgment) + 1 new test in `TP14RetrieveFailureAuditToolFailure` (non-string list method).
- Regression baseline: 682 → 690 tests (+8), 0 failures, 0 errors across full `scripts/test_*.py` discovery.

### Design memo

A local, gitignored design memo carries the option-1 vs option-2 analysis, CV-INV-4 dedupe key shape rationale, and the release-framing decision.

Closes [#119](https://github.com/Imbad0202/academic-research-skills/issues/119). Refs [#120](https://github.com/Imbad0202/academic-research-skills/issues/120) P2-1, P2-2, P2-3, P2-4 (all four R8 findings).

---

## [3.8.0] - 2026-05-16 — L3 Claim-Faithfulness Locator + Audit (v3.7.3 + #103 paired milestone)

v3.7.3 + v3.8 close the L3 (claim-faithfulness) gap end-to-end. v3.7.3 ships the locator infrastructure (every citation carries a three-layer anchor so the audit can fetch the cited passage); v3.8 ships the audit pass that consumes those anchors, judges whether the cited source supports the claim, and gate-refuses HIGH-WARN violations at the formatter terminal hard gate. The release also bundles 5 audit-trail-shipped feature PRs accumulated on main since v3.7.0 (#104 / #105 / #108 / #111 / #115). External motivation: Zhao et al. arXiv:2605.07723 (2026-05) — 146,932 hallucinated citations across arXiv / bioRxiv / SSRN / PMC in 2025.

### #103 — v3.8 claim ↔ reference faithfulness audit agent (2026-05-16)

**Parent issue:** [#103](https://github.com/Imbad0202/academic-research-skills/issues/103) — closes the L3 (claim-faithfulness) gap left open by v3.7.3 (which closed the locator-channel half). Spec: `docs/design/2026-05-15-issue-103-claim-alignment-audit-spec.md` + decision doc `docs/design/2026-05-15-issue-103-claim-alignment-audit-decision.md` (D1-D6 settled).

**Why:** Zhao et al. arXiv:2605.07723 (2026-05) shows 146,932 hallucinated citations across arXiv / bioRxiv / SSRN / PMC in 2025; v3.7.3 stopped the "no locator" path but a present-but-wrong claim ↔ source mismatch was still undetected. v3.8 adds a Stage 4→5 audit pass that judges every sampled citation against its retrieved excerpt, emits 5 new passport aggregates, and drives 5 new HIGH-WARN annotation classes through the formatter terminal hard gate.

**New components:**

- **`claim_ref_alignment_audit_agent`** (1 new agent, `academic-pipeline/agents/`) — opt-in (`ARS_CLAIM_AUDIT=1`, default OFF for v3.8.0) audit agent dispatched between v3.7.1 cite finalizer and formatter hard gate. Takes citations + manifests + corpus + Stage 4 draft sentence stream (full uncited + D4-c filtered subset).
- **5 new passport schemas** (`shared/contracts/passport/`): `claim_audit_result`, `claim_intent_manifest`, `claim_drift`, `uncited_assertion`, `constraint_violation`. Cross-field invariants INV-1..INV-18 / M-INV-1..M-INV-4 / U-INV-1..U-INV-4 / D-INV-1..D-INV-4 / CV-INV-1..CV-INV-4 lint-enforced (JSON Schema can't express the conditional matrix relating judgment / audit_status / defect_stage / ref_retrieval_method).
- **Runtime pipeline** (`scripts/claim_audit_pipeline.py`) — implements §4 step 1-6 + manifest set-diff (D6 set-of-text semantics). Per-citation judge wrapping (`_invoke_judge` + `_invoke_retrieve` translate transient failures to INV-14 `audit_tool_failure` rows: judge_timeout / judge_api_error / judge_parse_error / cache_corruption / retrieval_api_error / retrieval_timeout / retrieval_network_error). Cache hits re-validated through the same surface. Per-manifest uncited judge calls to prevent MNC id collisions across manifests.
- **8-row finalizer matrix** (`scripts/claim_audit_finalizer.py`) — discriminates paywall (LOW-WARN advisory) / fabricated reference (HIGH-WARN gate-refuse) / anchorless (HIGH-WARN defense-in-depth) / audit_tool_failure (MED-WARN advisory) via `ref_retrieval_method` alongside `(judgment, defect_stage)`.
- **5 new HIGH-WARN annotation classes** in `formatter_agent` REFUSE list: `[HIGH-WARN-CLAIM-NOT-SUPPORTED]` / `[HIGH-WARN-NEGATIVE-CONSTRAINT-VIOLATION]` / `[HIGH-WARN-FABRICATED-REFERENCE]` / `[HIGH-WARN-CLAIM-AUDIT-ANCHORLESS]` / `[HIGH-WARN-CONSTRAINT-VIOLATION-UNCITED]`. Mirrors v3.7.3 R-L3-1-A asymmetry — `/ars-mark-read` does NOT clear; remediation is fixing the prose.
- **"Claim Intent Manifest Emission" sibling section** added to `synthesis_agent` / `draft_writer_agent` / `report_compiler_agent` per v3.6.7 PATTERN PROTECTION pattern. The §3a SHA-pinned blocks stay byte-equivalent to commit `e7e775a0e1b4`.
- **Calibration runner** (`scripts/claim_audit_calibration.py` + `scripts/test_claim_audit_calibration.py` + `scripts/fixtures/claim_audit_calibration/gold_set.json`) — 20-tuple gold set (12 alignment + 8 constraint); T-C1 threshold gate (FNR < 0.15 + FPR < 0.10), T-C2 per-class FNR/FPR, T-C3 gold-set shape integrity. Re-run: `PYTHONPATH=. python3 -m unittest scripts.test_claim_audit_calibration -v`.
- **2 new lints + 1 new pytest module + 7 new unittest modules wired into CI** (`.github/workflows/spec-consistency.yml`): `check_claim_audit_consistency.py` (38 invariant checks + schema validation), `check_v3_8_annotation_literal_sync.py` (formatter-finalizer literal drift gate). Test suite: 194 unittest tests across the 7 modules.

**Review trail (Step 13 dual-track, 2026-05-16):** 8 rounds codex (gpt-5.5 xhigh) + 1 round Gemini 3.1-pro-preview before Gemini quota exhausted. Trajectory R1 4P1+2P2 → R2 0P1+3P2 → R3 0P1+5P2 → R4 2P1+2P2 → R5 0P1+2P2+1P3 → R6 1P1+1P2 → R7 1P1+1P2+1P3 → **R8 0P1+4P2 → ship**. Per `feedback_codex_review_surface_loop_design_phase.md` design-phase P2 noise floor doesn't auto-converge; the user declared ship signal at R8 with all P0/P1 closed and 4 R8 P2 carried over to v3.8.1 ([#120](https://github.com/Imbad0202/academic-research-skills/issues/120)).

**Carry-over follow-up issues:**

- [#118](https://github.com/Imbad0202/academic-research-skills/issues/118) — uncited path NOT_VIOLATED swallow on judge failure (schema-level decision)
- [#119](https://github.com/Imbad0202/academic-research-skills/issues/119) — nested schema-invalid shapes still crash invariant helpers
- [#120](https://github.com/Imbad0202/academic-research-skills/issues/120) — 4 R8 P2 findings (CV-INV-4 dedupe scope / invariant walker short-circuit / judgment + method type-check before set membership)

**Regression baseline (post-ship):**

- pytest: 1356 passed, 3 skipped, 103 subtests (was 1107 pre-#103, +249 tests across schema / pipeline / detector / manifest / finalizer / e2e / calibration / lint coverage)
- v3.x lints: 7/7 PASS (v3.6.7 / v3.6.8 ×4 / v3.7.3 / v3.8)
- personal-boundary: 0 violations (614 files scanned)
- SHA-pinned zero-touch: `shared/sprint_contract.schema.json` 0 lines diff, `shared/contracts/passport/audit_artifact_entry.schema.json` 0 lines diff against main

### #115 — Semantic Scholar client maturity: throttle + outage latch (2026-05-15)

**Parent issue:** [#115](https://github.com/Imbad0202/academic-research-skills/issues/115) — follow-up to #105 PR codex round-5 [P2]×2 findings (R5-2 throttle + R5-3 outage latch). Both deferred during #105 ship per architectural-inflection discipline; this entry closes the SS-client maturity gap.

**Modified files:**

- `scripts/semantic_scholar_client.py` — two additions:
  - **Throttle** (#115 R5-2): new ctor params `clock` + `min_interval_seconds`. Defaults: 1.0s unauthenticated (1 req/s per protocol), auto-drops to 0.1s when `S2_API_KEY` detected (authenticated 10 req/s tier). Pre-request pacing tracks `_last_request_at`; sleeps `max(0, min_interval - elapsed)` before each call. First request passes through.
  - **Outage latch** (#115 R5-3): `_latched_unavailable` flag set on `URLError`. Subsequent `lookup()` calls short-circuit with `SemanticScholarUnavailable` without invoking urlopen. New `reset_outage_latch()` method lets long-running tools retry between passport batches. HTTP 5xx does NOT latch (server-side error ≠ transport outage).
- `scripts/test_semantic_scholar_client.py` — 9 new tests (5 throttle: first-no-sleep / back-to-back / past-interval / authenticated-tier / override; 3 latch: URLError short-circuits / reset restores / 5xx does not latch; 1 efficiency: 429-retry refreshes throttle anchor).
- `scripts/contamination_signals.py` — new `reset_client_outage_latch(client)` helper. Production clients implementing the outage-latch pattern expose `reset_outage_latch()`; mocks may not. Helper invokes when present, no-ops when absent — avoids AttributeError when callers swap clients. 2 new tests.
- `scripts/migrate_literature_corpus_to_v3_7_3.py` — `migrate_directory` resets the SS client's outage latch between passports so a transient network blip on one passport doesn't permanently disable lookups for the rest of the directory. Within a single passport the latch still short-circuits to protect a dead service from N retry waves.

**Production behavior change:**

- `_build_default_ss_client()` API unchanged (`SemanticScholarClient()` no-arg). New throttle is automatic per protocol — no migration tool changes required.
- For a 5000-entry unauthenticated migration: same ~1.5hr runtime (already constrained by 1 req/s); now achieves it via deterministic pacing rather than 429-retry exhaustion.
- For an authenticated migration (`S2_API_KEY` set): drops to 0.1s/call = ~8min for 5000 entries.
- Network outage during large corpus: previously retried every entry independently (up to 30s timeout per entry on the slow path); now the first URLError latches the client and subsequent entries short-circuit until the next batch boundary calls `reset_outage_latch()`. The `migrate_directory` helper does this reset automatically between passports.

**Out of scope:** migration tool (`migrate_literature_corpus_to_v3_7_3.py`) — #105 partial-fill / provenance contract correct as shipped. Protocol doc — already correct; this issue is implementation alignment.

**Regression:** 472 unittest (+8 #115 tests) + 201 pytest adapters + spec_consistency + preprint_venues all green.

### #105 — v3.7.3 contamination_signals backfill migration tool (2026-05-15)

**Parent issue:** [#105](https://github.com/Imbad0202/academic-research-skills/issues/105). Spec anchor: v3.7.3 §3.2 R-L3-2-B (the deferred batch operation; bibliography_agent computes signals at ingest, this tool delivers post-hoc backfill on legacy corpora). Design: `docs/design/2026-05-15-issue-105-contamination-signals-backfill-design.md`.

**New files:**

- `scripts/contamination_signals.py` — two pure-function resolvers + emission rules + `SemanticScholarClient` protocol. `compute_preprint_signal()` (Signal 1, deterministic year+venue check against 10-server closed list). `compute_ss_unmatched_signal()` (Signal 2, dependency-injected SS client, returns `None` on manual exemption + API degradation per spec).
- `scripts/migrate_literature_corpus_to_v3_7_3.py` — CLI tool: `[--dry-run] [--verbose] <passport_or_dir>`. Uses `ruamel.yaml` round-trip to preserve comments + key order + quoting style. Reports `processed / patched / skipped_already_migrated / skipped_insufficient_data` counts. Idempotent.
- `scripts/test_contamination_signals.py` — 25 unit tests covering Signal 1 (15 cases: 10 preprint venues × year boundary, non-preprint venue, missing year, missing venue), Signal 2 (6 cases: manual exemption / match / no-match / API degradation × 2 paths / unexpected exception), emission rules (4 cases).
- `scripts/test_migrate_literature_corpus_to_v3_7_3.py` — 9 unittest cases covering dry-run, full migration per emission rules, idempotency, insufficient-data skip, empty-corpus passport, directory scan (non-recursive), comment preservation.
- `docs/migration/v3.7.3-contamination-signals-backfill.md` — user-facing migration guide (when to run, dry-run workflow, idempotency, SS API rate-limit considerations, what's out of scope).

**Modified files:**

- `shared/contracts/passport/literature_corpus_entry.schema.json` — purely additive: new optional `contamination_signals_backfilled_at` field (ISO-8601 date-time string). Existing v3.7.3 ingest-time entries (which lack this field) remain valid; pre-v3.7.3 entries (which lack both this field and `contamination_signals`) remain valid.
- `scripts/adapters/tests/test_literature_corpus_entry_schema.py` — 3 new tests for the additive field (valid present / absent / non-string rejected).
- `requirements-dev.txt` — add `ruamel.yaml>=0.17`.

**Open-question resolutions (user-chosen 2026-05-15):**

- Q1 API rate-limit handling: backoff-only via existing SS protocol (429 → 2s × 3); no resumable checkpoint (YAGNI per minimal scope)
- Q2 schema field naming: scalar `contamination_signals_backfilled_at` ISO-8601 timestamp; strictly additive upgrade path if v3.7.4 needs structured provenance
- Q3 multi-passport batch mode: directory-scan only; no `--input-list` (YAGNI)
- Q4 YAML library: `ruamel.yaml` round-trip to preserve user-owned passport formatting (memory `feedback_toml_duplicate_table_corruption` spirit)

**Spec discipline (per v3.7.3 R-L3-2-B):**

- Migration is offline + opt-in: user explicitly invokes; pipeline doesn't auto-trigger
- Idempotency keyed on `contamination_signals` presence: first-migration timestamp preserved across re-runs
- `obtained_via=manual` exemption preserved at migration time (semantic_scholar_unmatched field omitted, matches the v3.7.3 schema cross-field rule)
- API degradation → field omitted (NOT set to False, per "absence ≠ negative confirmation" rule)

**Files explicitly NOT touched:**

- `deep-research/agents/bibliography_agent.md` — v3.7.3 ingest-time computation frozen
- `academic-pipeline/agents/pipeline_orchestrator_agent.md` — finalizer behavior unchanged
- Existing `scripts/adapters/*` — adapters produce ingest-time entries; migration is downstream

**Regression status:** 1053 #108 baseline + 17 #111 baseline + 25 resolver + 9 migration + 3 schema = 1107 total. All green. No regression on the existing 4 `allOf` cross-field invariants (manual exemption + preprint year=2024 boundary verified by adapter pytest).

### #104 — README motivation: add Zhao et al. corpus-scale evidence anchor (2026-05-15)

**Parent issue:** [#104](https://github.com/Imbad0202/academic-research-skills/issues/104). Doc-only — no code changes.

Adds a third evidence anchor to the `### Why human-in-the-loop, not full automation?` README section, between the ARS positioning paragraph and the PaperOrchestra paragraph. Closes the gap where v3.7.x trust-and-locator machinery appeared in the codebase without its corpus-scale motivation surfaced in the public-facing README.

**Modified files:**

- `README.md` — new Zhao et al. paragraph
- `README.zh-TW.md` — translated equivalent

**Three motivation anchors now read in sequence:**

- Lu et al. (Nature 651:914-919) — case-study evidence of autonomous-pipeline failure modes
- Zhao et al. (arXiv:2605.07723) — corpus-scale evidence of the citation-faithfulness problem (111M references / 2.5M papers / 146,932 conservative 2025 estimate / mid-2024 inflection / 85.3% bioRxiv-to-PMC persistence)
- PaperOrchestra (Song et al., arXiv:2604.05018) — method-level technique source

**Discipline (#104 acceptance criteria):**

- Statistics verified directly against Zhao et al. abstract (111M / 2.5M / 146,932 / conservative qualifier) + v3.7.3 spec which carries the body-level numbers (85.3% bioRxiv→PMC specificity, mid-2024 inflection) through prior 10-round codex + gemini cross-model review.
- No claims that v3.7.x "closes" L3 — only "adds locator infrastructure" / "advisory risk signals".
- L3 attributed to ARS terminology, not the paper's.
- "Motivated by" not "responds to".

### #111 — slr_lineage emission on systematic-review → academic-paper full handoff (2026-05-15, unreleased)

**Parent issue:** [#111](https://github.com/Imbad0202/academic-research-skills/issues/111), follow-up to #108 (PR #110, merged 70c8678) round-8 P2 #1. Design: `docs/design/2026-05-15-issue-111-slr-lineage-emission-design.md`.

> Version label `v3.7.4` below is provisional and will be confirmed at the next release sweep per `feedback_version_bump_sweep_checklist.md`. If this work ships as part of v3.7.3 (the in-progress release at writing time), the version stamps in this entry and the prose files below are swept to the final label at release tag.

Closes the pipeline-plumbing gap surfaced by #108: `disclosure --policy-anchor=prisma-trAIce` now dispatches automatically when the documented `deep-research systematic-review → academic-paper full → disclosure` path runs, without the user manually supplying `mode=systematic-review` at cold-start.

**New files added:**

- `scripts/slr_lineage.py` — two pure functions: (a) `resolve_from_stages(stages)` returns `True` iff any stage was produced by `deep-research` in systematic-review mode (bound to the deep-research producer specifically — a non-deep-research stage carrying mode='systematic-review' does NOT trigger SLR lineage); (b) `emit(stages, incoming_slr_lineage)` is the monotonic-OR wrapper the orchestrator calls at every handoff. The OR preserves any signal already persisted on the incoming passport (load-bearing for `resume_from_passport=<hash>` sessions whose `state_tracker.stages` is empty — codex round-1 [P2] closure).
- `scripts/test_slr_lineage_emission.py` — 17 conformance tests: resolver semantics (7 cases: positive / non-SLR / mid-entry / empty / alias `slr` / non-deep-research / missing-mode), renderer integration (3 cases: pipeline-emitted dispatches without `mode_param` / non-SLR still blocks / pre-#111 cold-start fallback preserved), end-to-end pipeline handoff (2 cases), and monotonic-OR emit semantics (5 cases: resume preserves true / in-session false-to-true / no-evidence false / None incoming / default arg ergonomics).

**Modified files:**

- `shared/handoff_schemas.md` — Schema 9 Material Passport gains optional top-level `slr_lineage: boolean` row + dedicated "Run-level lineage signal (v3.7.4)" subsection documenting semantics, producer, consumer, backward compat, and G1 boundary note (passport-level vs corpus-entry-level distinction).
- `academic-pipeline/agents/pipeline_orchestrator_agent.md` — §4 Transition Management gains a "Run-level lineage emission (v3.7.4+)" step computed at every handoff transition before dispatch. Passport carry-line updated to reference `slr_lineage` from v3.7.4+.

**Files explicitly NOT touched (matches #111 §Scope out-of-scope):**

- `scripts/policy_anchor_disclosure_referee.py` — #108 referee, contract unchanged
- `academic-paper/references/policy_anchor_disclosure_protocol.md` — #108 protocol, unchanged
- `academic-paper/references/policy_anchor_table.md` — #108 anchor table, unchanged
- `academic-paper/references/disclosure_mode_protocol.md` — already references `slr_lineage` as pipeline-supplied
- `shared/contracts/passport/literature_corpus_entry.schema.json` — G1 invariant frozen (corpus entry schema, not passport schema)

**G1 boundary clarification:** Decision Doc §4.4 #11 G1 invariant scope is `literature_corpus_entry.schema.json` (corpus entry data schema). Schema 9 Material Passport top-level extensions follow the v3.6.3 (`reset_boundary[]`) / v3.6.4 (`literature_corpus[]`) / v3.6.7 (`audit_artifact[]`) precedent and are permitted per Decision Doc §4.4 #11's "non-renderer code changes for §4.4 concerns are permitted" provision.

**Backward compat:** passports written by pre-v3.7.4 runs lack the `slr_lineage` field; renderer treats absence as `false` (cold-start path requiring explicit `mode_param='systematic-review'`). Identical to pre-v3.7.4 behavior.

**Regression status:** 1053-baseline frozen (no #108 contract drift); +17 new tests cover this issue's acceptance criteria #1-#3 plus codex round-1 [P2] (monotonic-OR emit across resume).

### #108 — AI disclosure policy-anchor renderer (2026-05-14, audit-trail-shipped)

**Parent docs:** Decision Doc (`docs/design/2026-05-14-ai-disclosure-schema-decision.md`, PR #109, merged commit 20ed72d) + implementation spec (`docs/design/2026-05-14-ai-disclosure-impl-spec.md`).

**Migration note (G1 + G6 invariants):** **no migration required**. Decision Doc §2.1 G1 invariant: no `ai_disclosure` field is added to `shared/contracts/passport/literature_corpus_entry.schema.json`. Decision Doc §3 G6: no deprecation horizon — legacy entries (which by §1 fact-check do not carry any AI-disclosure field today) stay byte-equivalent. The implementation extends the runtime renderer path, not the data schema.

**New files added:**

- `academic-paper/references/policy_anchor_table.md` — 4-anchor (PRISMA-trAIce / ICMJE / Nature / IEEE) × 16-field source-of-truth reference table carrying verbatim policy quotes lifted from discovery doc §4.3-4.6 (PR #107, commit 299c4b6) + per-anchor renderer rules.
- `academic-paper/references/policy_anchor_disclosure_protocol.md` — LLM-prose runtime protocol for the new `--policy-anchor=<a>` track: 7-section flow covering inputs / G10 7-row precedence table / per-anchor render flows / auto-promotion forbiddance / venue-anchor conflict resolution / three-state completeness flag / 11-concern resolution map.
- `shared/policy_data/nature_policy.md` — canonical Nature substantive policy source; both the policy-anchor track and the v3.2 venue track cross-reference this path for the G4 dedup invariant.
- `scripts/check_policy_anchor_table.py` + `scripts/test_check_policy_anchor_table.py` — anchor table structural lint with 13 mutation tests + Nature dedup guard wired into the main lint command.
- `scripts/check_policy_anchor_protocol.py` + `scripts/test_check_policy_anchor_protocol.py` — protocol doc lint with 12 mutation tests covering §4.3 8 invariants + §4.4 11 concerns + G10 7-row precedence table + auto-promotion forbiddance + anchor inventory closed-enum.
- `scripts/policy_anchor_disclosure_referee.py` + `scripts/test_policy_anchor_disclosure.py` — executable specification (referee) of §3 G10 7-row decision table + 8 invariant predicates; 61 conformance tests covering every (input × expected output) combination + forbidden-path negative fixtures.

**Modified files:**

- `academic-paper/references/disclosure_mode_protocol.md` — `--policy-anchor=<a>` track added in parallel to v3.2 `--venue=<v>` track. Phase 1 dispatch becomes selector-aware (step 1a / step 1b venue / step 1c anchor). Venue-only flow unchanged; anchor flow delegates Phase 3+4 to `policy_anchor_disclosure_protocol.md`. Concern #7 venue+anchor conflict resolution enforced.
- `academic-paper/references/venue_disclosure_policies.md` — Nature entry gains derivation note + dedup pointer to `shared/policy_data/nature_policy.md`. v3.2 venue rendering content unchanged (derived view, manual sync to canonical source until future refactor).
- `.github/workflows/spec-consistency.yml` — 5 new CI steps wiring the new validators and conformance test suite into the existing spec-consistency job.

**§4.4 11 open concerns resolved** (4 user-chosen, 7 inline; full table in impl spec §3):
1. Track-selection lookup: explicit `slr_lineage` input from pipeline orchestrator (user-chosen).
2. Tool identity collection: auto-detect from session metadata (mirror v3.2 Phase 4).
3. Prompt scope: per-(tool × task) tuple per PRISMA M6.a.
4. IEEE section locator: free-form list with recommended IMRaD exemplars.
5. Nature image metadata: hybrid output channel (annotation block + suggested inline patches) (user-chosen).
6. UNCERTAIN per-facet finalization: USED-full + per-facet annotation alongside still-UNCERTAIN (user-chosen).
7. Venue+anchor conflict: reject conflicting selectors with explicit error.
8. Three-state completeness flag: full computation logic encoded in §6 of protocol doc.
9. Test set scope: 86 new tests covering 8 invariants + 10 concerns × {positive, negative}.
10. `ai_used:true` substantive-content gate: force v3.2 categorization flow (user-chosen).
11. G1 invariant scope: data layer untouched; non-renderer pipeline plumbing permitted.

**Known follow-up (out of #108 scope):** the academic-pipeline orchestrator does not yet emit `slr_lineage` on the documented `systematic-review → academic-paper full` handoff. Authors targeting `--policy-anchor=prisma-trAIce` must supply `mode=systematic-review` manually until that plumbing lands in a separate PR (touches `academic-pipeline/` + `shared/handoff_schemas.md`, outside §4.1 items 1-5 NO-CHANGE boundary).

**Regression status:** 967 baseline + 86 new tests = 1053 passing / 3 skipped / 0 failed. Public-repo boundary clean. Eight rounds of codex gpt-5.5 xhigh review (R1 4 P2 → R8 2 P2); shipped audit-trail-complete per user decision rather than pushing past Decision Doc 11-round high water mark. R8 P2 #1 captured as the known follow-up above.

### v3.7.3 — claim faithfulness locator + contaminated-source advisory (2026-05-12, in progress)

**External motivation:** Zhao, Wang, Stuart, De Vaan, Ginsparg, Yin "LLM hallucinations in the wild: Large-scale evidence from non-existent citations" (arXiv:2605.07723, 2026-05). Corpus-scale audit of 111M references across 2.5M papers across arXiv / bioRxiv / SSRN / PMC finds 146,932 hallucinated citations estimated for 2025 alone, with the inflection point at mid-2024, 85.3% of preprint hallucinations surviving into the published record, and Google Scholar increasingly indexing citation-only entries. The paper names the L3 (claim faithfulness) gap explicitly: *"real citations deployed to support claims the cited references do not actually make ... remains an open challenge for which reliable detection methods remain under active development."* v3.7.3 closes the locator-channel half of that gap (anchor infrastructure for future L3 audit) and surfaces two contamination signals (preprint post-LLM-inflection + Semantic Scholar unmatched) as advisory cite-time markers.

**L3-1 — Three-Layer Citation Emission (claim faithfulness locator):**

- `deep-research/agents/synthesis_agent.md`, `academic-paper/agents/draft_writer_agent.md`, `deep-research/agents/report_compiler_agent.md` gain `## Three-Layer Citation Emission (v3.7.3)` H2 section that extends v3.7.1 Two-Layer with a third hidden marker: `<!--anchor:<kind>:<value>-->` where `<kind>` ∈ `{quote, page, section, paragraph, none}`. Production-mandatory locator rule (R-L3-1-A) requires `<kind>` ≠ `none` for every visible citation; emitting `none` triggers finalizer MED-WARN-NO-LOCATOR (gate-refused). Quote anchors capped at 25 words by whitespace split (R-L3-1-B). Anchor values come from corpus context only — no frontmatter reads (R-L3-1-C, inherits v3.6.7 partial-inversion discipline).
- `academic-pipeline/agents/pipeline_orchestrator_agent.md` gains a `## Cite-Time Provenance Finalizer — v3.7.3 extension` H2 section: 4-cell matrix becomes 5-cell along a new precedence-zero locator-presence axis. NO-LOCATOR resolution: `[UNVERIFIED CITATION — NO QUOTE OR PAGE LOCATOR]<!--ref:slug--><!--anchor:none:-->`.
- `academic-paper/agents/formatter_agent.md` gains a `## Cite-Time Provenance Hard Gate (v3.7.1 + v3.7.3)` section formalizing the terminal hard-gate refusal across all three v3.7.x severity tiers (HIGH-WARN-NO-ORIGINAL, MED-WARN-NOT-CROSS-CHECKED, MED-WARN-NO-LOCATOR).

**L3-2 — Contaminated-source advisory signals:**

- `shared/contracts/passport/literature_corpus_entry.schema.json` adds optional `contamination_signals: { preprint_post_llm_inflection, semantic_scholar_unmatched }` object. Both sub-fields optional within the object; both default to absent (signals not computed). `additionalProperties: false` enforced on the sub-object. Backward compat: entries without the field stay valid.
- `deep-research/agents/bibliography_agent.md` gains `## Contamination Signal Computation (v3.7.3)` section. Signal 1 (`preprint_post_llm_inflection`): `year >= 2024 AND venue ∈ {arXiv, bioRxiv, medRxiv, SSRN, Research Square, Preprints.org}`. Signal 2 (`semantic_scholar_unmatched`): existing Semantic Scholar API protocol returns no match by DOI or title; exempted when `obtained_via: manual`; omitted (not `false`) on API degradation.
- Pipeline finalizer (in pipeline_orchestrator) annotates `ok` / `LOW-WARN` markers with `CONTAMINATED-PREPRINT` / `CONTAMINATED-UNMATCHED` / `CONTAMINATED-PREPRINT+UNMATCHED` suffix per `contamination_signals` state. Annotations are **advisory only** — they do NOT change the gate decision (v3.5 Collaboration Depth Observer precedent).

**Lint + tests:**

- New `scripts/check_v3_7_3_three_layer_citation.py` static lint: every `<!--ref:slug-->` must be followed by `<!--anchor:<kind>:<value>-->`; `quote` values ≤25 words; orphan anchors rejected.
- New `scripts/test_check_v3_7_3_three_layer_citation.py`: 14 tests covering positive (5 kinds × passing cases, contamination-suffix marker, LOW-WARN-resolved marker, multi-citation) + negative (bare ref, orphan anchor, invalid kind, 26-word quote).
- New 6 contamination_signals tests in `scripts/adapters/tests/test_literature_corpus_entry_schema.py`: absence / empty / both-false / both-true / unknown-subfield-rejected / non-boolean-rejected.
- New `V373ExtensionLineBudgetTest` in `scripts/test_v3_6_7_phase_6_6.py`: 60-line budget for `## Cite-Time Provenance Finalizer — v3.7.3 extension` block; existing Phase 6.6 +60 v3.6.7 budget test updated to subtract both v3.7.1 Step 3b AND v3.7.3 extension lines.

**Regression status (final, post round-10 convergence):** 967 tests pass, 3 skipped, 0 failed (42 new tests across rounds 1-10 fixes; pre-review baseline was 925). v3.6.7 + v3.6.8 + v3.7.1 + v3.7.2 lints all PASS unmodified. v3.6.7 PATTERN PROTECTION blocks remain byte-equivalent (SHA gate v2 unchanged). Material Passport literature_corpus_entry schema backward compatible (new contamination_signals field optional; cross-field rules only fire when explicitly set). New v3.7.3 lint wired into spec-consistency.yml CI workflow per F18.

**Cross-model review closure (2026-05-12, 11 rounds total — 10 codex + 1 gemini cross-model):**

| Round | Reviewer | Findings | Closures |
|---|---|---|---|
| 1 (initial) | Codex | 0 P1 / 2 P2 | F3 (untracked artifacts → closed at commit), F4 (NO-LOCATOR acknowledgment contradiction → removed `/ars-mark-read` promise from formatter+finalizer+spec Q5) |
| 1 (initial) | Gemini 3.1-pro-preview | 2 P1 / 2 P2 / 1 P3 | F1 (hyphen-encode → 3 prompts + lint + 3 tests), F2 (whitespace/newline tolerance → finalizer clarification + 4 tests), F5 (year<2024 schema cross-field → allOf + 4 tests), F6 (venue list 6 → 10 added ChemRxiv / EarthArXiv / OSF Preprints / TechRxiv), F7 (fenced code block isolation → helper + 4 tests) |
| 2 | Codex | 0 P1 / 2 P2 | F8 (lint regex widened to {0,2} suffix tokens → 3 tests), F9 (empty non-`none` anchor value rejection → 5 tests) |
| 3 | Codex | 0 P1 / 2 P2 | F10 (premature HTML comment terminator sentinel scan → 3 tests), F11 (schema manual-entry exemption → 4 tests) |
| 4 | Codex | 0 P1 / 1 P2 / 1 P3 | F12 (orphan_pattern lookbehind removed → 3 tests), F13 (schema venue list description sync 6 → 10) |
| 5 | Codex | 0 P1 / 1 P2 | F14 (malformed ref broad-scan detector → 4 tests) |
| 6 | Codex | 0 P1 / 1 P2 | F15 (prompt-vs-lint alignment on `--` rule → 2 tests; prompts loosened to match lint's narrower contract) |
| 7 | Codex | 0 P1 / 3 P2 | F16 (finalizer status-suffix-tolerant for revision-loop reruns), F17 (standalone deep-research self-gate), F18 (CI workflow wires v3.7.3 lint into spec-consistency.yml) |
| 8 | Codex | 0 P1 / 3 P2 | F19 (decode value before empty check → 3 tests), F20 (formatter raw `anchor:none` gate), F21 (F17 self-gate scoped to standalone mode only via prompt mode-detection) |
| 9 | Codex | 0 P1 / 1 P2 | F22 (self-gate also rejects bare refs without anchor — parity with pipeline finalizer's precedence-zero "no anchor = anchor=none" rule) |
| **10 (final)** | **Codex** | **0 findings** | **Convergence achieved.** |

- **No cross-finding overlap across reviewers.** Codex and Gemini found complementary defect classes — Codex caught contract gaps + regex completeness + architectural integration; Gemini caught HTML comment parsing edge cases + cross-field schema rules + venue completeness. This is the canonical value split documented in `feedback_codex_workflow_consolidated.md`.
- **Cascade pattern:** each round's closure introduced no new defects in its OWN scope, but interactions with other v3.7.3 surfaces surfaced new layers — F19 was an F9 layer (encoded-whitespace bypass after the F9 raw-value fix), F21 was a F17 regression (self-gate ran in pipeline mode and interfered with finalizer), F22 was an F17+F21 boundary (only catching explicit `none` markers missed bare-ref legacy form). The 10-round convergence trajectory is consistent with the v3.6.8 18-round implementation precedent and `feedback_complex_spec_review_inventory_pattern.md`.
- **F23+ not yet observed.** Round 10 returned no findings on the 9th amended branch state, providing the convergence signal. Future codex challenge mode (adversarial scope) may surface architecturally deeper gaps; tracked separately as a v3.7.4+ concern.

**Out of v3.7.3 scope (tracked as follow-up issues):**

- v3.7.4 retrieval-side hardening: OpenAlex + Crossref triangulation as second contamination signal (Vector 2 currently single-source via Semantic Scholar only).
- v3.8 L3 full audit: `claim_ref_alignment_audit_agent` running LLM-as-judge over (claim, ref full-text) pairs. v3.7.3 anchors are the input; v3.8 verifies anchor content faithfulness.
- AI disclosure schema split (per-stage: drafting / editing / **reference suggestion** / data analysis) — Zhao et al. Fig. 1l correlates AI-writing-signature with hallucination rate.
- Public README motivation update citing arXiv:2605.07723.
- Migration tool for legacy `literature_corpus[]` entries lacking `contamination_signals`.

Spec: `docs/design/2026-05-12-ars-v3.7.3-claim-faithfulness-and-contaminated-source-spec.md`.

### Backlog — gbrain harness borrow analysis (2026-05-10, post codex review)

Source: 2026-05-10 analysis of `garrytan/gbrain` (14.2k★ agent harness for OpenClaw/Hermes), with codex cross-model review same day. Two candidates surfaced; they have different risk profiles and are tracked separately.

**Candidate A — Shared `shared/_invariants.md` cross-skill rules file** (gbrain pattern P3). Status: backlog, low-risk.

ARS cross-cutting rules are scattered today: Iron Rules in adapter overview, hedging contract in `protected_hedging_phrases.md`, citation precedence in agents' frontmatter, integrity gates referenced from multiple SKILL.md. When a rule evolves (e.g. v3.6.5 corpus protocol Iron Rules), secondary mentions drift.

Shape if adopted:
- `shared/_invariants.md` enumerating **positive invariants only** (no rejected-reasoning column; that was the contamination vector in the 2026-05-10 anti-pattern-table evaluation)
- File stays short, normative, and example-free — additional examples turn invariants into demonstrations and re-introduce few-shot drift
- Each SKILL.md references it via a stronger convention than `## See Also` (which reads as optional reading); proposed wording at adoption time
- Frontmatter `validated_against: <version>` enables a stale-reference grep job on minor bumps. **The grep job detects version drift only — it does NOT validate semantic compliance.** Semantic checks remain a human / codex review responsibility.

**Candidate B — Declarative `shared/_review_pairs.yaml` cross-model review config** (gbrain pattern P6). Status: **needs design spike before becoming a real candidate**, higher-risk.

ARS cross-model review is currently invoked imperatively: `ARS_CROSS_MODEL=1` env flag + manual codex review per phase. A declarative `(deliverable_kind, reviewer_model, dimensions, when_to_invoke)` map could improve reproducibility for Stage 2.5 / 4.5 integrity gates and Phase 6 in-pair evaluator review.

Three open problems before this is shippable:
1. **Refusal-routing semantics conflict.** gbrain's chain (primary → DeepSeek → Qwen → Groq, silent switch) routes past refusal; ARS treats reviewer disagreement as signal. Borrowing the YAML format without resolving this imports the wrong invariant. Likely answer is "borrow the declarative-pairing shape, drop the refusal-routing chain entirely."
2. **Embedding governance in config.** A YAML that decides "this deliverable triggers this reviewer with these dimensions" is workflow policy. Wrong shape locks in a bad routing decision across all phases. Needs a usage survey of existing manual invocations before designing the schema.
3. **Lower confidence than Candidate A.** ARS already has review phases and cross-model invocation working manually; the missing piece is reproducibility, not the capability. If manual invocation isn't causing missed reviews or inconsistent reviews in practice, this should drop too.

Rejected from same gbrain analysis: P1 RESOLVER.md dispatcher (10 slash commands serve dispatch), P4 trust boundary (research tool, no untrusted caller class), P5 pain-triggered subagent routing (covered in user CLAUDE.md, repo-level not relevant). **P2 friction protocol** is a soft reject — codex review pointed out a first-class friction CLI captures pain at the moment of pain, which 5+ round codex review at deliverable-time does not. Re-examine if ARS skill development surfaces recurring author-time pain that retrospective review doesn't capture.

Meta-lesson from this analysis: "we already do something adjacent" is weaker than it sounds as a reject reason. The test is whether the existing mechanism captures the same signal at the same time with the same enforcement strength.

### Added (v3.6.7 Step 6 Phase 6.8 — Step 8 evaluation case)

- **17 micro-fixtures + 1 chapter-level integration fixture** under
  `tests/fixtures/v3_6_7_pattern_eval/` exercising the 17 numbered downstream
  -agent patterns (A1–A5, B1–B5, C1–C3, D1–D4) per spec §7. Each micro
  fixture: `manifest.json` (`fixture_kind: "micro"`) + `upstream_context/`
  (`passport_snippet.yaml` + `prior_artifacts/`) + `bad_run/` + `good_run/`
  with `deliverable.md`, `expected_audit_findings.yaml`,
  `expected_orchestrator_action.yaml`. Integration fixture under
  `integration/chapter_level_run/` exercises A3+C2+D4+C1 across 3-round
  MATERIAL escalation → ship_with_known_residue acknowledgement per §7.3.
- **`scripts/check_pattern_eval_manifest.py`** — fixture_kind discriminator
  routing micro (§7.2) vs integration (§7.3) JSON Schema 2020-12 manifest
  schemas; `audit_verdict.schema.json` validation on every
  `expected_audit_findings.yaml`; path-safety rejects absolute paths and `..`
  segments; coverage cross-check enforces 17/17 numbered IDs covered (with
  hard-fail on unknown directory names per §7.5).
- **`scripts/test_pattern_eval_runtime.py`** — 112-test parametrized harness
  reading expected verdicts as synthesized output and asserting against
  expected orchestrator action. Per-pattern parametrized tests (BAD signal +
  GOOD passes + run_id F1 regex + BAD/GOOD uniqueness); integration state
  runner driving §7.3 5-step procedure (load verdicts → drive §5.6 → verify
  pipeline state per round → feed escalation user_response → verify final
  passport state); Path A re-verification axis (≥6 A7 happy-path legs at
  rounds 2+3); finding-id lineage carry-forward per audit-template Section 6;
  per-phase synthetic injections (24 of 26 PHASE_TO_PASSPORT_MUTATION rows
  validated for "none" / "appended"); A1.5 supersession-preflight axis tests.
- **`scripts/test_run_codex_audit_e2e.py`** — Phase 6.1 deferred end-to-end
  dispatch test (Linux Bash 4+ only; macOS stock Bash 3.2 self-skips). Mocks
  codex CLI via PATH-prefix shim emitting canonical Phase 2 JSONL stream.
  Validates wrapper produces 4 contract files + 3 diagnostic files; proposal
  entry validates against `audit_artifact_entry.schema.json --mode proposal`
  (Pattern C3 defense — `verified_at`/`verified_by` absent); `--dry-run`
  writes nothing; `--round=2` without `--previous-findings` rejected with
  `EX_USAGE`.
- **`.github/workflows/spec-consistency.yml`** — 4 new CI steps: Phase 6.8
  manifest validation, pattern-eval-unit (micro fixtures + phase inventory +
  synthetic non-supersession), pattern-eval-integration (integration fixture
  + synthetic supersession), Phase 6.1 wrapper E2E (Linux runner only).
- **`docs/design/TODO-l-doc-1-18-patterns-prose-retirement.md`** — files
  L-doc-1 follow-up enumerating 8 retirement locations for the docs-only PR
  retiring "18 patterns" prose to "17 patterns" per §9.2.
- **Spec amendments** at `docs/design/2026-04-30-ars-v3.6.7-step-6-orchestrator
  -hooks-spec.md`: §7.4 success criterion 1 prose updated for C2 MINOR
  special case + D2 PASS convergence-policy assertion; §7.4 phase example
  updated `escalation` → `B11`; §7.6 deployment note explaining named-step
  CI deployment (vs literal "two separate jobs"); §9.2 L-doc-1 row points at
  the TODO file; §7.3 example manifest snippet updated to F-101/F-103.

### Notes

- **11 codex review rounds converged to 0 findings**. Cumulative 24
  findings closed (4 P1 + 18 P2 + 2 P3) across rounds 1-10.
- 135 Phase 6.8-specific tests; total repo regression 742 pytest + 251
  unittest = 993 green + 3 skipped (macOS Bash 3.2 wrapper E2E gate).
- v3.6.7 Step 6 + Step 8 now structurally complete: prompt-level pattern
  protection (Step 1+2) + version sweep (Step 7) + runtime audit-artifact
  gate (Step 6 §1-§11 + Phases 6.1-6.7) + synthetic evaluation case
  (Phase 6.8) deliver the §10 ship-quality target.

## [3.7.0] - 2026-05-05

> **Claude Code plugin packaging.** ARS now installs in one line on Claude Code
> CLI / VS Code / JetBrains via `/plugin marketplace add Imbad0202/academic-research-skills`
> + `/plugin install academic-research-skills`. The traditional
> `git clone + symlink to ~/.claude/skills/` flow continues to work — both
> tracks are first-class.

### Added

- **Plugin manifest + marketplace metadata** (Phase 1, PR #68).
  `.claude-plugin/plugin.json` declares the suite. `.claude-plugin/marketplace.json`
  registers the plugin so a single GitHub-hosted endpoint serves both the
  marketplace listing and the plugin source. `skills/` directory carries
  relative symlinks to the four existing skill directories so the plugin
  loader auto-discovers them without moving repo layout.
- **10 slash commands** at `commands/ars-*.md` (Phase 2.1, PR #69) mapping
  `MODE_REGISTRY.md` entries to `/ars-<mode>` triggers. Model routing pinned
  in each command's frontmatter — `opus` for `full` and `revision-coach`
  (architectural / review-interpretation depth), `sonnet` for the other 8.
  No Haiku per `feedback_no_haiku.md`.
- **3 plugin-shipped agents** at `agents/*_agent.md` (Phase 2.1, PR #69)
  as relative symlinks to the v3.6.7-hardened downstream agents in
  `deep-research/agents/`: `synthesis_agent`, `research_architect_agent`,
  `report_compiler_agent`. Underscore filenames preserved to match
  `scripts/check_v3_6_7_pattern_protection.py` hard-pinned paths and the
  INV-3 manifest-confined Clause 1 invariant. Symlinks (not copies) preserve
  a single source of truth and prevent the Pattern C3 attack surface that
  v3.6.7 §6 inversion sweep + INV-1/2/3 lint closes.
- **`model: inherit`** added to those three source agent frontmatters
  (PR #69 R1 codex finding). Inherit chosen over pinning `sonnet` so an
  Opus session running the full pipeline keeps Opus agents (instead of
  being capped) while the user's existing PreToolUse `warn-agent-no-model.sh`
  hook gates Haiku at the dispatch boundary.
- **SessionStart announce hook** at `hooks/hooks.json` +
  `scripts/announce-ars-loaded.sh` (Phase 2.2, PR #70). When the plugin
  loads, the hook injects `additionalContext` listing the 10 slash commands,
  the 3 plugin agents, and a token-budget pointer into the LLM's first
  turn. `startup` and `clear` source values get the full announce; `resume`
  and `compact` get a one-line ack to avoid burning context on every
  resume. Bash 3.2 compatible — runs on macOS stock `/bin/bash` with no
  `brew install bash` requirement. `${CLAUDE_PLUGIN_ROOT}` quoted for
  install paths containing spaces.
- **`docs/PERFORMANCE.md` + `.zh-TW.md`** subsection
  "v3.7.0 Plugin agents and model routing" explaining `model: inherit`
  semantics and the current 3-agent scope boundary.
- **`docs/ARCHITECTURE.md`** Evolution Timeline extended with v3.6.7 / v3.6.8 /
  v3.7.0 entries.
- **README + README.zh-TW** version badge bumped to v3.7.0; Pipeline section
  heading bumped to v3.7; CHANGELOG entry added.

### Deferred (future release)

- **SubagentStop → `run_codex_audit.sh` codex audit hook** (Phase 2.2 scope
  reduction). Two compounding reasons: (a) wrong invoker class —
  `run_codex_audit.sh` lines 4–7 forbid same-session in-LLM invocation
  (Pattern C3 attack surface), and the original PostToolUse Write|Edit
  matcher would fire from inside the producing session; (b) contract gap —
  the SubagentStop hook payload carries no stage/deliverable info, so a
  wrapper would have to half-infer those required arguments. Real
  audit-hook integration deferred to a future release when ARS gains a stage/deliverable
  propagation contract. See
  `docs/design/2026-04-30-ars-v3.7.0-plugin-packaging-roadmap.md`
  Update note 2026-05-05 (Phase 2.2 scope reduction).

### Changed

- `academic-pipeline/SKILL.md` frontmatter `version: "3.7.0"` + H1 +
  Version Info table.
- `MODE_REGISTRY.md` Last updated bumped to `v3.7.0 (2026-05-05)`.
- `.claude/CLAUDE.md` Skills Overview row + Suite version footer bumped
  to 3.7.0.
- `scripts/check_spec_consistency.py` lint pins (Suite version, README
  badge, MODE_REGISTRY heading, CHANGELOG section heading) bumped to
  v3.7.0.

### Unchanged

The four skill directories, all 25 modes, agent prompts, schema files,
and lint contracts. Plugin packaging only adds new top-level surface
(`commands/`, `agents/`, `hooks/`, `.claude-plugin/`, `skills/` symlink
dir, three plugin-agent `model: inherit` frontmatter additions).
Existing 4.3k clone-install users see no breaking change.

### Codex review chain

8 inline iterative rounds + 3 fresh PR-level rounds across the three
PRs (#68 / #69 / #70), all converging to 0 P0/P1/P2 findings before
merge. The Phase 2.2 fresh PR review caught one P2 (unquoted
`${CLAUDE_PLUGIN_ROOT}` breaking install paths with spaces) that the
inline rounds missed — confirms the value of separating implementation
review (inline) from contract / install-time review (fresh).
Reference: `feedback_codex_review_vs_resume_audit_scope.md`.

## [3.6.8] - 2026-05-03

> **Naming note**: this release ships the **v3.6.6 generator-evaluator contract**
> spec (`docs/design/2026-04-27-ars-v3.6.6-generator-evaluator-contract-design.md`)
> and its implementation. The v3.6.6 work landed after v3.6.7 due to project
> sequencing; the design doc retains the v3.6.6 internal naming for the
> contract gate version (`writer_full` / `evaluator_full` mode, Schema 13.1,
> `pre_commitment_artifacts` + `disagreement_handling` schema fields), while
> the suite release is tagged v3.6.8 to keep the CHANGELOG monotonic.

### Added

- **Schema 13.1 generator-evaluator contract gate** for `academic-paper full`
  mode (`shared/sprint_contract.schema.json`, design doc §3): two new `mode`
  enum values (`writer_full` + `evaluator_full`); two new optional top-level
  fields (`pre_commitment_artifacts` writer-only with
  `acceptance_criteria_paraphrase.minimum_dimensions`; `disagreement_handling`
  evaluator-only with `paraphrase_minimum_dimensions` + `scoring_plan` +
  `pre_commitment_check_protocol` + `disagreement_resolution`); 12 `allOf`
  branches enforcing reviewer- / writer- / evaluator-conditional gates
  (existing 2 + 10 new per design doc §3.5 table).
- **Two new shipped contract templates**: `shared/contracts/writer/full.json`
  (writer dimensions D1 section_completeness / D2 citation_density /
  D3 argument_blueprint_fidelity / D4 total_word_count /
  D5 per_section_word_count / D6 acknowledged_limitations /
  D7 register_consistency; F-conditions F1/F4/F2/F3/F0; no `scoring_plan`)
  and `shared/contracts/evaluator/full.json` (evaluator dimensions
  D1 originality / D2 methodological_rigor / D3 evidence_sufficiency /
  D4 argument_coherence / D5 writing_quality; F-conditions F1/F2/F3/F6/F4/F5/F0;
  full `scoring_plan` + `disagreement_handling`). Templates already shipped on
  the spec branch as design-time artefacts since 2026-04-28; this release
  promotes them to live status atomically with the Schema 13.1 upgrade.
- **Two-phase orchestration inside `academic-paper full` mode** (design doc §5):
  Phase 4 splits into Phase 4a paper-blind writer pre-commitment + Phase 4b
  paper-visible drafting + self-scoring. Phase 6 splits into Phase 6a
  paper-blind evaluator pre-commitment + Phase 6b paper-visible scoring +
  decision. Phase-numbered `<phase4a_output>` / `<phase6a_output>` data
  delimiters mirror the v3.6.2 reviewer pattern. Lint counts: writer 3+4 /
  evaluator 5+5 / reviewer 5+6 (reviewer surfaces remain zero-touch per §3.6).
  `[GENERATOR-PHASE-ABORTED]` abort tag with 5% / three-month operational
  monitor.
- **`academic-paper/SKILL.md` `## v3.6.6 Generator-Evaluator Contract Protocol`
  orchestration block** (101 lines): four-call structure with system-vs-user
  content discipline, schema-vs-runtime emission distinction, per-phase lint,
  abort handling, two valid Stage 3 entry paths (standard F0/F4 + exceptional
  F5), cross-session resume scope. Plus a new `## Known limitations` section
  carrying the graceful-degradation forward note (v3.6.7 candidate) + the
  cross-session resume `pre_commitment_history[]` forward note (v3.6.7+
  candidate) + in-pair Phase 6 evaluator vs external `academic-paper-reviewer`
  tech debt.
- **`academic-paper/agents/draft_writer_agent.md` + `peer_reviewer_agent.md`**
  each gain a verbatim `## v3.6.6 Generator-Evaluator Contract Protocol`
  section with the system-prompt sub-sections for Phase 4a/4b (writer) and
  Phase 6a/6b (evaluator). The orchestrator includes the relevant sub-section
  verbatim in the system prompt for the corresponding call; user content
  carries contract JSON, paper metadata, delimiter blocks, and upstream
  artefacts per the SKILL.md discipline.
- **`scripts/check_sprint_contract.py` SC-* mode-gating audit** (per §7.1
  implementation requirement): SC-5 (measurement_procedure canonical outputs)
  and SC-11 (panel_size sanity) now mode-gated to
  `mode.startswith("reviewer_")` so they do not noise on clean writer /
  evaluator templates. SC-9 (paraphrase_minimum_dimensions exceeds dim count)
  extended across all three mode families: reviewer reads
  `mp.paraphrase_minimum_dimensions`, writer reads
  `pre_commitment_artifacts.acceptance_criteria_paraphrase.minimum_dimensions`,
  evaluator reads `disagreement_handling.paraphrase_minimum_dimensions`.
  Mode-agnostic warnings (SC-1 baseline lag, SC-2 single dimension, SC-3 no
  mandatory, SC-4 orphan dim ref, SC-7 conflicting actions, SC-10 unreferenced
  mandatory/high) unchanged.
- **17 new validator tests** (54 → 71 total): 4 writer/evaluator template
  positive tests; 5 schema-branch negative tests covering branches 11 / 12 /
  4 / 5 / 6 hard-fail (cross-mode field leakage intentionally NOT a v3.6.6
  hard-fail per §7.1 R1 settled — v3.7.x `not`-clause hardening is the
  long-term fix); 2 §3.6 reviewer regression tests
  (`test_existing_reviewer_contracts_still_valid_under_13_1` +
  `test_byte_equivalent_validation_for_reviewer_contracts`); 6 SC-5/SC-9/SC-11
  mode-gating tests.
- **`scripts/check_v3_6_6_ab_manifest.py`** (new) implements the §7.5 manifest
  CI lint: schema-shape checks per §6.2 (top-level required fields with
  declared types; per-paper required fields; paper_id uniqueness; aggregate
  role counts 6+1; paper-A paper_type families 3 × 2; paper-A required
  judge_output_baseline; paper-C must-have known_failure_mode +
  failure_evidence; paper-C must-not-have judge / metrics fields);
  path-existence checks (mode-conditional + populated-optional);
  reverse-scan against fixture-orphans; exit-1-on-malformed-YAML mirrors
  `check_sprint_contract.py` convention.
- **`.github/workflows/spec-consistency.yml`** extends the "Validate sprint
  contract templates" step to iterate writer + evaluator template directories
  alongside the existing reviewer loop, and adds a new "Validate v3.6.6 A/B
  fixture manifest" step running the new manifest CI lint script as an
  additional step inside the existing `spec-consistency` job.
- **`tests/fixtures/v3.6.6-ab/` A/B evidence fixture stub** (30 files):
  manifest.yaml + README.md + 6 paper-A inputs/baseline + 1 paper-C
  inputs/baseline + Stage 3 reviewer excerpt + 6 codex-judge baseline
  placeholders. `manifest_lint_mode: spec_branch`, `fixture_version: 0.1.0`.
  Each placeholder explains the expected populated content; real fixture data
  (existing deep-research synthesis reports for paper-A; v3.6.5 session log
  + Stage 3 reviewer excerpt for paper-C; codex gpt-5.5 + xhigh judge runs
  against paper-A baseline) populates in follow-up commits before the
  v3.6.6 implementation work fully completes.
- **`academic-paper-reviewer/references/sprint_contract_protocol.md`
  cross-reference** noting Schema 13.1 since v3.6.6 + pointing readers at
  `academic-paper/SKILL.md` + design doc §5 for the parallel
  generator-evaluator protocol. The reviewer protocol itself is byte-equivalent
  across v3.6.2 → v3.6.8 (zero-touch promise per §3.6).

### Changed

- **Suite version**: v3.6.7 → v3.6.8 (per the naming note above; design doc
  retains v3.6.6 for the contract gate version).
- **`academic-pipeline` skill version** bumped from v3.6.7 to v3.6.8 in the
  `.claude/CLAUDE.md` Skills Overview table.

### Deferred

- **Real fixture data populate** for `tests/fixtures/v3.6.6-ab/` (30
  placeholders → real paper-A inputs + baseline + paper-C session log + codex
  judge runs) lands in follow-up commits.
- **Treatment runs** (writer Phase 4a/4b + evaluator Phase 6a/6b on the seven
  fixtures), **codex judge against treatment**, and **metrics computation
  + summary.md** require actual `academic-paper full` invocations + Semantic
  Scholar API + codex CLI runs; deferred to follow-up commits before the
  fixture-completeness work concludes.
- **manifest_lint_mode flip** from `spec_branch` to `implementation_pr`
  co-lands with the treatment population in the same atomic merge state per
  §6.5 invariant 3.
- **ROADMAP §3.6.4 description correction** per design doc §9.3 ("Extend
  v3.6.2 sprint contract pattern to the existing `academic-paper`
  writer/evaluator pair via contract-gated phase splits and Schema 13.1
  conditional gates. No new agent files; existing `draft_writer_agent` and
  `peer_reviewer_agent` gain per-phase sub-section instructions") lands in
  the private ROADMAP.md (gitignored, maintained outside this public repo), not in
  this repo PR.

## [3.6.7] - 2026-04-30

### Added

- **Downstream-agent pattern protection layer** (`docs/design/2026-04-29-ars-v3.6.7-downstream-agent-pattern-protection-spec.md`).
  Hardens three downstream agents against 17 hallucination/drift patterns
  documented in the spec: `synthesis_agent` (A1–A5 narrative-side), the
  survey-designer mode of `research_architect_agent` (B1–B5 instrument-side),
  and the abstract-only mode of `report_compiler_agent` (C1–C3 publication-
  side), plus four cross-cutting patterns (D1–D4). Patterns observed in
  production output across multiple chapter-length runs.
- **Four reference files in `shared/references/`** carrying the operational
  contracts that protection clauses cite:
  - `irb_terminology_glossary.md` — anonymity vs confidentiality vs
    de-identification vs pseudonymization (B1).
  - `psychometric_terminology_glossary.md` — true reverse-coded vs contrast
    item, with construct-equivalence rule (B2).
  - `protected_hedging_phrases.md` — five-rule contract for upstream-marked
    hedge protocol (conservative inclusion, anchor every entry, no
    duplicates, verbatim preservation, conflict reporting) (C1).
  - `word_count_conventions.md` — whitespace-split standard (`body.split()`),
    3–5% buffer below hard cap, publisher conventions (C1).
- **Cross-model audit prompt template** at
  `shared/templates/codex_audit_multifile_template.md` — seven audit
  dimensions (cross-ref, hallucination, primary-source integrity, internal
  coherence, instrument quality, Round-N framing, COI adequacy) plus a
  mandatory three-part Section 4(f) check for `report_compiler_agent`
  bundles (whitespace-split cap-minus-buffer, protected-hedge verbatim,
  abstract no less hedged than body — failure of any sub-check is P1).
- **Static lint** at `scripts/check_v3_6_7_pattern_protection.py` enforcing
  protection-clause presence and obligation-phrase shape across the
  reference files, audit template, and three downstream agent prompts.
  Per-regex `allow_prohibition` flag scopes the prohibition exemption so
  prohibition-style obligations (`DO NOT simulate`, `must not claim
  audit-passed state`, `does not paraphrase`) do not leak the exemption to
  assertion-style obligations on the same Check. Span-restricted exemption
  rejects a second prohibition elsewhere in the bullet. Modal/advisory
  weakener coverage: `may`, `should`, `can`, `will`, `would`, `ought to`,
  `ideally`, `preferably`, `We recommend that`, `is/are recommended`,
  `is/are allowed`, `is/are permitted`, plus exception qualifiers
  (`except`, `unless`, `save when`).
- **Mutation test suite** at
  `scripts/test_check_v3_6_7_pattern_protection.py` with 29 tests
  preserving codex review evidence (R2–R6). Future checker regressions
  surface in CI rather than only in ad-hoc mutation runs.
- **CI wiring** in `.github/workflows/spec-consistency.yml` runs both the
  static lint and the mutation suite on every push and pull request.

### Changed

- **`deep-research/agents/synthesis_agent.md`** carries a `PATTERN
  PROTECTION (v3.6.7)` block with five clauses covering effect-inventory
  cross-section consistency self-check, pending-verification hedge wrap,
  one-line anchor justification, verbatim phrase boundary on quotes, and
  the prohibition on declarative claims about un-provided documents
  (with conditional-language fallback).
- **`deep-research/agents/research_architect_agent.md`** survey-designer
  mode carries a `PATTERN PROTECTION (v3.6.7)` block with five clauses
  covering IRB terminology pass-through, reverse-coded construct-
  equivalence justification, event-anchored retrospective default
  (calendar-anchored only when sample shares a common event date),
  neutral-balanced item phrasing with chapter argument vocabulary
  forbidden, and primary-source list enumerate-fully (no subsetting,
  no over-setting, no scope cross-contamination).
- **`deep-research/agents/report_compiler_agent.md`** abstract-only mode
  carries a `PATTERN PROTECTION (v3.6.7)` block with three clauses
  covering whitespace-split word budget plus 3–5% buffer with budget-
  protected hedges, explicit-temporal-bounds reflexivity disclosure
  (year range / past-tense disambiguating verb / "former" prefix; deictic
  phrases forbidden), and the anti-fake-audit guard (DO NOT simulate any
  audit step; DO NOT claim to have run codex/external review; output
  metadata must not claim audit-passed state).

### Notes

- v3.6.7 ships in two stages. **Step 1 + Step 2** (this entry) include
  the four reference files, the audit template, the static lint, the
  mutation test suite, the CI wiring, and the three agent-prompt
  protection blocks. **Step 6** (orchestrator hooks for automatic
  per-agent audit and anti-fake-audit guard wiring) and **Step 8**
  (synthetic evaluation case demonstrating all 17 patterns triggered +
  protected) ship in a follow-up PR. Step 6 is cross-agent runtime work
  that warrants its own design discussion and is intentionally decoupled
  from this prompt-and-lint PR.
- Codex review history: seven rounds of `gpt-5.5` + `xhigh` cross-model
  review reached SHIP-OK with zero P1 + P2 findings. R1 closed ten
  Step-1 findings; R2 closed four cascade gaps plus the per-Check
  `allow_prohibition` leak; R3 closed three P2 findings (span-restricted
  exemption, token→regex with imperative anchoring, `except/unless/
  save when` weakeners); R4 closed three P2 findings (modal verb scope
  expansion, §6 sub-clause coverage, lint→CI wiring); R5 closed one P2
  plus one P3 (`should/can/permitted` modals and the mutation test
  suite); R6 closed one P2 (`will/would/ought to/ideally/preferably/
  We-recommend-that` weakeners) and explicitly deferred orchestrator
  runtime hooks to the Step 6 follow-up PR. R7 surfaced only one P3
  add-counter signal (`try to / generally / where relevant` weakeners),
  which is non-blocking polish.
- ARS pipeline ship-quality target updates from "each agent produces a
  clean v1" to "end-to-end deliverable set passes independent xhigh
  cross-model audit at 0 P1 + P2 finding within three rounds" (per spec
  §10).

## [3.6.5.2] - 2026-04-27

### Changed

- **`docs/SETUP.md` Method 4 (claude.ai) recommendation revised**. Method 4b
  (Project + GitHub integration) is now presented first as the recommended
  claude.ai path, since it brings the repository into Project knowledge for
  reading and citation without losing fidelity. Method 4a (Custom Skill upload)
  is now explicitly marked as **not recommended for this suite**, with a
  rationale paragraph covering two compounding reasons:
  - ARS depends on Claude Code-only orchestration features. Each skill drives
    12-13 specialised agents through Claude Code's Task / subagent tooling
    and Material Passport file handoffs that resume across sessions.
    claude.ai Custom Skills do support multi-file packages with `scripts/`
    and code execution per Anthropic's documentation, but the Anthropic-
    documented scope of the claude.ai Custom Skill runtime does not include
    Claude Code's Task / subagent control surface or cross-session Material
    Passport handoffs. The recommendation is forward-looking based on those
    documented assumptions; we have not run a live upload to characterise
    the actual surfacing in claude.ai.
  - Trimming the four `description` fields below claude.ai's 200-character cap
    would weaken Claude Code and Cowork routing on the platforms the suite was
    actually built for. The Agent Skills specification and Claude Code Skills
    documentation both allow up to 1,024 characters; only claude.ai's upload
    UI enforces 200. Trading Claude Code and Cowork routing precision for
    partial functionality on the limited claude.ai path was judged not worth
    it.
- **Method 4a install commands kept in place** for users who decide to try it
  anyway, framed as "if you want to try this path despite the limitations"
  rather than as a recommended flow. The upload UI's expected rejection on
  description-too-long is documented as deliberate, not an oversight to fix
  later.
- **`docs/SETUP.zh-TW.md`** mirrors the English changes end-to-end.

### Notes

- Doc-only patch. No `SKILL.md` (frontmatter or body), no agent file, no
  schema, no script, no test, no workflow, and no version bump in any skill
  changed in this patch. The four current `description` fields stay at their
  Claude Code-native lengths (440-842 characters) so routing on Claude Code
  and Cowork remains intact.
- This patch is a scope change from the v3.6.5.2 originally forecast in the
  v3.6.5.1 SETUP doc. The earlier plan was a description trim; on review, the
  trim direction was abandoned because it would have damaged Claude Code and
  Cowork routing to unblock a path that delivers an untested partial fit
  anyway. The v3.6.5.1 SETUP text's forward-promise of a description trim is
  removed here.
- Issue [#44](https://github.com/Imbad0202/academic-research-skills/issues/44)
  receives a single consolidated reply on this PR's merge, summarising both
  v3.6.5.1 (SETUP doc rewrite) and v3.6.5.2 (Method 4a recommendation), and
  closes there.

## [3.6.5.1] - 2026-04-27

### Fixed

- **`docs/SETUP.md` Method 3 install paths** — Option A (symlink) and Option B (copy)
  now install each of the four skill folders separately into `~/.claude/skills/<skill-name>/`,
  matching the `<install-root>/<skill-name>/SKILL.md` discovery convention. The previous
  text installed the whole repo under `~/.claude/skills/academic-research-skills/`, which
  buried the four `SKILL.md` files one level too deep for Cowork / Claude Code discovery.
- **`docs/SETUP.md` Method 4 (claude.ai) restructured** — split into Method 4a
  (Custom Skill upload via Settings → Capabilities → Skills, the standard claude.ai Skill
  install path) and Method 4b (Project + GitHub integration, fallback knowledge mode and
  not a Skill install). The previous text framed GitHub integration as a Skill install
  path, which conflated content retrieval with skill execution. Method 4a documents the
  current 200-character `description` cap blocker (this entry originally forecast a
  description trim in v3.6.5.2; see the v3.6.5.2 entry above for the actual decision —
  Method 4a is documented as not recommended for this suite, and descriptions remain at
  their Claude Code-native lengths).
- **Method 3 prerequisites** — expanded from one sentence to a full prerequisites
  subsection covering Claude Desktop version, internet connectivity, Cowork process model,
  folder permissions, paid plan, and Team/Enterprise org-admin controls.
- **Method 4 prerequisites** — split per sub-method. 4a documents zip structure +
  description cap surfacing as upload-time errors; 4b documents GitHub authentication via
  the Anthropic connector, private-repo App authorization, and Team/Enterprise owner-level
  connector enablement.
- **Cowork UI terminology** — replaced "Cowork tab" / "working directory" with current
  Cowork UI labels: mode selector (Chat / Cowork), Tasks view, "Use an existing folder"
  in the left navigation panel, and Cowork Project as the canonical term.
- **Skill invocation framing** — clarified that Claude uses each skill's `description`
  for relevance routing rather than literal trigger-phrase matching, and documented the
  Cowork `/` command palette and `+` capability picker as explicit invocation surfaces.
- **Method 4 directory table** — added the `scripts/` row (required for Material Passport
  `literature_corpus[]` adapters and schema validators) and refreshed the project-capacity
  guidance against current Anthropic Project file limits (per-file 30 MB; file count is
  not artificially capped at 200).
- **`docs/SETUP.zh-TW.md`** — mirrored the English rewrite end-to-end so Traditional
  Chinese readers see the same structure and content for Methods 1-4.
- **`QUICKSTART.md` Step 1** — install commands aligned with the new Method 3 four-symlink
  approach.

### Notes

- Doc-only patch. No skill content (`SKILL.md`), no agent file, no schema, no script,
  and no test changed in this patch.
- Issue [#44](https://github.com/Imbad0202/academic-research-skills/issues/44) (philpav)
  reports SETUP problems on Cowork and claude.ai. v3.6.5.1 fixes the SETUP doc;
  this entry originally forecast a `SKILL.md` description-length fix in v3.6.5.2,
  but v3.6.5.2 instead documents Method 4a as not recommended for this suite (see
  the v3.6.5.2 entry above for the actual decision). Issue #44 receives a single
  consolidated reply and closes on v3.6.5.2 ship.

## [3.6.5] - 2026-04-27

### Added

- Material Passport `literature_corpus[]` consumer integration in Phase 1
  (deep-research/bibliography_agent + academic-paper/literature_strategist_agent).
  Corpus-first, search-fills-gap flow with PRE-SCREENED reproducibility block.
  Reproducibility for systematic-review use is preserved through Iron Rule 1
  same-criteria parity plus Step 2 case C (standard external search runs even
  when corpus fully covers RQ subtopics).
- `academic-pipeline/references/literature_corpus_consumers.md` — consumer protocol
  reference with four Iron Rules (Same criteria / No silent skip / No corpus mutation /
  Graceful fallback on parse failure) and per-consumer reading instructions.
- `scripts/check_corpus_consumer_protocol.py` — CI lint enforcing nine protocol invariants
  with manifest-driven consumer list and stub-block opt-out.
- `scripts/corpus_consumer_manifest.json` — supported-consumer manifest.

### Changed

- `shared/handoff_schemas.md` Schema 9 — retired the v3.6.4 "Consumer-side integration
  deferred to v3.6.5+" caveat; replaced with backpointer to the consumer protocol.
- `deep-research/SKILL.md` 2.9.1 → 2.9.2 — bibliography_agent corpus-first flow (also
  syncs Version Info footer that lagged at 2.9.0).
- `academic-paper/SKILL.md` 3.1.0 → 3.1.1 — literature_strategist_agent corpus-first flow.
- `academic-pipeline/SKILL.md` 3.6.4 → 3.6.5 — suite version invariant.
- `.claude/CLAUDE.md`, `MODE_REGISTRY.md`, `README.md`, `README.zh-TW.md`,
  `scripts/check_spec_consistency.py` updated for the version bump (suite version,
  badge, tag, changelog heading).

### Notes

- Consumer integration is presence-based: auto-engages when passport carries a
  non-empty `literature_corpus[]` and parses cleanly. Parse failures fall back
  to external-DB-only flow with a `[CORPUS PARSE FAILURE]` surface. No new env
  flag introduced.
- Schema is unchanged from v3.6.4. Existing user adapters work without modification.
- `citation_compliance_agent` corpus integration deferred to v3.6.6+.
- `source_pointer` is not dereferenced by consumers; URI resolution remains a future
  `source_verification_agent` concern.

## [3.6.4] - 2026-04-25

### Added

- **Material Passport `literature_corpus[]` input port**. Schema 9 gains an optional `literature_corpus[]` field defined by `shared/contracts/passport/literature_corpus_entry.schema.json`. Each entry carries `citation_key`, CSL-JSON `authors`, `year`, `title`, and a `source_pointer` back to the user's own KB. `abstract` and `user_notes` are private optional fields with copyright caveats.
- **Adapter contract** (`academic-pipeline/references/adapters/overview.md`): language-neutral specification for producing literature_corpus entries from user-owned corpus sources. Covers fail-soft entry-level error handling, mandatory `rejection_log.yaml` output, deterministic ordering (sort by `citation_key` / `source`), and extension points for user-written adapters.
- **Three reference Python adapters** (`scripts/adapters/`): `folder_scan.py` (filesystem of PDFs), `zotero.py` (Better BibTeX JSON export), `obsidian.py` (vault frontmatter, BibTeX-style or literature-note convention). Each ships with pytest tests, fixtures, and golden expected outputs.
- **Rejection log contract** (`shared/contracts/passport/rejection_log.schema.json`). Always emitted; empty when no rejections; closed enum of categorical reason values.
- **CI lint + pytest job**: `scripts/check_literature_corpus_schema.py` (schema + adapter example validation), `scripts/sync_adapter_docs.py --check` (schema→docs drift detector with auto-regen mode), and a new `.github/workflows/pytest.yml` running `scripts/adapters/tests/` on path-filtered triggers.
- `_common.ensure_unique_citekey(key, existing)` helper for adapters whose source already supplies a citekey (zotero, obsidian frontmatter), with sanitization to satisfy the schema pattern and a/b/...zz alpha-suffix collision disambiguation.
- `_common.path_to_file_uri(path)` helper that delegates to `Path.as_uri()` so spaces and reserved characters in filenames are properly percent-encoded.

### Changed

- `academic-pipeline/references/passport_as_reset_boundary.md`: "deferred to v3.6.4, PR-B" placeholders replaced with forward references to `adapters/overview.md` and `literature_corpus_entry.schema.json`.
- `shared/handoff_schemas.md`: Schema 9 optional fields table adds `literature_corpus`; new "Literature Corpus Input Port (v3.6.4)" subsection appended after Reset Boundary Extension.
- `academic-pipeline/SKILL.md` bumped 3.6.3 → 3.6.4 (suite version invariant). Other skills retain independent semver.
- `.claude/CLAUDE.md`, `MODE_REGISTRY.md`, `README.md`, `README.zh-TW.md`, `scripts/check_spec_consistency.py` updated for the version bump (suite version, badge, tag, changelog heading).

### Not changed (explicit non-goals)

- No ARS agent consumes `literature_corpus[]` yet. Consumer-side integration is deferred to v3.6.5+. v3.6.4 defines the input port only.
- No PDF parsing, no text extraction, no live API clients, no authenticated library crawling. The reference adapters read filenames or local export files and never make network calls.

## [3.6.3] - 2026-04-23

### Added
- **Opt-in passport reset boundary** via `ARS_PASSPORT_RESET=1`. Every FULL checkpoint becomes a context-reset boundary when the flag is set. `systematic-review` mode with the flag ON makes reset mandatory; other modes treat reset as the flag-gated default.
- **`resume_from_passport=<hash>` mode** in `academic-pipeline`. Lets users resume a pipeline run in a fresh Claude Code session from the Material Passport ledger alone.
- **Schema 9 `reset_boundary[]`** optional append-only field with two entry kinds (`boundary`, `resume`). Entry shape in `shared/contracts/passport/reset_ledger_entry.schema.json` (oneOf split with `kind` discriminator). Hash computed via JSON Canonical Form + SHA-256 with `"000000000000"` placeholder for self-reference safety. Optional `pending_decision` field handles MANDATORY branch choices (Stage 3 reject/restructure/abort, Stage 5 finalization) that survive the reset boundary.
- **Protocol doc:** `academic-pipeline/references/passport_as_reset_boundary.md` (authoritative; every file mentioning `ARS_PASSPORT_RESET` must co-locate a reference).
- **CI lint:** `scripts/check_passport_reset_contract.py` + unittest suite. Wired into `.github/workflows/spec-consistency.yml`.
- **`docs/PERFORMANCE.md` + `docs/PERFORMANCE.zh-TW.md`** long-running-session subsection documenting when reset beats continuation, passport file-location convention, and empirical-measurement disclaimer.

### Changed
- `academic-pipeline/agents/pipeline_orchestrator_agent.md` adds §"Passport Reset Boundary (v3.6.3+)" and §"Resume Mode: `resume_from_passport`". FULL Checkpoint Template includes conditional reset-handoff tag slot.
- `academic-pipeline/references/pipeline_state_machine.md` documents `awaiting_resume` transitions derived from the ledger (no out-of-band state).
- `academic-pipeline/SKILL.md` adds `resume_from_passport` to the mode table and bumps version 3.6.2 → 3.6.3.
- `shared/handoff_schemas.md` Schema 9 gains `reset_boundary` row + "Reset Boundary Extension (v3.6.3)" subsection with full YAML example showing both kinds.

### Changed (post-P1 fixes)
- `pending_decision.options[]` now carries per-branch routing (`{value, next_stage, next_mode}`); `value` uniqueness within one options array is enforced by CI lint (`scripts/check_passport_reset_contract.py`). The matched option's `next_stage` supersedes the boundary entry's advisory `next` field. `next` MAY be `null` when all branches terminate or no sensible default exists.
- Exclusive advisory lock (POSIX `fcntl.flock LOCK_EX`, bounded timeout not exceeding 60 s, 30 s recommended) is required for the resume read-check-append sequence. Non-POSIX implementations MUST refuse to resume rather than degrade silently.

### Notes
- **Flag OFF is the default.** Pre-v3.6.3 behavior is preserved byte-for-byte when `ARS_PASSPORT_RESET` is unset or `=0`.
- Out of scope (deferred to v3.6.4): `examples/adapters/{folder_scan, zotero, obsidian}/` reference adapters and the `literature_corpus` entry shape on Schema 9.
- No breaking changes. No existing mode behavior changes when the flag is OFF.

## [3.6.2] - 2026-04-23

### Added

- **Sprint Contract (Schema 13) — reviewer hard gate.** `shared/sprint_contract.schema.json` defines machine-checkable acceptance criteria (`panel_size`, `acceptance_dimensions`, `failure_conditions` with `severity` + `cross_reviewer_quantifier`, `measurement_procedure`, optional `override_ladder`, bounded `agent_amendments`). Validator `scripts/check_sprint_contract.py` (schema validation + `check_structural_invariants()` hard check + nine soft warnings SC-1..SC-11 with SC-6 documented as dead path and SC-8 promoted to hard check). Two templates ship: `shared/contracts/reviewer/full.json` (panel 5) and `shared/contracts/reviewer/methodology_focus.json` (panel 2). Reviewer orchestration reshaped into paper-content-blind Phase 1 + paper-visible Phase 2 hard gate. Synthesizer runs three-step mechanical protocol (build matrix → evaluate with quantifier → resolve precedence). See `docs/design/2026-04-23-ars-v3.6.2-sprint-contract-design.md`.
- **Token cost note.** Reviewer total calls under sprint contract = `2 × panel_size`. For `reviewer_full`: 5 → 10 calls. Phase 1 input is metadata-only and output short, so real token bound is well below 2x.

### Changed

- **`academic-paper-reviewer` v1.8.1 → v1.9.0.** Five reviewer agent markdown files (EIC + methodology + domain + perspective + DA) gain Phase 1/2 protocol sections; `editorial_synthesizer_agent.md` gains the three-step synthesizer protocol + forbidden-operations list.
- **Harness retirement notes folded in.** The prior `[Unreleased]` harness-retirement pass (Task A per `project_ars_v3.6_execution_order.md`) ships with this release — 7 negative-framing blocks rewritten to positive / split form across 7 files, no behaviour change:
  - `academic-paper/agents/socratic_mentor_agent.md` — Core Principles items 1, 6 (F-001)
  - `deep-research/agents/socratic_mentor_agent.md` — Quality Standards items 2, 3, 4 (F-002)
  - `academic-paper/agents/draft_writer_agent.md` — quick style check, paragraph variation, colloquialisms, transition-word usage (F-003, 4 spots)
  - `academic-pipeline/agents/pipeline_orchestrator_agent.md` — **split** "Prohibited Actions" (9 items, all negative) into "Scope (delegate, don't perform)" (items 1-6, positive delegation) + "Hard boundaries (never violate)" (items 7-9, kept negative as intentional safety directives for silent-failure modes: fabrication, skipped checkpoints, skipped integrity gates) (F-004)
  - `academic-pipeline/agents/collaboration_depth_agent.md` — Agent-specific boundaries 4 bullets (F-005)
  - `academic-pipeline/SKILL.md` — single-line UX guidance (F-006)
  - `academic-paper/references/academic_writing_style.md` — §4 Formality 3 items (F-007, discovered during apply)

### Notes

- `reviewer_re_review`, `reviewer_calibration`, `reviewer_guided` are reserved in the Schema 13 `mode` enum but ship without contract templates in v3.6.2. Those modes continue pre-v3.6.2 behaviour until a follow-up patch adds their templates.
- `reviewer_quick` is intentionally excluded from the Schema 13 `mode` enum (Q3-A' boundary).
- CI gate: `validate-sprint-contracts` step in `.github/workflows/spec-consistency.yml` runs the full unit test suite and validates every template under `shared/contracts/reviewer/*.json` against the current ARS version.
- Kept-as-debt from harness retirement: ~50 anti-hallucination references across `deep-research/`, `academic-paper/references/anti_leakage_protocol.md`, `academic-pipeline/references/ai_research_failure_modes.md`, `shared/agents/compliance_agent.md`, `shared/compliance_checkpoint_protocol.md` — load-bearing integrity architecture (Lu 2026 7-mode; S2 API Tier-0; `[MATERIAL GAP]` taxonomy). Not retired under the iron rule clause for silent-failure domains.

## [3.5.1] - 2026-04-22

### Added

- **Opt-in Socratic reading-check probe.** When `ARS_SOCRATIC_READING_PROBE=1` is set, the Socratic Mentor fires a one-time honesty probe during goal-oriented sessions where the user has cited a specific paper. The probe asks the user to paraphrase one passage. Decline is logged without penalty. Outcome is recorded in the Research Plan Summary and flows into the Stage 6 AI Self-Reflection Report when the pipeline continues. Default OFF. Roadmap slot: v3.7.3. See `deep-research/agents/socratic_mentor_agent.md` §"Optional Reading Probe Layer".

### Changed

- `deep-research/SKILL.md`, `deep-research/references/socratic_mode_protocol.md`, `academic-pipeline/references/process_summary_protocol.md` — aligned text updates for the new probe section. No behaviour change when the env var is unset.

### Version

- Suite: 3.5.0 → 3.5.1 (patch; opt-in, default OFF, no breaking change)
- `deep-research` skill: 2.9.0 → 2.9.1
- `academic-pipeline` skill: 3.5.0 → 3.5.1 (tracks suite version per `check_version_consistency.py` invariant)

## [3.5.0] - 2026-04-21

### Added
- `shared/collaboration_depth_rubric.md` v1.0 — canonical 4-dimension rubric (Delegation Intensity, Cognitive Vigilance, Cognitive Reallocation, Zone Classification). Based on Wang, S., & Zhang, H. (2026). "Pedagogical partnerships with generative AI in higher education: how dual cognitive pathways paradoxically enable transformative learning." *International Journal of Educational Technology in Higher Education*, 23:11. DOI 10.1186/s41239-026-00585-x. Licensed CC-BY-NC 4.0.
- `academic-pipeline/agents/collaboration_depth_agent.md` — observer agent (Agent Team grows 3 → 4). Invoked at every FULL/SLIM checkpoint and at pipeline completion; scores user-AI collaboration pattern against the canonical rubric. **Advisory only — never blocks progression.** Frontmatter declares `blocking: false`, `measures: collaboration_depth`, `rubric_ref: shared/collaboration_depth_rubric.md`.
- `scripts/check_collaboration_depth_rubric.py` + `scripts/test_check_collaboration_depth_rubric.py` — new lint enforces: (1) rubric file exists; (2) rubric cites Wang & Zhang 2026 with DOI; (3) `rubric_version` frontmatter field; (4) four canonical dimension headings; (5)/(6) any agent claiming `measures: collaboration_depth` references the canonical rubric path and declares `blocking: false`; (7)/(8) orchestrator and SKILL.md mention observer with non-blocking semantics. 10 unit tests, all green.
- `academic-pipeline/references/changelog.md` row v2.8.
- `academic-pipeline/references/reinforcement_content.md` row for FULL/SLIM checkpoint — IRON RULE: observer is advisory only, never blocks, never a leaderboard.

### Changed
- `academic-pipeline/SKILL.md` — version bump `3.3.0 → 3.4.0`. Agent Team table grows to 4 rows. New "Collaboration Depth Observer" section with explicit non-blocking guarantees and distinction from integrity verification and Stage 6 self-reflection. Reference Files table adds rubric entry.
- `academic-pipeline/agents/pipeline_orchestrator_agent.md` — checkpoint Steps flow amended: after `state_tracker` update the orchestrator invokes `collaboration_depth_agent` on the just-completed stage's dialogue range (FULL/SLIM only; MANDATORY integrity gates explicitly skip) and injects its output into checkpoint templates as a named "Collaboration Depth" section. FULL checkpoint template expanded with the observer block; SLIM template gains a one-line compact observer summary; MANDATORY template unchanged (integrity gates never dilute). New "Collaboration Depth Observer" subsection under §3 Checkpoint Management covers invocation, cross-model behaviour, short-stage guard, and non-blocking IRON RULE.
- `academic-pipeline/agents/state_tracker_agent.md` — Write Access Control adds `collaboration_depth_agent` (append-only `collaboration_depth_history[]`). New `dialogue_log_ref` turn-range pointer per stage; new `collaboration_depth_history[]` root-level array; new `append_observer_report()` function (only function that writes the history; preconditions block any attempt to turn observer output into a blocking condition).
- `scripts/_skill_lint.py` — new shared `split_frontmatter(text) -> (dict|None, str)` lenient helper, reused by the new lint.
- Suite version bumped to `3.5.0` across `README.md`, `README.zh-TW.md`, `MODE_REGISTRY.md`, `.claude/CLAUDE.md`; new `### v3.5.0 (2026-04-21)` section in both READMEs; new `## v3.5 Key Additions` block in `.claude/CLAUDE.md`.
- `scripts/check_spec_consistency.py` — README version expectations bumped to `v3.5.0`; `MODE_REGISTRY.md` last-updated expectation updated; `.claude/CLAUDE.md` suite version expectation updated. New embedded-changelog regression checks for `### v3.5.0 (2026-04-21)` entries.

### Notes
- MANDATORY integrity checkpoints (Stages 2.5, 4.5) are **not** instrumented by the observer. The observer never appears in the "Flagged" line of any checkpoint. `blocked_by: collaboration_depth_agent` is never a legal state. The orchestrator's numbered Step 3 explicitly branches on checkpoint_type.
- Cross-model behaviour (`ARS_CROSS_MODEL`): observer runs on both models; dimension disagreement > 2 points is flagged explicitly, never silently averaged. `ARS_CROSS_MODEL_SAMPLE_INTERVAL` escape hatch documented.
- Short-stage guard: if the completed stage has fewer than 5 user turns, a static `insufficient_evidence` block is injected and the full-model observer call is skipped.
- Credit: Wang & Zhang (2026) introduced the dual-pathway SEM and three-zone (Zone 1 / Zone 2 / Zone 3) framework that anchors the rubric's dimension operationalisation and synthesis rule.

## [3.4.0] - 2026-04-20

### Added

- `shared/agents/compliance_agent.md` — single mode-aware agent for PRISMA-trAIce + RAISE compliance. Dispatches on `compliance_mode ∈ {systematic_review, primary_research, other_evidence_synthesis}`. See design spec `docs/design/2026-04-20-v3.4-prisma-trAIce-raise-readcheck-design.md`.
- `shared/prisma_trAIce_protocol.md` — verbatim 17-item snapshot from `cqh4046/PRISMA-trAIce` (2025-12-10) + per-item ARS check procedure + 4-tier behaviour table. Citation: Holst et al. 2025, JMIR AI, doi:10.2196/80247.
- `shared/raise_framework.md` — 4 principles (human oversight / transparency / reproducibility / fit-for-purpose) + 8-role matrix + mandatory scope disclaimer. Citation: Thomas et al. 2025, NIHR ESG Best Practice Working Group, 17 July 2025.
- `shared/compliance_checkpoint_protocol.md` — Stage 2.5 / 4.5 dual-gate behaviour spec, decision precedence, override ladder, fail-loop integration, boundary behaviour for non-pipeline invocation.
- `shared/compliance_report.schema.json` — Schema 12 validator (Draft 2020-12).
- `examples/compliance/fixture_sr_full_compliant.yaml`, `fixture_sr_missing_M4.yaml`, `fixture_primary_raise_weak.yaml` — regression fixtures + user reference templates.
- `scripts/check_compliance_report.py` + tests — Schema 12 CLI validator.
- `scripts/validate_compliance_fixtures.py` + tests — YAML→JSON fixture loop used by CI.
- `scripts/check_prisma_trAIce_freshness.py` + tests — non-blocking upstream-drift warning (180-day threshold).
- `.github/workflows/freshness-check.yml` — weekly cron (Monday 09:00 UTC) + path-filtered push trigger for freshness check.
- `docs/PERFORMANCE.md` + `.zh-TW.md`: new "Long-running session management" section + v3.4.0 token-cost deltas.

### Changed

- `shared/handoff_schemas.md`: Schema 12 pointer + Material Passport `compliance_history[]` (append-only audit trail).
- `academic-pipeline/SKILL.md` (v3.2.2 → v3.3.0): Stage 2.5 / 4.5 extended with compliance payload; checkpoint dashboard gains compliance row.
- `deep-research/SKILL.md` (v2.8.1 → v2.9.0): `systematic-review` mode now triggers `compliance_agent` at both gates.
- `academic-paper/SKILL.md` (v3.0.2 → v3.1.0): `full` mode adds pre-finalize RAISE principles-only check (warn-only). `disclosure` mode unchanged and complementary.
- `.github/workflows/spec-consistency.yml`: added compliance validator + unit test runner steps.
- `scripts/check_spec_consistency.py`: version pins bumped.
- `README.md`, `README.zh-TW.md`, `.claude/CLAUDE.md`, `MODE_REGISTRY.md`: suite version → 3.4.0.

### Notes

- Calibration philosophy: compliance_agent ships with transparent reporting, **no hard FNR/FPR threshold**. This is self-consistent with ARS's v3.3.2 `task_type: open-ended` truth-in-advertising annotation — publishing a hard gate would contradict the "not a benchmark task" declaration.
- Compliance Mandatory failures in SR mode are blocking, but the 3-round override ladder preserves human-in-the-loop authority. Overrides auto-inject `disclosure_addendum` into the final manuscript — no detection evasion.
- The v3.2 Failure Mode Checklist and the v3.4.0 compliance agent run in parallel at the same gates. Their scopes are non-overlapping: failure-mode checks research validity; compliance checks reporting transparency.
- Internal numbering: compliance_report is Schema 12 (not 10). Schema 10 is Style Profile (v2.7+); Schema 11 is R&R Traceability Matrix. The plan's initial Schema 10 assignment was corrected mid-branch before Task 9.

## [3.3.6] - 2026-04-15

### Added
- `docs/ARCHITECTURE.md` — single source of truth for pipeline structure (flow, stage × dimension matrix, data-access flow, skill dependency graph, quality gates, modes). Merged into main via PR #18.
- `docs/SETUP.md` + `docs/SETUP.zh-TW.md` — prerequisites, API keys, Pandoc / tectonic setup, cross-model verification (`ARS_CROSS_MODEL`), and four installation methods.
- `docs/PERFORMANCE.md` + `docs/PERFORMANCE.zh-TW.md` — per-mode token budgets, full-pipeline cost estimate, and recommended Claude Code settings (Agent Team, Ralph Loop, Skip Permissions).

### Changed
- `README.md` and `README.zh-TW.md` streamlined: removed the ASCII pipeline diagram and the 16-point key-feature list (superseded by `docs/ARCHITECTURE.md`). Setup, performance, and installation sections relocated to `docs/`. Skill Details now anchors version numbers and routes readers to ARCHITECTURE.md §3 for per-agent rosters.
- `scripts/check_spec_consistency.py` — bumped README version expectations to `v3.3.6`; DOCX contract expectations (both EN and zh-TW) moved from READMEs to the new `docs/SETUP.*` docs; added `check_setup_docs()` step.
- Suite version bumped to `3.3.6` across `README.md`, `README.zh-TW.md`, `.claude/CLAUDE.md`, and `MODE_REGISTRY.md`.

### Notes
- No functional change to any skill. Pure documentation reorganization.

## [3.3.5] - 2026-04-15

### Added
- `shared/benchmark_report.schema.json` — JSON Schema (draft-2020-12) defining required fields for ARS benchmark reports. Catches the "n=2 author-conducted baseline" failure mode from Anthropic's automated-w2s-researcher paper.
- `shared/benchmark_report_pattern.md` — narrative hub doc explaining the schema.
- `scripts/check_benchmark_report.py` + tests — validator with self-scored and small-sample warnings.
- `examples/benchmark_report_template.json` — fillable template.
- `repro_lock` optional sub-block added to Material Passport (Schema 9 in `shared/handoff_schemas.md`). Configuration lockfile; NOT a deterministic replay guarantee.
- `shared/artifact_reproducibility_pattern.md` — hub doc with mandatory "not a replay guarantee" disclaimer section and required `stochasticity_declaration` field.
- `scripts/check_repro_lock.py` + tests — passport validator.
- `examples/passport_with_repro_lock.yaml` — example.
- `requirements-dev.txt` — formal Python dev dep manifest (pyyaml + jsonschema).

### Changed
- `.github/workflows/spec-consistency.yml` installs via `pip install -r requirements-dev.txt` instead of ad-hoc `pip install`.
- `academic-pipeline/references/reproducibility_audit.md` cross-links to new artifact-reproducibility pattern.

## [3.3.4] - 2026-04-15

### Fixed
- Embedded changelog sections in `README.md` and `README.zh-TW.md` now include the missing `v3.3.3` and `v3.3.2` summaries, so the README history matches the published releases.
- `scripts/check_spec_consistency.py` now verifies that the README changelog summaries include the latest release entries, so future drift fails CI.

### Changed
- Suite version bumped to `3.3.4` across release-facing docs after the README changelog sync patch release.

## [3.3.3] - 2026-04-15

### Fixed
- `scripts/_skill_lint.py` now rejects SKILL frontmatter that is missing a closing `---` fence instead of silently treating the rest of the file as YAML.
- `scripts/_skill_lint.py` now reports a readable error when frontmatter parses as valid YAML but not as a mapping object, instead of crashing with `AttributeError`.
- Broken showcase link for the post-publication audit report corrected in both `README.md` and `README.zh-TW.md`.
- `scripts/check_spec_consistency.py` now validates README relative Markdown links so future dead links fail CI.

### Changed
- DOCX generation contract aligned across README, `academic-paper/SKILL.md`, `academic-paper/agents/formatter_agent.md`, `academic-pipeline/SKILL.md`, and `academic-pipeline/agents/pipeline_orchestrator_agent.md`: direct `.docx` output is Pandoc-dependent, with Markdown + conversion instructions as the fallback.
- Added regression tests covering missing closing fences and non-mapping YAML frontmatter in both lint test suites.
- Suite version bumped to `3.3.3` across release-facing docs; `academic-paper` patch-bumped to `3.0.2` and `academic-pipeline` patch-bumped to `3.2.2`.

## [3.3.2] - 2026-04-15

### Added
- `metadata.data_access_level` field on every top-level SKILL.md. Three-tier vocabulary (`raw` | `redacted` | `verified_only`) declaring what kind of data each skill may consume. Inspired by the three-tier isolation pattern in Anthropic's automated-w2s-researcher (2026).
  - `deep-research` = `raw`
  - `academic-paper` = `redacted`
  - `academic-paper-reviewer` = `verified_only`
  - `academic-pipeline` = `verified_only`
- `scripts/check_data_access_level.py` lint script with unit tests; wired into `.github/workflows/spec-consistency.yml`.
- Pointer section in `shared/handoff_schemas.md` documenting the vocabulary for future skill authors.
- `metadata.task_type` field on every top-level SKILL.md. Two-value vocabulary (`open-ended` | `outcome-gradable`) declaring whether the task has a scalar ground-truth metric. All current ARS skills are `open-ended` — the field is a truth-in-advertising signal that ARS targets domain-judgment work, not benchmark tasks.
- `scripts/check_task_type.py` lint script with 4 unit tests; wired into the same CI workflow.
- Pointer section in `shared/handoff_schemas.md` for the `task_type` vocabulary.
- `shared/ground_truth_isolation_pattern.md` — narrative pattern doc explaining the three-layer model behind `data_access_level` and `task_type`. Cross-references existing protocols (S2 verification, anti-leakage, integrity gates, calibration mode). Linked from `handoff_schemas.md` and `CONTRIBUTING.md`.

### Changed
- Per-skill `metadata.version` patch-bumped on all 4 SKILL.md files; `last_updated` refreshed to 2026-04-15.
- Suite version bumped to 3.3.2 across `README.md`, `README.zh-TW.md`, and `.claude/CLAUDE.md`.

## [3.3.1] - 2026-04-14

### Fixed
- Public contract drift across `README.md`, `README.zh-TW.md`, `.claude/CLAUDE.md`, `MODE_REGISTRY.md`, and the affected `SKILL.md` files
- Cross-model wording now matches the implemented scope: integrity sample verification and independent DA critique are shipped; sixth-reviewer peer review remains planned
- `academic-pipeline` checkpoint docs now state that SLIM checkpoints still wait for explicit user confirmation
- `academic-pipeline` integrity gate docs now consistently state that Stage 2.5 and Stage 4.5 cannot be skipped
- `academic-paper/SKILL.md` mode-count heading and `academic-paper-reviewer/SKILL.md` Version Info block

### Added
- `scripts/check_spec_consistency.py` to catch mode-count, version-block, and forbidden-claim drift
- `.github/workflows/spec-consistency.yml` to run the consistency check on pushes and pull requests

## [3.3] - 2026-04-09

### Added — PaperOrchestra-inspired enhancements
Integrates techniques from Song et al. (2026, *arXiv:2604.05018*) "PaperOrchestra: A Multi-Agent Framework for Automated AI Research Paper Writing."

- **Semantic Scholar API Verification** (deep-research, academic-pipeline): Tier 0 programmatic reference verification via S2 API. Title search with Levenshtein >= 0.70 matching. DOI mismatch detection for Compound Deception Pattern #5. Bibliography deduplication via S2 IDs. Graceful degradation if API unavailable.
  - New file: `deep-research/references/semantic_scholar_api_protocol.md`
  - Modified: `source_verification_agent`, `bibliography_agent`, `integrity_verification_agent`
- **Anti-Leakage Protocol** (academic-paper, deep-research): Knowledge Isolation Directive prioritizes session materials over LLM parametric memory for factual content. Flags `[MATERIAL GAP]` for missing content instead of silently filling from memory. Reduces Mode 5/6 failure risk.
  - New file: `academic-paper/references/anti_leakage_protocol.md`
  - Modified: `draft_writer_agent`, `report_compiler_agent`
- **VLM Figure Verification** (academic-paper): Optional closed-loop verification of rendered figures using vision-capable LLM. 10-point checklist covering data accuracy, APA 7.0 compliance, and visual quality. Max 2 refinement iterations.
  - New file: `academic-paper/references/vlm_figure_verification.md`
  - Modified: `visualization_agent`
- **Score Trajectory Protocol** (academic-pipeline): Per-dimension rubric score delta tracking across revision rounds. Detects regressions (delta < -3) and triggers mandatory checkpoint. Extends v3.2 early-stopping with dimension-level granularity.
  - New file: `academic-pipeline/references/score_trajectory_protocol.md`
  - Modified: `integrity_review_protocol.md`, `handoff_schemas.md` (Schema 5)
- **Stage 2 Parallelization Directive** (academic-pipeline): Visualization and argument building can run in parallel after outline completion.
- **Handoff Schema Updates** (shared): `semantic_scholar_id` field added to Bibliography source object. `score_trajectory` structure added to Integrity Report schema.

**Version bumps**: deep-research v2.8, academic-paper v3.0, academic-pipeline v3.2

## [3.2] - 2026-04-09

### Added — Lu 2026 integration
Integrates insights from Lu et al. (2026, *Nature* 651:914-919) — the first end-to-end autonomous AI research system to pass blind peer review.

- **AI Research Failure Mode Checklist** (academic-pipeline): 7-mode taxonomy extending the existing 5-type citation hallucination taxonomy. Covers implementation-bug blindness, hallucinated experimental results, shortcut reliance, bug-as-insight, methodology fabrication, and pipeline-level frame-lock. Runs at Stage 2.5 and 4.5 with mandatory blocking behaviour. Reported at Stage 6 in the Failure Mode Audit Log subsection of the AI Self-Reflection Report.
  - New file: `academic-pipeline/references/ai_research_failure_modes.md`
- **Reviewer Calibration Mode** (academic-paper-reviewer v1.8): opt-in mode that measures FNR / FPR / balanced accuracy / AUC against a user-supplied gold-standard set of 5-20 papers. Uses 5x ensembling with fresh context per run. Cross-model verification default-on. Session-scoped confidence disclosure.
  - New file: `academic-paper-reviewer/references/calibration_mode_protocol.md`
- **Disclosure Mode** (academic-paper v2.9): venue-specific AI-usage disclosure statement generator. v1 database covers ICLR, NeurIPS, Nature, Science, ACL, EMNLP. Unknown venues halt and prompt user to paste policy.
  - New files: `academic-paper/references/disclosure_mode_protocol.md`, `academic-paper/references/venue_disclosure_policies.md`
- **Fidelity-Originality Mode Spectrum** (all skills): classifies all modes on a fidelity–originality axis per Lu 2026 Fig 1c. Quick Mode Selection Guides updated with Spectrum column.
  - New file: `shared/mode_spectrum.md`
- **Early-Stopping Criterion** (academic-pipeline v3.1): convergence check (delta < 3 points + no P0) suggests stopping revision loop. Budget transparency estimate at pipeline start.
- **README Positioning Update**: "Why human-in-the-loop, not full automation?" section citing Lu 2026 as external evidence for ARS's design thesis. Both EN and zh-TW updated.

### Changed
- `.claude/CLAUDE.md`: synced all skill versions and mode lists to reality (deep-research v2.7, academic-paper v2.9, academic-paper-reviewer v1.8, academic-pipeline v3.1)
- `quality_rubrics.md`: added "Known error profile" preamble explaining rubric scores are ordinally but not cardinally interpretable without calibration

**Version bumps**: academic-paper v2.9, academic-paper-reviewer v1.8, academic-pipeline v3.1

## [3.1.1] - 2026-04-09

### Added
- **Information Systems — Senior Scholars' Basket of 11** (extending the *Basket of 8* added in v2.9): *Decision Support Systems*, *Information & Management*, *Information and Organization* — completing the AIS College of Senior Scholars' official list of premier IS journals
- Section heading updated from "Information Systems (Basket of 8)" to "Information Systems (Senior Scholars' Basket of 11)" in `academic-paper-reviewer/references/top_journals_by_field.md`
- Original IS Basket of 8 proposed and drafted by [@mchesbro1](https://github.com/mchesbro1) — [Issue #5](https://github.com/Imbad0202/academic-research-skills/issues/5). Extended to Basket of 11 by [@cloudenochcsis](https://github.com/cloudenochcsis) — [Issue #7](https://github.com/Imbad0202/academic-research-skills/issues/7), [PR #8](https://github.com/Imbad0202/academic-research-skills/pull/8). Source: [AIS Senior Scholars' List of Premier Journals](https://aisnet.org/research/seniorscholarsbasket/)

## [2.9.1] - 2026-04-03

### Added
- `status` and `related_skills` metadata to all 4 SKILL.md frontmatters
  - Enables skill discovery tools and cross-skill navigation for users with multiple skills installed
  - `deep-research` ↔ `academic-paper` ↔ `academic-paper-reviewer` ↔ `academic-pipeline`

## [2.9] - 2026-03-27

### Added
- **Style Calibration** — learn the author's writing voice from past papers (optional, intake Step 10)
- **Writing Quality Check** — checklist catching overused AI-typical patterns (renamed from AI Writing Lint)
- Information Systems Basket of 8 journals added to academic-paper reference list
- Copilot philosophy tagline to README EN + zh-TW
- Substack guide articles to both READMEs

### Fixed
- Skill Details section version numbers and agent descriptions updated
- /simplify review — stale refs, lint sweep efficiency, schema fields
- Removed last v4.0 reference in CHANGELOG

## [2.8] - 2026-03-22

### Added
- **SCR Loop Phase 1** — State-Challenge-Reflect mechanism integrated into Socratic Mentor Agent
  - Commitment gates at layer/chapter transitions (collect user predictions before presenting evidence)
  - Certainty-triggered contradiction (probes high-confidence statements with counterpoints)
  - Adaptive intensity (tracks commitment accuracy, adjusts challenge frequency)
  - Self-calibration signal (S5) for convergence detection
  - SCR Switch — users can disable/re-enable predictions mid-dialogue
- `deep-research/agents/socratic_mentor_agent.md` — SCR Protocol section with commitment gates, divergence reveal, and adaptive intensity
- `deep-research/references/socratic_questioning_framework.md` — SCR Overlay Protocol mapping SCR phases to Socratic functions
- `academic-paper/agents/socratic_mentor_agent.md` — Chapter-level SCR Protocol with per-chapter commitment questions and cross-chapter pattern tracking

## [2.7.3] - 2026-03-10

### Fixed
- Version badge corrected in both EN and zh-TW READMEs

## [2.7.2] - 2026-03-10

### Added
- Version, license, and sponsor badges to README
- zh-TW README badges

## [2.7.1] - 2026-03-10

### Fixed
- Buy Me a Coffee username corrected

## [2.7] - 2026-03-09

### Added
- Integrity Verification v2.0: Anti-Hallucination Overhaul
- Full academic research skills suite (4 skills, 116 files)
- Deep Research v2.3 — 13-agent research team with 7 modes
- Academic Paper v2.4 — 12-agent paper writing with LaTeX hardening
- Academic Paper Reviewer v1.4 — Multi-perspective peer review with quality rubrics
- Academic Pipeline v2.6 — 10-stage orchestrator with integrity verification
