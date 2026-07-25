# AI Disclosure — Implementation Spec

**Status:** READY (Decision Doc 11-round audit-trail-complete; this spec resolves §4.4 11 open concerns per user-decision protocol)
**Date:** 2026-05-14
**Issue:** [#108](https://github.com/Imbad0202/academic-research-skills/issues/108)
**Branch:** `feat/108-ai-disclosure-renderer`
**Author:** Cheng-I Wu
**Blocked-by:** Decision Doc `docs/design/2026-05-14-ai-disclosure-schema-decision.md` ([commit 20ed72d](https://github.com/Imbad0202/academic-research-skills/commit/20ed72d), PR #109, closed-by-merge)
**Scope:** Translate Decision Doc §4.1 implementation map + §4.3 invariants + §4.4 11 open concerns into an ARS-conventional implementation plan with file paths, test discipline, and decision provenance.

---

## 0. How to read this document

The Decision Doc decides **what** (G1–G10 outcomes + 8 frozen invariants + 11 open concerns the implementation must resolve). This implementation spec decides **how** in ARS's actual deployment shape — protocol prose for LLM execution, anchor-data reference tables, lint validators (Python), and structured conformance fixtures (Python). There is no Python renderer module in ARS today; the v3.2 `disclosure` mode is LLM-orchestrated prose, and this implementation extends that pattern rather than introducing runtime renderer code.

For every §4.4 concern, this spec cites the resolution path (user-chosen or inline) and the rationale, so the implementation work is auditable downstream.

---

## 1. ARS-specific deployment shape (correcting "renderer" terminology)

The Decision Doc uses "renderer" as a layer-abstract term. In ARS the realisation of that layer is:

| Decision Doc term | ARS realisation | File type |
|---|---|---|
| renderer (LLM-executed) | Protocol prose the LLM reads at runtime when in `disclosure` mode | Markdown protocol doc under `academic-paper/references/` |
| anchor policy table | Structured reference table of verbatim policy quotes the LLM looks up | Markdown reference doc under `academic-paper/references/` |
| renderer tests | Static-content lint validators **plus** structured input/output conformance fixtures | Python `scripts/check_*.py` + `scripts/test_*.py` (unittest) |
| renderer input contract | Prompt-time inputs documented in the protocol doc + signal hooks (e.g., `slr_lineage`, `policy_anchor`, `venue`) the upstream pipeline sets | Documented in protocol doc; lint-validated against schema |
| de-dup mandate vs v3.2 Nature venue renderer | Single Nature policy table imported into both v3.2 venue path (existing `venue_disclosure_policies.md`) and new anchor path (new `policy_anchor_table.md`) | Cross-reference + lint guard preventing drift |

This terminology mapping is **load-bearing** for the test design: ARS lint validators check protocol prose against anchor-data tables; ARS conformance fixtures simulate LLM-input-shape and assert the protocol-encoded decision the LLM should produce per §3 G10 7-row table and §4.3 invariants.

---

## 2. File map (locks in scope discipline)

### 2.1 New files

| Path | Responsibility |
|---|---|
| `academic-paper/references/policy_anchor_table.md` | 4 anchor tables (PRISMA-trAIce / ICMJE / Nature / IEEE) × 16 fields, each cell carrying verbatim policy quote + snapshot ref mirroring discovery doc §3 provenance |
| `academic-paper/references/policy_anchor_disclosure_protocol.md` | LLM-execution prose: 4 anchor-conditioned render flows + lookup mechanism + §3 G10 7-row decision table + §4.3 invariants + §4.4 11 resolved concerns + auto-promotion forbiddance |
| `scripts/check_policy_anchor_table.py` | Static lint: each anchor has all 16 fields; each cell has verbatim policy quote + snapshot ref; Nature cell content equals the source-of-truth shared with v3.2 venue renderer (de-dup guard); `ai_used: true` substantive-content forbiddance encoded |
| `scripts/check_policy_anchor_protocol.py` | Static lint: protocol doc references each §4.3 invariant by name; §4.4 11 concerns each have a resolved-path section; 7-row precedence table preserved verbatim from Decision Doc §3 G10; auto-promote-UNCERTAIN forbiddance present |
| `scripts/test_policy_anchor_disclosure.py` | Conformance unit tests: each §4.3 invariant + each §4.4 #1–#11 resolved path has at least one positive fixture; each forbidden path has at least one negative fixture that raises `AssertionError` or returns `non-conformant` decision |
| `scripts/test_check_policy_anchor_table.py` | Validator mutation tests: assert lint fails on each of (missing field cell / missing verbatim quote / missing snapshot ref / drift from Nature source of truth) |
| `scripts/test_check_policy_anchor_protocol.py` | Validator mutation tests: assert lint fails on each of (missing invariant name / missing §4.4 concern resolution / 7-row table drift / missing forbiddance clause) |

### 2.2 Modified files

| Path | Change |
|---|---|
| `academic-paper/references/disclosure_mode_protocol.md` | Phase 1 intake branches on `--venue` vs `--policy-anchor` selectors; Phase 3+4 delegates to `policy_anchor_disclosure_protocol.md` when anchor mode; venue+anchor conflict → reject (§4.4 #7); v3.2 venue lookup path unchanged |
| `academic-paper/SKILL.md` | `## v3.7.3 …` and `## v3.7.0 …` style block added: `## #108 Policy-Anchor Disclosure Renderer Protocol` describing protocol doc cross-reference + new lints + new test counts |
| `.github/workflows/spec-consistency.yml` | New steps invoking 3 new validators + 3 new test files |
| `.claude/CLAUDE.md` | Add #108 entry under existing "v3.7.3 / v3.7.0" block in the suite-level section: "AI-disclosure renderer protocol (no schema change; renderer is LLM-prose; 4 policy anchors)" |
| `CHANGELOG.md` | New `[Unreleased]` bullet documenting (a) no migration needed (G1+G6), (b) added files list, (c) cross-ref Decision Doc + this spec |

### 2.3 Files explicitly NOT changed (Decision Doc §4.1 items 1–5)

| Path | Decision Doc citation |
|---|---|
| `shared/contracts/passport/literature_corpus_entry.schema.json` | §4.1 #1 — G1 no-add |
| `shared/handoff_schemas.md` | §4.1 #2 — Schema 9 fields used as-is |
| `deep-research/agents/bibliography_agent.md` | §4.1 #3 — no entry-level disclosure to emit |
| `academic-paper/agents/literature_strategist_agent.md` | §4.1 #3 — no entry-level disclosure to emit |
| `scripts/check_ai_disclosure_schema.py` | §4.1 #4 — not created (no schema to validate) |
| Any migration tooling | §4.1 #5 — no migration needed |

---

## 3. §4.4 11 open concerns — resolved paths

Each row cites whether the resolution is **user-chosen** (decided via AskUserQuestion in this implementation session) or **inline** (decided by this spec author using standard engineering judgement bounded by the Decision Doc's stated forbiddances).

| # | Concern | Resolution | Source | Rationale |
|---|---|---|---|---|
| 1 | Track-selection lookup mechanism | **(b) explicit `slr_lineage` input** | User-chosen | Simplest + most testable. Pipeline orchestrator sets `slr_lineage=true|false` based on whether any SLR-mode stage appears in the run history; renderer reads the flag without chasing `upstream_dependencies`. Cold-start manual invocation requires explicit `mode=` parameter (silent fallback to general track forbidden per §4.3 G2 invariant). |
| 2 | Tool identity collection path | Auto-detect from session metadata (mirror v3.2 Phase 4); explicit fallback per tool when session metadata absent | Inline | v3.2 `disclosure_mode_protocol.md` already auto-detects Claude model version per Phase 4 note; reuse the same pattern. When the pipeline log is absent (cold-start) or the AI tool is non-Claude (cross-tool pipelines), prompt user per tool. |
| 3 | Per-(tool × task) prompt-scope record format | Per-(tool × task) tuple: each PRISMA-trAIce stage (search / screening / data extraction / Risk of Bias / synthesis / drafting) × each tool gets its own prompt record; missing tuples emit "not supplied" annotation per tuple, not per tool | Inline | PRISMA M6.a says verbatim "for each specific task"; per-tool aggregation would lose the per-task granularity the framework mandates. Test fixture covers the (tool × task) → annotation mapping. |
| 4 | IEEE section locator shape | Free-form list with recommended IMRaD exemplars (parallel to G8 `level_of_involvement` design) | Inline | IEEE #6 verbatim language ("specific sections of the article that use AI-generated content shall be identified") invites narrative; a closed enum over-constrains. Recommended exemplars (`"Introduction" | "Methods" | "Results" | "Discussion" | "Abstract" | "Title" | other-free-form`) provide guidance without locking. Test fixture covers both exemplar-match and free-form-text inputs. Pairing with G8 `level_of_involvement` enforced per §4.3 G8 invariant. |
| 5 | Nature image metadata + labelling channel | **Hybrid (annotation block + suggested inline patches)** | User-chosen | Renderer emits two outputs: (a) standalone `image_disclosure_instructions.md` block — anchor-specific, per-image, with carve-out classification and Nature label text; (b) a suggested patch diff against manuscript source figure metadata for the author to optionally apply. Implementation note: the patch diff is **suggested-only**; ARS does not modify manuscript source autonomously. Test fixture covers both outputs are present in Nature anchor renders. |
| 6 | UNCERTAIN per-facet finalization rule | **(b) USED facets full + UNCERTAIN per-facet annotation** | User-chosen | Row 4 of §3 G10 table emits the full anchor-specific disclosure; USED categories render at full strength; each still-UNCERTAIN category surfaces a per-facet `"AI disclosure pending — category {X} not confirmed; resolve via v3.2 Phase 2"` annotation immediately after the facet's render slot. **Forbidden** (Decision Doc invariant): rendering a still-UNCERTAIN category as though USED in any anchor output. |
| 7 | Venue + anchor conflict resolution | **Reject conflicting selectors with error** | Inline | Most transparent path. When `--venue=<v>` and `--policy-anchor=<a>` both supplied and the two map to incompatible policies (e.g., `--venue=Nature` selects v3.2 Methods placement vs `--policy-anchor=IEEE` selects acknowledgments-only placement), renderer refuses with explicit error message listing the policy conflict. Per Decision Doc §4.4 #7: silent precedence is forbidden. Test fixture covers conflict-rejection + consistent-pair-pass. |
| 8 | Three-state input completeness flag full spec | Computed from `ai_used` input + each v3.2 category state per row 1–7 preconditions; partial-state composition per #6 (b) | Inline | Field-level computation: (a) `ai_used` ∈ {true, false, unset}; (b) each v3.2 category ∈ {USED, NOT USED, UNCERTAIN, not-supplied}; (c) first-match-wins evaluation across §3 G10 7 rows; (d) row-4 partial-state per #6 (b). Test fixture covers all (ai_used × category-state) combinations distinguishing rows. |
| 9 | Test set scope | Cover §4.3 8 invariants + §4.4 #1–#8 + #10 + #11 each positive + negative path | Inline | Test count: ≥ 8 invariant tests + 11 concern tests × {positive, negative} = ≥ 30 conformance tests. Per concern: each acceptable implementation path needs a positive test demonstrating it works; each forbidden path needs a negative test demonstrating it fails. Plus validator mutation tests per `test_check_*.py`. |
| 10 | `ai_used: true` substantive-content gate | **(a) Force v3.2 categorization flow** | User-chosen | bare `ai_used: true` (no USED category supplied) treated as prompt-trigger: renderer halts current run with a prompt asking user to complete v3.2 Phase 2 categorization before any anchor render emits. Once categories supplied, re-evaluate against §3 G10 7-row table. Test fixture covers bare-flag halt + post-categorization re-evaluation. Consistent with #6 (b): both choices preserve "honest signal over silent guess" as the design principle. |
| 11 | G1 invariant scope narrowing | §2.1 G1 Decision authoritative ("no `ai_disclosure` field added to corpus entry schema"); non-renderer code changes needed for §4.4 #1 (e.g., pipeline orchestrator setting `slr_lineage`) **permitted** | Inline (per Decision Doc §4.4 #11 last paragraph) | Decision Doc §4.4 explicitly says "implementation MUST treat the §2.1 G1 Decision (no schema field) as authoritative; the §4.3 invariant phrasing is to be corrected to 'data layer is untouched; non-renderer code changes needed for §4.4 concerns are permitted'". This spec adopts the corrected phrasing; the `policy_anchor_disclosure_protocol.md` cross-references this clarification. |

---

## 4. Test discipline (TDD)

Per `superpowers:test-driven-development`, every protocol-encoded behaviour and every validator rule MUST have a failing test first.

### 4.1 Per-anchor verbatim quote tests

For each of (PRISMA-trAIce × 16 fields) + (ICMJE × 16 fields) + (Nature × 16 fields) + (IEEE × 16 fields) = 64 cells:

```
RED: write test asserting cell N contains the verbatim policy quote from discovery §3 snapshot
VERIFY RED: fail (cell empty)
GREEN: populate cell with the verbatim quote
VERIFY GREEN: pass
```

### 4.2 Per-invariant conformance tests (§4.3 G1–G9)

For each of 8 invariants (G1, G2, G3+G10 composite, G4, G5, G7, G8, G9):

```
RED: write fixture asserting the protocol rejects a forbidden case + accepts an acceptable case
VERIFY RED: fail (protocol doc has not been written; lint fires on missing clause)
GREEN: encode the protocol clause + lint rule
VERIFY GREEN: pass
```

### 4.3 Per-concern resolved-path tests (§4.4 #1–#8 + #10 + #11)

For each concern, both positive and negative paths must have a fixture (per row 9 above).

### 4.4 De-dup guard test (Nature anchor ↔ v3.2 Nature venue)

```
RED: write fixture asserting policy_anchor_table.md Nature cells and venue_disclosure_policies.md Nature cells are byte-equivalent (single source of truth)
VERIFY RED: fail (no shared content yet)
GREEN: extract Nature policy content to shared/policy_data/nature_policy.md, both consumers import from there
VERIFY GREEN: pass
```

### 4.5 967-test baseline regression test

Per #108 acceptance #6: full `spec-consistency.yml` workflow steps run locally and produce **no new failures** versus the v3.7.3 baseline (967 pass / 3 skipped / 0 failed). New tests are additive.

---

## 5. Implementation order (locked)

The order minimises cascade-fix risk per `feedback_inventory_pattern_for_codex_fix_cascade.md`: define data first (anchor table = source of truth), then protocol consuming the data, then extension wiring, then tests covering both data and protocol.

1. **`policy_anchor_table.md`** + `check_policy_anchor_table.py` + `test_check_policy_anchor_table.py` (Task #4) — TDD: write lint validator + mutation tests first, watch fail; populate table to pass.
2. **`policy_anchor_disclosure_protocol.md`** + `check_policy_anchor_protocol.py` + `test_check_policy_anchor_protocol.py` (Task #5) — TDD: write lint validator + mutation tests first, watch fail; populate protocol to pass.
3. **Extend `disclosure_mode_protocol.md`** (Task #6) — TDD: extend `check_policy_anchor_protocol.py` to also assert v3.2 extension points; modify v3.2 doc; verify lint passes.
4. **Conformance fixtures `test_policy_anchor_disclosure.py`** (Task #7) — TDD per §4 above for invariants + concerns.
5. **Wire CI** (Task #8) — add validator + test steps to `spec-consistency.yml`.
6. **Regression baseline** (Task #9) — run full suite; confirm 967 + new tests; 0 failures.
7. **Codex review** (Task #10) — ≥ 3 rounds → 0 P1/P2.
8. **CHANGELOG + PII scan + simplify + PR** (Tasks #11–#14).

---

## 6. Test count expectation (for #108 acceptance criterion #6 framing)

| Test surface | Count (lower bound) |
|---|---|
| Anchor table content tests (cell verbatim + snapshot ref) | 64 cells × 2 assertions = 128 |
| Validator mutation tests (`test_check_policy_anchor_table.py`) | 8 negative paths × 1 assertion = 8 |
| Validator mutation tests (`test_check_policy_anchor_protocol.py`) | 11 negative paths × 1 assertion = 11 |
| Invariant conformance tests (G1–G9) | 8 invariants × {positive, forbidden} = 16 |
| Concern conformance tests (#1–#8, #10, #11) | 10 concerns × {positive, negative} = 20 |
| De-dup guard test (Nature anchor ↔ venue) | 1 |
| **Total new tests (lower bound)** | **184** |

Final regression target: 967 baseline + ~184 new = ≥ 1151 pass / 3 skipped / 0 failed. The "lower bound" qualifier is intentional — implementation may surface additional edge cases warranting extra tests; the §4.3 invariant set bounds the floor.

---

## 7. Codex review expectation

Per Decision Doc §5 closure note: implementation is code + doc, not pure cross-reference; expected to converge faster than the Decision Doc's 11-round high-water mark. Target: ≥ 3 rounds → 0 P1/P2. Trigger conditions for surfacing architectural inflection to user (per `feedback_lint_cap_rule_when_lexical_enumeration_loops` and `feedback_llm_defect_class_problems_may_have_no_current_fix`):

- R5+ still produces 3+ P2 with no net downward trend across rounds R3 → R5 → R7 → ...
- Each fix at one section surfaces a stale reference / new conflict at another (whack-a-mole pattern).

Hitting either trigger ⇒ stop and ask user whether to accept audit-trail-complete framing (like Decision Doc R11) or push further.

---

## 8. Public-repo boundary discipline

This is a public repository. Pre-push gates:

1. `grep -rn` for the private-org and private-project tokens enumerated in the maintainer's local boundary deny list — block on hit (Springer is **legal** anchor scope per Decision Doc §4.5 / §4.6).
2. Run the maintainer's local boundary-check script against the repo root — block on hit.
3. `/codex review` + `/security-review` parallel: both must produce 0 P1/P2 before merge.

---

## 9. Related

- Decision Doc (this spec's parent): `docs/design/2026-05-14-ai-disclosure-schema-decision.md`
- Discovery doc (provenance for anchor verbatim quotes): `docs/design/2026-05-13-ai-disclosure-schema-discovery.md`
- v3.2 disclosure mode protocol (the file this spec extends): `academic-paper/references/disclosure_mode_protocol.md`
- v3.2 venue disclosure policies database (source of truth Nature must de-dup against): `academic-paper/references/venue_disclosure_policies.md`
- v3.7.3 trust-chain infrastructure (not invoked, but Dimension A5 reservation noted in Decision Doc §1.3): `docs/design/2026-05-12-ars-v3.7.3-claim-faithfulness-and-contaminated-source-spec.md`
- #108 (implementation issue, this spec produced under)
