# AI Disclosure Schema — Decision Document

**Status:** READY (11-round codex review complete; 2 deep P2 documented as §4.4 open concerns #10 + #11 for the implementation issue). Acceptance per #108 criterion #4 reinterpreted from "≥2 rounds → 0 P1/P2" to **"audit-trail complete; deep P2 contract gaps captured as open concerns the implementation issue MUST resolve"** — see §5 closure notes for the reinterpretation rationale.
**Date:** 2026-05-14
**Issue:** [#108](https://github.com/Imbad0202/academic-research-skills/issues/108)
**Author:** Cheng-I Wu
**Blocked-by:** discovery doc shipped 2026-05-13 ([commit 299c4b6](https://github.com/Imbad0202/academic-research-skills/commit/299c4b6), PR #107, closed #106)
**Scope:** Decision — answers G1–G4 load-bearing gates + G5–G10 secondary questions for the implementation issue (#108). Does NOT itself implement.

---

## 0. How to read this document

This document **decides** the implementation direction the discovery deliberately left open. It does not re-litigate the matrix or the design space; both are owned by the discovery doc (`docs/design/2026-05-13-ai-disclosure-schema-discovery.md`). For every decision below the doc:

1. Cites the §5 trade-off table row(s) chosen.
2. Names the weakness of the chosen option (per #108 Anti-goals — choosing an option without naming its weakness is a design regression).
3. Names why the alternative §5 options were not chosen, including their respective weaknesses (so the asymmetry is auditable).
4. States the implementation-surface impact at the end (§4) so #108's provisional surface list can be confirmed or trimmed.

**Honest about uncertainty:** the discovery doc kept four credible outcomes on the table (single-anchor verbatim alignment / hybrid / defer to renderer / retain minimal). The decision below selects **one** of those outcomes as the primary direction and explicitly classifies the others as not chosen. The decision is **not** "hybrid by default"; per #108 Anti-goals, that assumption is explicitly disallowed.

---

## 1. Framing context

Three framing questions had to be settled before the G-gates could be answered without bias. They are stated here so reviewers can see the inputs feeding each decision.

**Fact-check correction (load-bearing for G1, G3, G6, G10):** the discovery doc's §1 background characterizes ARS as having a "minimal `ai_disclosure` field (boolean / narrative)". Inspecting `shared/contracts/passport/literature_corpus_entry.schema.json` (current `main`) shows this is not accurate — the schema is `additionalProperties: false` and carries **no** `ai_disclosure` property. The status-quo is therefore "no entry-level AI-disclosure field at all", not "a minimal field that already exists". This correction propagates: the G1 "retain status-quo" option is "do not add the field", not "keep an existing field"; G3 D3 "soft + legacy marker" applies to renderer-input absence, not to legacy entry-level data; G6 horizon is about a hypothetical future field, not an existing one; G10 "silence default" is the de facto current behaviour by data shape, not by interpretation. The G-gate answers below state this explicitly where it matters.

### 1.1 Who is ARS's primary user?

Inputs: `.claude/CLAUDE.md` skill matrix; `deep-research` 7 modes; `academic-paper` 10 modes; pipeline orchestrator topology.

**Finding:** ARS spans three audience surfaces — SLR researcher (deep-research `systematic-review` mode, one of seven modes), academic-paper author (the dominant downstream surface across plan / full / revision / disclosure / abstract / format-convert / citation-check modes), and reviewer / methodologist (`academic-paper-reviewer`). The **majority workflow is general writing**, not SLR-specific. SLR mode is a single mode in deep-research; every other ARS mode is venue-agnostic with respect to disclosure.

**Implication for the G-gates:** an SLR-centric schema or stage taxonomy would over-fit a minority workflow. The discovery's 4-anchor matrix already encodes this asymmetry — PRISMA-trAIce is the only anchor with item-level granularity, but it carries 0 mandate cells (pre-Delphi) and applies only when the AI tool is methodological-in-SLR (conditional-mandate framework-level; §4.3 caveat).

### 1.2 How does v3.2 `disclosure` mode integrate?

Inputs: `academic-paper/references/disclosure_mode_protocol.md`; v3.2 entry in `.claude/CLAUDE.md`.

**Finding:** v3.2 `disclosure` mode is already a **venue-aware narrative renderer**, not a schema. Its inputs are (a) the paper draft, (b) target venue, (c) AI usage categories detected from the pipeline log; its output is a venue-specific disclosure paragraph plus placement instructions. The v1 policy database covers six venues (ICLR / NeurIPS / Nature / Science / ACL / EMNLP). The lookup axis is **venue**, not **policy anchor** — only Nature overlaps with the 4-anchor matrix.

**Implication for the G-gates:** v3.2 occupies the **render layer**, not the data layer. A new `ai_disclosure` schema in the corpus / bibliography entries would operate at a different layer (per-entry AI usage records inside the literature corpus). The two are not in competition; they can coexist or one can absorb the other. The G1 decision must say which.

### 1.3 Does v3.7.3 trust-chain infrastructure complement or constrain this?

Inputs: `docs/design/2026-05-12-ars-v3.7.3-claim-faithfulness-and-contaminated-source-spec.md`; v3.7.3 entry in `.claude/CLAUDE.md`.

**Finding:** v3.7.3 ships `<!--anchor:<kind>:<value>-->` annotations after `<!--ref:slug-->` for **claim-level provenance** (which sentence in the source backs this claim). Its `<kind>` enum is `{quote, page, section, paragraph, none}` — none of which is `ai_stage` or `tool_id`. v3.7.3's spec explicitly defers "AI disclosure schema split" to a separate disclosure-protocol PR (`docs/design/2026-05-12-…v3.7.3…-spec.md` line 236).

**Implication for the G-gates:** v3.7.3 is **available infrastructure**, not a precondition. A G1 answer that uses Dimension A5 (event-log linked to v3.7.x trust-chain anchors) is supported by v3.7.3; a G1 answer that does not is unaffected by it. The discovery doc §1 point 1 phrases this as "hypothesized as a complement on the production side, but should be tested rather than assumed" — the decision below tests it explicitly.

---

## 2. Load-bearing decisions (G1–G4)

### 2.1 G1 — Single-anchor vs hybrid vs deferred vs status-quo?

**Question source:** #106 §2 + Q1 + Q6.

**Matrix evidence (recap; full evidence in discovery doc §4.3–4.6 + §5.1, §5.3):**

- 4 anchors disagree at the field level: PRISMA-trAIce 0 mandate / 10 recommend (pre-Delphi); ICMJE 2/2 with 9 not-addressed; Nature 3/2 with 7 not-addressed; IEEE 4/1 with 9 not-addressed. **No single anchor covers 16 of 16 fields at mandate strength.**
- 4-anchor #14 disclosure-location enums have **empty intersection** (§4.5 + §4.6 cross-anchor observation; §5.3 matrix evidence).
- Per §5.3 evidence bullet 4, the copyediting carve-out has anchor-specific strength semantics (Nature eliminate vs IEEE downgrade).
- Per framing §1.1, ARS users are predominantly venue-targeting, not anchor-targeting.

**Decision: Defer policy mapping to a renderer layer (Dimension C, option C4).** No `ai_disclosure` field is added to `literature_corpus_entry.schema.json` at this issue; all policy work happens in the renderer. This corresponds to outcome 3 from #106 §2 (defer to renderer) as the primary direction, plus the schema-layer position of outcome 4 (no new schema field) as a side effect of "renderer-only investment". **Fact check baseline:** the corpus entry schema today (`shared/contracts/passport/literature_corpus_entry.schema.json`, `additionalProperties: false`) has *no* `ai_disclosure` property — discovery doc §1 phrases the current shape as "boolean / narrative", but the actual schema does not carry it. The G1 decision is therefore **not** "retain a field that already exists"; it is "explicitly opt to **not** add the field at this issue, while answering G2–G10 in a way that does not require it". A future issue may revisit the schema-layer question (see §2.1 C5 contingent reservation); this issue does not.

**Cited §5.3 row:** C4 alignment-depth H / schema-simplicity H / backward-compat-burden H / integration-cost M.

**Weakness named (per Anti-goals):** the discovery doc's own §5.3 wording: *"Audit-quality depends on renderer correctness, not data correctness — bug in renderer breaks all venue alignments at once."* The schema-layer audit becomes weaker because the data does not encode which anchor's policy is being satisfied; correctness moves to the renderer artifact. This is a real cost, partially mitigated by the ARS post-v3.7.3 codex review discipline (11-round convergence on v3.7.3 spec; 967-test regression baseline) but not eliminated by it. A future renderer regression that silently misroutes anchor policy would not be caught by schema-layer validation; renderer-layer tests have to bear that load instead.

**Why not the other §5.3 options:**

- **C1 (single declaration_mode)**: §5.3 weakness — *"strict / lenient hides which anchor's strictness; ambiguous at audit time. Copyediting carve-out is one bit, losing eliminate-vs-downgrade distinction."* Trade-off table row C1 alignment-depth **L**. Loses the §4.5 #15 / §4.6 #15 split entirely.
- **C2 (carve-out list)**: §5.3 weakness — *"Cannot express Nature #16 default-deny regime — that is a mandate, not a carve-out."* Trade-off row C2 alignment-depth **M** at the carve-out facet, but **L** for the image-rights regime (§4.5 #16) which is mandate-strength in Nature.
- **C3 (multi-field separation)**: §5.3 weakness — *"Schema has 4+ correlated fields that may drift … Validator burden is high."* Trade-off row C3 schema-simplicity **L**. Buys some auditability at high schema cost; the cost is not justified when the matrix already lacks intersection across anchor location enums.
- **C5 (versioned policy-profile)**: §5.3 weakness — *"Profile registry is a separate artifact to maintain."* Trade-off row C5 alignment-depth H but schema-simplicity **M**. C5 is **plausible** and the closest credible alternative to C4 — it preserves the deferred policy mapping but pins it to a named, versioned profile. Not chosen at this gate because the framing §1.2 finding (v3.2 already supplies a venue-keyed lookup) means policy-profile pinning at the **corpus entry level** would duplicate the renderer-side policy registry. Adding a per-entry `policy_profile` field also reintroduces schema change, contradicting the G1 outcome 4 component. **Contingent reservation:** if a future ARS user reports that anchor pinning at entry-level is needed for audit (e.g., compliance reporting), C5 is the documented upgrade path — see also §4 out-of-scope item 3 and §5 closure notes.

**Why not the other #106 §2 outcomes:**

- **Single-anchor verbatim alignment**: per §5.5 matrix evidence and §5.3 location-enum-disjoint finding, picking one anchor loses the others' mandate cells. Whichever anchor is picked, the schema misaligns with the other three at the location level — and in the case of ICMJE / Nature / IEEE, also at mandate-level fields the unchosen anchors uniquely require (Nature #16 image rights, IEEE #6 section locator, ICMJE #10 human-responsibility statement). Weakness severe enough that no single-anchor alignment satisfies more than 1 of 4 anchors' #14 location enum.
- **Status-quo only (retain minimal)**: this is the schema-layer component of the chosen direction. As a *complete* outcome it is rejected because it would leave the discovery doc's §4 evidence stranded — 9 mandate cells across ICMJE / Nature / IEEE document real disclosure obligations that ARS authors face, and providing no rendering support is an under-response to that evidence. The chosen direction (defer policy to renderer) extends status-quo at the data layer by adding renderer-side investment; pure status-quo does not.
- **Hybrid (Dimension A / B / C / D / E composite chosen up-front)**: per #108 Anti-goals, "Do not assume the answer is 'hybrid'". The decision pattern that emerges from this Decision Doc is **multi-axis** (defer policy at C, two-track at B, soft legacy at D, multi-per-anchor at E) — but each axis is chosen on its own §5 evidence and each weakness named, which is the path #108 demands. Calling the resulting composite "hybrid" is a description after the fact, not an a priori commitment.

### 2.2 G2 — Stage taxonomy approach (B1–B5)?

**Question source:** Q2.

**Matrix evidence:**

- §5.2 evidence bullets 1–4: PRISMA-trAIce explicit 6-stage enum; ICMJE / Nature / IEEE use unstructured stage language; IEEE #4 "level" reads as degree-of-involvement, not workflow stage; PRISMA-trAIce M6 prompt rule is tool-type-conditioned independent of stage.
- §4.6 IEEE matrix #4 / #5 distinction: #5 ("specific sections … and a brief explanation regarding the level") is explicit-mandate; #4 ("level at which the AI system was used") is implicit because "level" semantically diverges from workflow stage (degree-of-involvement vs stage). A schema that conflates the two misaligns with IEEE at the semantic layer.
- Per framing §1.1, SLR-only stage taxonomy would over-fit minority workflow.

**Decision: Two-track by mode (Dimension B, option B4).** `systematic-review` work renders with the PRISMA-trAIce 6-stage enum (search / screening / data extraction / Risk of Bias / synthesis / drafting); all other work renders with a 4-stage general taxonomy (research / drafting / revision / copyediting). The track decision is made at **renderer entry**. Dispatch must be **SLR-lineage-aware**, not directly-producing-mode-only: the documented `deep-research systematic-review → academic-paper full` handoff means the directly-producing artifact's `origin_mode` is `full`, but the SLR work it carries still warrants the PRISMA-trAIce track. The dispatch resolves SLR lineage via the §2.2 weakness paragraph below + §4.4 concern #1; the **invariant** is that SLR work routes to PRISMA-trAIce regardless of the directly-producing mode label.

**Cited §5.2 row:** B4 alignment-depth **H** / schema-simplicity **L** / backward-compat-burden **M** / integration-cost **M**.

**Weakness named:** the discovery doc's own §5.2 row text: *"Schema is most complex — two enums in one schema gated by mode. Mode-detection logic must be reliable."* In this Decision Doc's G1-defer direction, **the complexity moves from schema to renderer**, which mitigates but does not eliminate the cost — the renderer must implement two enums and pick correctly per mode.

The track-selection input cannot be the directly-producing `origin_mode` alone. The documented ARS handoff path `deep-research systematic-review → academic-paper full` produces a paper-stage artifact whose `origin_mode` is `full`, not `systematic-review`; reading `origin_mode` in isolation would route a systematic review's manuscript to the general track and skip the PRISMA-trAIce stages that the SLR work product actually warrants.

Schema 9 does not carry a "lineage mode" field, and `upstream_dependencies` is defined as a list of *version labels* (e.g., `synthesis_v1`, `research_v1`) — not mode names. Concretely, the renderer must:

1. **Read the current passport's `origin_mode`** (required field). If it equals an SLR mode identifier (e.g., `systematic-review`), select the PRISMA-trAIce track and stop.
2. **If `origin_mode` is not an SLR identifier**, iterate `upstream_dependencies` (if present) and **resolve each version label to its own producing passport** (lookup mechanism: the passport ledger / artifact registry that already maps version labels to artifacts in the pipeline). For each resolved upstream passport, read **that passport's `origin_mode`**. If any upstream passport's `origin_mode` is an SLR identifier, select the PRISMA-trAIce track.
3. **If neither the current passport nor any resolved upstream passport indicates SLR**, the general track applies.
4. **If the renderer runs outside a pipeline (no passport at all)**, an explicit `mode=<value>` input parameter is mandatory — silent fallback to the general track on missing input would hide the SLR-vs-general decision.

The lookup in step 2 is **non-trivial** — it requires that the artifact registry / passport ledger expose a version-label-to-passport resolver. If that resolver is not already available in the existing ARS pipeline infrastructure at implementation time, the implementation issue must add it OR fall back to an **explicit `slr_lineage=true|false` renderer input** that the upstream pipeline orchestrator sets when an SLR-mode stage is in the run history. The Decision Doc takes no position between the two implementations; either is acceptable as long as the SLR-track selection no longer relies on (a) `origin_mode` alone or (b) literal mode strings appearing inside `upstream_dependencies`.

The residual weakness after the two-signal check: renderer-internal duplication — any anchor policy update that changes the SLR stage list (e.g., a future PRISMA-trAIce Delphi consensus revising M3.a) must be reflected in both the SLR track and any cross-references in the general track. A drift-detection lint at the renderer level is the mitigation that should accompany B4 implementation.

**Why not the other §5.2 options:**

- **B1 (closed enum, PRISMA-shaped)**: §5.2 row weakness — *"Aligns with PRISMA-trAIce only; ICMJE/Nature/IEEE are agnostic so any closed enum is compatible at the policy layer, but a PRISMA-shaped enum may surprise non-SLR authors."* Trade-off alignment-depth **M** and would force non-SLR authors into SLR vocabulary. Per framing §1.1 finding (majority workflow is non-SLR), B1 violates the user-population reading.
- **B2 (open enum)**: §5.2 row weakness — *"Auditability low — same stage may appear under 5 different labels across the corpus."* Alignment-depth **L–M**. Defeats the renderer's ability to map stage → anchor location.
- **B3 (closed enum + `other_label` escape hatch)**: §5.2 row weakness — *"escape hatch encourages unsystematic use."* Alignment-depth **M**. Carries B1's PRISMA-shape but with an audit-loss safety valve; the safety valve undoes the audit gain.
- **B5 (hierarchical)**: §5.2 row weakness — *"Schema complexity is highest of the five options."* Schema-simplicity **L**. Alignment-depth M–H. B5 is the **closest credible alternative to B4** — the top-level (research / production / review) would satisfy ICMJE / Nature / IEEE without committing to PRISMA-trAIce, and substage aliases would absorb SLR. Not chosen at this gate because (a) B5's added expansion surface (top-level + substage + future anchor groups) is unmotivated at the current 4-anchor scope, and (b) B4's two-track semantics is **simpler to validate per-mode** (renderer chooses one enum; B5 renderer must consistently resolve top-level + substage joins). B5 becomes attractive only if a fifth or sixth anchor group is added (COPE / CSE / WAME); see §3 Q3-related notes.

**Note on IEEE #5 "level":** B4 does not model degree-of-involvement separately from stage. IEEE #5 mandate is handled at G8 below — the proposal there is to add `level_of_involvement` as a renderer-side annotation, orthogonal to the B-dimension stage track.

**Note on the framing §1.1 tension:** giving SLR its own track when framing §1.1 reads SLR as a minority workflow is *not* a contradiction. PRISMA-trAIce supplies item-level granularity (M2.a–M10) that none of the other three anchors provide; not surfacing it for `systematic-review` mode would discard a content-ceiling resource. B4 is therefore "minority workflow gets its own renderer track on its own evidence", not "minority workflow upgraded to majority". The majority general track does not pay any cost for the SLR track's existence beyond the renderer's mode-gate dispatch logic.

### 2.3 G3 — Failure mode for incomplete disclosure (D1–D4)?

**Question source:** Q4.

**Matrix evidence:**

- §5.4 evidence bullet 2: *"The 4 anchors all describe forward-looking policy: none of them obligate retrospective disclosure of past AI use."*
- §5.4 evidence bullet 4: *"PRISMA-trAIce has zero mandate strength because it is pre-Delphi. A schema that rejects entries lacking PRISMA-shaped fields would treat a not-yet-formal-consensus framework as binding. Over-strict."*
- Framing §1.2: v3.2 disclosure mode operates at render time on a paper-level basis. Per the §1 fact-check correction, corpus-level entries do **not** carry any `ai_disclosure` field today — discovery doc §1's characterization of a "minimal field" was inaccurate. The G3 question is therefore *how the renderer responds when no AI-usage input is supplied*, not *how to handle legacy entry-level data*.

**Decision: Soft + legacy marker (Dimension D, option D3), reframed for G1 defer.** Per G1, no entry-level AI-disclosure field exists today and none is being added. There is therefore no "legacy schema shape" at the entry level to detect — every existing entry is uniformly "no entry-level AI-disclosure data". The D3 *spirit* (soft + transparent marker) applies at the **renderer-input** layer instead: when the user invokes the renderer without supplying AI-usage categories (the v3.2 `disclosure` mode Phase 2 input) and the pipeline log is unavailable, the renderer **surfaces an honest "AI-disclosure status not supplied for this run"** annotation rather than halting, forcing backfill, or silently emitting a no-AI render. No pipeline halt, no forced backfill, no silent skip.

**Cited §5.4 row:** D3 alignment-depth **M** / schema-simplicity **M** / backward-compat-burden **H** / integration-cost **H**.

**Weakness named:** the discovery doc's own §5.4 row text: *"Schema adds 1 boolean + acknowledgment text."* In the G1-defer direction this **schema-side cost is not paid** — no field is added. The residual weakness moves to the renderer: a user who never supplies AI-usage categories receives the "not supplied" annotation for every render, which is technically honest but may be perceived as friction. Mitigation: the v3.2 `disclosure` mode already auto-detects categories from the pipeline log when present (`disclosure_mode_protocol.md` Phase 2); the policy-anchor renderer reuses that detection path so well-instrumented pipelines do not see the friction. Cold-start manual invocations (renderer called outside a pipeline run) do see the friction and that is the correct UX — the alternative is silently rendering as if no AI was used, which §5.4 evidence bullet 4 already classifies as the worst failure mode (D4 territory).

**Why not the other §5.4 options:**

- **D1 (strict reject)**: §5.4 row weakness — *"Breaks existing pipelines until users migrate every entry. Over-strict relative to anchor scope (no anchor requires retrospective disclosure)."* Alignment-depth **M**, but the operational cost is paid by every existing user and the alignment benefit is illusory because the anchors do not require retrospective fill. Rejected because the cost is not earned.
- **D2 (hybrid storage-yes / render-no)**: §5.4 row weakness — *"Renderer output may be misleading — looks like no AI use when in fact disclosure status is unknown."* Alignment-depth **L**. Silently hiding ambiguity violates the discovery doc's "honest about uncertainty" stance; rejected on principle.
- **D4 (forced backfill)**: §5.4 row weakness — *"Most likely to produce fabricated retrospective disclosures, which violates ICMJE #10 (human-responsibility) in spirit."* Alignment-depth **L**. Worst option in the table — actively incentivizes guessing about past AI use. Rejected categorically.

### 2.4 G4 — Renderer target (E1–E4)?

**Question source:** Q6 + image-rights asymmetry.

**Matrix evidence:**

- §5.5 evidence bullet 1: *"4-anchor #14 enums do not intersect"*. Verbatim PRISMA-trAIce 6-section / ICMJE cover-letter+section / Nature Methods+caption+alt / IEEE acknowledgments-only.
- §5.5 evidence bullet 2: Nature #16 in-image-field labelling requires per-image annotation integrating with figure metadata; pure JSON/YAML output cannot satisfy it.
- §5.5 evidence bullet 3 + framing §1.2: v3.2 disclosure mode already ships 6 venue renderers (Nature is the only overlap with the 4-anchor matrix).

**Decision: Multiple per-anchor renders (Dimension E, option E2), at the policy-anchor level, parallel to v3.2's venue level.** ARS produces 4 anchor-conditioned renderers (PRISMA-trAIce / ICMJE / Nature / IEEE). v3.2's existing 6 venue renderers (ICLR / NeurIPS / Nature / Science / ACL / EMNLP) stay; the new policy-anchor renderers add a parallel lookup track keyed by anchor (not venue). Authors specify either a venue or a policy-anchor; renderer picks the matching path. Cross-track integration (Nature overlap): the Nature anchor renderer and the v3.2 Nature venue renderer share a single source-of-truth policy table (de-duplication mandate).

**Cited §5.5 row:** E2 alignment-depth **H** / schema-simplicity **M** / backward-compat-burden **H** / integration-cost **L**.

**Weakness named:** the discovery doc's own §5.5 row text: *"Maintenance burden grows with anchor set (4 today; if expansion adds 5 candidates from §4.7, that's 9 renderers). Each renderer is a separate code path that can drift from anchor policy updates."* The drift risk is real and not eliminated by the chosen direction. Mitigation: each renderer must cite a snapshot ref (mirror §3 provenance pattern from discovery) and the renderer test suite must include a snapshot-verification step that re-fetches anchor pages and diffs verbatim quotes (similar to v3.7.3's tested-content discipline). The §4.7 expansion (COPE / CSE / WAME / JAMA / PLOS) is **explicitly out of scope** for this issue; if added in a future issue, each addition must reproduce the snapshot + renderer + test bundle. Until then E2 is sized for 4 renderers, not 9.

**Why not the other §5.5 options:**

- **E1 (single ARS-native render)**: §5.5 row weakness — *"Aligns with at most one anchor — others see render that mismatches their location/format requirements."* Alignment-depth **L**. Picks one location/format and misroutes the other three. Same failure mode as G1 single-anchor: information loss disproportionate to schema savings.
- **E3 (ARS render + user template)**: §5.5 row weakness — *"Two-track UX may confuse users into thinking default render is universally venue-safe (it isn't)."* Alignment-depth **M**. The default-render risk is structurally a worse UX than E2's explicit "specify anchor or venue" — E2 forces the choice; E3 hides it behind a default that authors may accept without verification.
- **E4 (no renderer, schema-only)**: §5.5 row weakness — *"alignment-depth in delivered manuscripts is unverifiable at the ARS layer. Honest about the fact that no single render fits all venues."* Alignment-depth **M**. Honest, but pushes the entire render cost to every author for every submission. Given v3.2 already invested in venue rendering, walking that back is sunk-cost negative.

**Note on Nature #16 image rights:** the chosen E2 direction does not by itself solve the in-image-field labelling problem (the renderer would still emit a separate disclosure text block, not modify figure metadata). The renderer for the Nature anchor must additionally produce **per-image annotation instructions** (separate output channel) that the author applies manually to the manuscript source. This is a renderer-side scope decision and is explicitly flagged here so the #108 implementation does not silently drop the image-side mandate.

---

## 3. Secondary questions (G5–G10)

The six questions below shape the renderer's field set but are not first-order decisions per #108. Each is answered with a §5 / §4 / §6 cite and a one-paragraph rationale.

### G5 — Q3: Is per-stage prompt disclosure mandatory or conditional on policy choice?

**Decision:** Conditional on **three** gates, all of which must hold:

1. The renderer has selected the PRISMA-trAIce track per G2 (SLR-lineage detected).
2. `tool_type ∈ {LLM, GenAI}` (per PRISMA M6 "if any" predicate).
3. **The AI use is methodological-in-SLR** (search / screening / data extraction / Risk of Bias / synthesis / drafting per PRISMA M3.a stage enum), **not pure copyediting/editorial assistance** that would fall under the §4.5/§4.6 copyediting carve-out scope.

When all three gates fire, PRISMA-trAIce M6 prompt disclosure applies at recommend strength (*not* anchor-mandate, since PRISMA-trAIce is pre-Delphi). When gate 3 fails (e.g., SLR manuscript that only used an LLM for grammar polishing), the renderer treats the use under the G7 copyediting-carve-out path instead — eliminating prompt disclosure under Nature semantics or downgrading under IEEE semantics, depending on which anchor (if any) the author also selected. The G7 carve-out is anchor-specific, not PRISMA-track-specific.

**Rationale.** §4.3 PRISMA-trAIce M6 has explicit-recommend strength gated to "LLM/GenAI tool used" (Phase 2 closure note 5: tool-type-conditioned independent of mandate strength). The §4.3 anchor caveat scopes the entire PRISMA-trAIce framework to "AI tool used as methodological tool in an SLR" — outside that condition the framework does not apply, and #15 (copyediting exemption predicate) is explicitly not-addressed by PRISMA-trAIce because copyediting falls outside the framework's scope. A G5 gate that fires for any LLM use on the PRISMA-trAIce track (including copyediting) would over-read the framework into uses it scopes out. §4.4 ICMJE, §4.5 Nature, §4.6 IEEE all leave prompt-disclosure not-addressed; their copyediting carve-out semantics (when applicable per the anchor selected) handle the editorial-only case independently of the PRISMA gate.

The track selector is the **G2 B4 dispatch result**, not the raw `origin_mode`. Per G2, the PRISMA-trAIce track applies via lineage-aware lookup; §4.4 concern #1 lists the acceptable implementation mechanisms. Keying G5 off the *selected track* (rather than off raw mode) ensures the documented `systematic-review → academic-paper full` handoff still surfaces PRISMA M6 prompts when methodological use is present — but adding gate 3 above prevents the cross-cut where SLR-route + LLM-tool + editorial-only-use would otherwise over-mandate prompts. Q3 in §6.1 phrased the open question as exactly this gate; the answer here refines it with the methodological-use scope clause.

### G6 — Q5: Backward-compatibility horizon (as phrased in #106 Q5, "legacy boolean entries")?

**Decision:** Indefinite (no deprecation date).

**Rationale.** §5.4 evidence bullet 2 confirms no anchor obligates retrospective disclosure. Setting a deprecation date would create a fabricated forcing function unmotivated by the source policies. The G1 + G3 decision already handles the no-entry-field state via renderer-side "not supplied" honest annotation; no schema-level deprecation is required because there is no entry-level field to deprecate. If a future issue adopts a schema-layer field (e.g., the C5 versioned policy-profile per §2.1 contingent reservation), a deprecation horizon for the *new* shape's lifecycle can be set at that time. Until then there is no legacy/non-legacy boundary at the schema layer.

### G7 — Q7: Does the copyediting carve-out have semantics distinct from boolean exemption?

**Decision:** Yes — carve-out is a structured object preserving strength + location; not a boolean. The renderer-side data model: `copyediting_carveout: { strength: "eliminate" | "downgrade", preserves_location: bool, preserves_content: bool }`.

**Rationale.** §4.5 #15 (Nature, eliminate) and §4.6 #15 (IEEE, downgrade-not-eliminate) define the same field with structurally different policies — Nature drops disclosure entirely; IEEE keeps location and content but lowers strength. §6.1 Q7 specifically calls this out. A boolean `exempted_uses: [copyediting]` would silently collapse the two policies into one. The structured form documented above is sufficient to render either anchor correctly. The schema-layer impact is **none** under the G1 defer decision (the structured form lives in the renderer's anchor table, not in the corpus entry). The renderer that picks IEEE preserves location and content; the renderer that picks Nature applies eliminate.

### G8 — Q8: Should the schema model "level of involvement" separately from stage?

**Decision:** Yes, as a renderer-side annotation. New field `level_of_involvement` is added at the renderer-input level (not the corpus entry schema). Accepted values: open string (rendered verbatim) with recommended exemplars `"full drafting" | "outline only" | "paragraph-level suggestion" | "factual check" | "stylistic revision"`.

**Rationale.** §4.6 IEEE #5 is mandate strength on "a brief explanation regarding the level at which the AI system was used"; §4.6 #4 confirms "level" semantically means degree-of-involvement, not workflow stage. A renderer for the IEEE anchor that omits this field misses an explicit mandate. The G1 defer decision keeps the field out of the corpus entry schema — it lives in renderer input alongside the stage track (G2). Recommended exemplars are not a closed enum because IEEE's "brief explanation" language explicitly invites narrative; closing the enum would over-constrain. PRISMA-trAIce / ICMJE / Nature renderers may pass the field through optionally; only IEEE renders it as mandate-strength.

**Companion mandate — IEEE #6 affected sections locator.** IEEE #5 ("level") is paired with IEEE #6 ("specific sections of the article that use AI-generated content shall be identified") at the same explicit-mandate strength (§4.6 #6). G8's `level_of_involvement` alone is therefore insufficient for IEEE conformance; the renderer also needs a section-locator input identifying which manuscript sections contain AI-generated content. The **shape** of that input (closed-enum-of-IMRaD-sections vs free-form-list-with-recommended-exemplars vs some hybrid) is left to the implementation issue per §4.4 concern #4 — both shapes can satisfy IEEE #6's mandate language, and freezing the shape inside this Decision Doc was the source of one of the R5/R6 cascade contradictions. The G8 **invariant** (§4.3): an IEEE render that supplies `level_of_involvement` without a section-locator input (or vice versa) is non-conformant, regardless of how the implementation shapes either input.

### G9 — Q9: Should image-rights regimes be unified or anchor-specific?

**Decision:** Anchor-specific. Each renderer carries its own image-rights policy table. No unified data model.

**Rationale.** §4.4 ICMJE #16 (text-attribution rule, no-AI-as-primary-source — mandate), §4.5 Nature #16 (default-prohibit publication + 3 carve-outs + labelling — mandate), §4.6 IEEE #16 (fold into general acknowledgments — implicit), §4.3 PRISMA-trAIce #16 (data-handling adjacency — implicit). The §4.5 cross-anchor observation states *"the 'AI-generated image rights' field is anchor-specific enum-of-policies, not a flat boolean"*. A unified field would either (a) flatten Nature's default-deny regime into a boolean, losing the 3 carve-outs and the labelling-required flag; or (b) inflate to a max-of-anchors super-schema that over-fits authors targeting venues with lighter rules. The G1 defer + G4 E2 combination supports anchor-specific tables natively; the renderer for the Nature anchor produces the default-deny check + labelling instruction, the renderer for IEEE folds image disclosure into the acknowledgments output, the renderer for ICMJE produces the text-attribution clause, the renderer for PRISMA-trAIce passes through the data-handling note. Q9 §6.2 phrased the choice as "unify or anchor-specific"; anchor-specific is the policy-faithful answer.

### G10 — Q10: Is "no AI use" itself a disclosable statement, or is silence default-OK?

**Decision:** Silence is default-OK. Explicit `ai_used: false` is optional opt-in (renderer-input field).

**Rationale.** §5.4 evidence bullet 4 confirms the matrix is silent on this — all 4 anchors describe forward-looking obligations conditional on AI use. ARS's current entry schema does not carry any AI-disclosure field at all (G1 fact-check baseline). The G1 defer + G3 D3 combination keeps the no-AI case from being an entry-level concern; what remains is the **renderer-input** semantics, where G3 and G10 must compose cleanly.

**Three-state renderer-input contract (resolves G3 ↔ G10 composition).** This table specifies the **whole-disclosure-level** output decision (what the disclosure paragraph as a whole reads); per-facet UNCERTAIN handling inside a partial-state render is delegated to §4.4 concern #6. Rows are evaluated in priority order from top to bottom; the renderer emits the output of the **first** row whose precondition matches. Subsequent rows do not fire. The rationale for each precedence level is in the third column.

| # | Precondition (first match wins) | Whole-disclosure output | Precedence rationale |
|---|---|---|---|
| 1 | `ai_used: false` supplied AND ≥1 v3.2 category is USED (contradiction; evaluated first to catch the data-integrity bug before any other row can silently resolve it) | Honest "AI-disclosure conflict — explicit no-AI input contradicts USED category" annotation; renderer prompts the user to reconcile | Refusing to silently pick one resolution side preserves authorship accountability (mirrors the G4 venue+anchor-conflict invariant in §4.4 #7). Promoted to row 1 from R10 round to remove ambiguity between rows 2 and 4 when `ai_used:false` is paired with UNCERTAIN categories. |
| 2 | `ai_used: false` supplied AND no v3.2 category is USED AND no v3.2 category is UNCERTAIN (every supplied category, if any, is NOT USED) | "No AI was used in preparing this paper" statement (G10 opt-in path) | Explicit no-AI statement. Requires no contradicting USED (row 1 already excluded that case) and no UNCERTAIN to resolve (UNCERTAIN paired with `ai_used:false` is itself ambiguous; row 3 catches it). |
| 3 | `ai_used: false` supplied AND ≥1 v3.2 category is UNCERTAIN AND no v3.2 category is USED | Honest "AI-disclosure tension — explicit no-AI input but categories still UNCERTAIN" annotation; renderer prompts the user to resolve UNCERTAIN before emitting the no-AI statement | Distinguished from row 1 (clear USED contradiction) and row 2 (clean no-AI declaration). The author asserts no AI use but the categorization has not converged — needs reconciliation. |
| 4 | `ai_used: true` supplied OR ≥1 v3.2 category is USED, AND row 1 did not match | **Full anchor-specific disclosure render**, applying the §4.4 #6 per-facet UNCERTAIN handling rule chosen by the implementation for any *still-unresolved* UNCERTAIN categories in this run. The G3/G10 invariant (UNCERTAIN MUST NOT auto-promote to USED) constrains §4.4 #6 — acceptable per-facet rules include: prompting user to resolve all UNCERTAIN before render, surfacing per-facet "not supplied" annotations alongside USED facets, or marking the whole disclosure draft until all UNCERTAIN resolve. **Forbidden:** rendering UNCERTAIN facets as though USED. | G4 E2 + G5–G9 normal path. The Decision Doc does not pick among the per-facet alternatives; it only forbids the auto-promotion case. |
| 5 | ≥1 v3.2 category is UNCERTAIN AND no v3.2 category is USED AND no `ai_used` input (covers both "all UNCERTAIN" and "mix of NOT USED + UNCERTAIN with no USED" — *no explicit author input asserted*) | Honest "AI-disclosure status not supplied — categories pending confirmation" annotation; renderer prompts the user to run the v3.2 UNCERTAIN-confirmation flow before re-invoking | At least one category needs resolution. Distinguished from row 6 (no UNCERTAIN at all) because here the user *should* re-confirm; row 6 has no signal to confirm. |
| 6 | ≥1 v3.2 category supplied AND every supplied category is NOT USED AND no UNCERTAIN AND no `ai_used` input (de facto no-AI run, complete categorization, no explicit author opt-in) | **Silence — emit no AI-disclosure statement at all** (G10 "silence is default-OK") | G10 Decision: anchors describe forward-looking obligations conditional on AI use. When categorization is complete and uniformly NOT USED, there is nothing to disclose; emitting "not supplied" would mis-frame a positive no-use signal as a missing signal. The explicit `ai_used: false` opt-in (row 2) is available to authors who want a positive statement. **At-least-one-category-supplied guard** (added R10): vacuous match on "every supplied category is NOT USED" with an empty supplied set is excluded by this row's precondition; the empty-set case falls through to row 7 instead. |
| 7 | None of rows 1–6 match (i.e., no `ai_used` input AND no v3.2 category supplied at all — empty input across every dimension) | Honest "AI-disclosure status not supplied for this run" annotation | G3 D3 pure cold-start case: log absent; cold-start invocation with no v3.2 Phase 2 categorization performed; no input dimension carries any signal. |

**Totality.** Rows 1–7 partition every (`ai_used` × v3.2-category-state) input combination. By construction:

- `ai_used: false` → row 1, 2, or 3 (one of: contradiction / clean no-AI / UNCERTAIN tension).
- `ai_used: true` → row 4 (USED-with-row-1-excluded; if no USED category, the `ai_used:true` input itself satisfies the row-4 disjunct).
- `ai_used` not supplied → row 4 (USED present), row 5 (UNCERTAIN, no USED), row 6 (complete NOT USED), or row 7 (no categories at all).

The seven rows distinguish three "no AI declared at the disclosure-statement level" states (rows 3, 5, 7 — all "not supplied" or "tension" annotations) from one positive no-AI state (row 2 G10 opt-in) and one positive silence state (row 6 G10 default-OK). Row 4 admits a render that may still carry per-facet UNCERTAIN annotations — the table is "first match at the whole-disclosure level"; the within-disclosure facet-level annotation policy lives at §4.4 #6 and is bounded by the auto-promotion forbiddance above. Forcing every author to set `ai_used: false` would (a) over-read the anchors (none require positive no-use statements), (b) impose disclosure labour on the majority of corpus entries which involve no AI use, and (c) require adding the very entry-level field this Decision Doc just opted not to add. The row-2 opt-in path keeps the explicit-no-use statement available to authors who want it; the row-6 silence path implements G10's "default-OK" stance for unambiguous no-use runs.

---

## 4. Implementation surface impact

#108's provisional implementation surface list (7 items, "depends on direction chosen at G1–G4") is now narrowed by the G1 defer decision. **Scope discipline:** this Decision Doc freezes the G1–G10 answers and a *minimum*-shape implementation map; it explicitly does **not** freeze the renderer's input contract — that is for the #108 implementation issue to design and review against the anchor verbatim quotes in discovery doc §4. A failed attempt to fully specify the renderer input contract inside this Decision Doc (codex review rounds 3–5 surfaced cascading detail gaps with no convergence at the input-field level) confirmed that doing so was scope creep; §4.4 lists the open implementation concerns the implementation issue must address rather than pre-committing here.

### 4.1 Implementation map (load-bearing for the G-decisions)

| # | Surface | Status | Driven by |
|---|---|---|---|
| 1 | `shared/contracts/passport/literature_corpus_entry.schema.json` | **NO CHANGE** — no `ai_disclosure` field added | G1 (explicit no-add, see §1 fact-check) |
| 2 | `shared/handoff_schemas.md` | **NO CHANGE** — existing Schema 9 fields (`origin_mode`, `upstream_dependencies`) used as-is | G2 (track-selection) |
| 3 | `bibliography_agent.md` + `literature_strategist_agent.md` | **NO CHANGE** — no entry-level disclosure field to emit | G1 |
| 4 | `scripts/check_ai_disclosure_schema.py` | **NOT CREATED** — no new schema validator | G1 |
| 5 | Migration tooling | **NOT NEEDED** — no entries to migrate (no field exists today, no field added) | G1 + G6 |
| 6 | `academic-paper/references/policy_anchor_disclosure_protocol.md` | **NEW** — describes the 4 anchor-conditioned renderers, their lookup mechanism, and the de-dup mandate against v3.2 Nature venue renderer | G1 + G4 |
| 6a | `academic-paper/references/policy_anchor_table.md` (or equivalent — final filename per implementation) | **NEW** — 4 anchor tables, each carrying snapshot ref from discovery doc §3, verbatim policy quotes per field, per-anchor renderer rules | G4 + G7 + G8 + G9 |
| 6b | Renderer test suite | **NEW** — anchor-verbatim snapshot verification + G1–G10 conformance tests (see §4.3 invariants + §4.4 open concerns) | All G-gates |
| 7 | `disclosure` mode in `academic-paper` | **EXTEND** — v3.2 venue-lookup path stays; new policy-anchor lookup path added in parallel | G1 + G4 |

### 4.2 Out of scope for #108 (deferred to future issues)

- **§4.7 expansion anchors** (COPE / CSE / WAME / JAMA / PLOS): each addition reproduces the renderer + snapshot + test bundle described in item 6.
- **Dimension A5** (event-log model linked to v3.7.x trust-chain anchors): not adopted at this decision per G1 framing §1.3. May be revisited if a future use case (e.g., per-claim AI provenance for #103 v3.8 L3 audit agent) provides motivating evidence.
- **C5 versioned policy-profile pinning at corpus entry level**: held in reserve per §2.1 contingent reservation. Triggered only if compliance reporting at the entry level becomes a documented user need.

### 4.3 Decision-Doc-frozen invariants for the renderer

The renderer implementation MUST honour these G-gate outcomes; deviation requires reopening the Decision Doc:

- **G1 invariant.** No `ai_disclosure` field is added to the corpus entry schema at this issue. Renderer is the only new code path; data layer is untouched.
- **G2 invariant.** SLR mode dispatches to the PRISMA-trAIce renderer track; non-SLR modes dispatch to the general track. Whether dispatch reads `origin_mode` + chases `upstream_dependencies`, reads an explicit `slr_lineage=` input, or some combination — the implementation issue picks. The invariant is that the documented `systematic-review → academic-paper full` handoff DOES dispatch to PRISMA-trAIce; the failure mode where raw `origin_mode == full` routes SLR work to the general track is forbidden.
- **G3 / G10 invariant.** The seven-row precedence table in §3 G10 (whole-disclosure output decision; first-match-wins; rows partition every input combination by construction per the totality note) MUST hold. The auto-promotion forbiddance: an **individual** v3.2 category that is still UNCERTAIN MUST NOT be rendered as though USED in any of the four anchor outputs. Partial-state cases (≥1 USED with one or more still-UNCERTAIN) are admitted into the §3 G10 table row 4 "full anchor-specific disclosure render"; the per-facet handling of the still-UNCERTAIN categories inside that render is the implementation issue's choice per §4.4 concern #6, bounded by this auto-promotion forbiddance.
- **G4 invariant.** The 4 policy-anchor renderers (PRISMA-trAIce / ICMJE / Nature / IEEE) are implemented against the discovery doc §4 verbatim quotes. v3.2 venue renderer set stays; Nature overlap shares a single source-of-truth policy table.
- **G5 invariant.** PRISMA-trAIce M6 prompt disclosure fires only when **all three** G5 gates hold (PRISMA-trAIce track AND `tool_type ∈ {LLM, GenAI}` AND the AI use is methodological-in-SLR per PRISMA M3.a stages, **not pure copyediting/editorial assistance**). When gate 3 fails (SLR-lineage manuscript whose only LLM use is editorial), the renderer routes to the G7 copyediting-carve-out path per the §3 G5 Decision, not to PRISMA M6 prompt collection. Prompt disclosure granularity follows PRISMA-trAIce M6.a verbatim ("for each specific task"), not per-tool aggregation.
- **G7 invariant.** Copyediting carve-out semantics are anchor-specific — Nature eliminate vs IEEE downgrade-with-location-and-content-preserved. Renderer MUST NOT collapse the two into a boolean.
- **G8 invariant.** IEEE #5 + IEEE #6 are a paired mandate. An IEEE render emitting `level_of_involvement` without `affected_sections` (or vice versa) is non-conformant.
- **G9 invariant.** Image-rights regimes are anchor-specific. Renderer MUST NOT unify the field into a single boolean; per-anchor policy tables stay distinct.

### 4.4 Open implementation concerns (the #108 implementation issue MUST resolve these)

The following concerns were surfaced during this Decision Doc's codex review cascade (rounds 3–5) and represent **real contract gaps** the renderer implementation must close. They are listed here as concerns, **not pre-committed answers** — the implementation issue chooses the resolution mechanism within the §4.3 invariants. Stop-and-surface rationale: continuing to specify renderer input fields inside the Decision Doc produced cascading P2 findings with no convergence; the architecturally correct fix is to let the implementation issue own the input contract and review it against the anchor quotes directly.

1. **Track-selection lookup mechanism.** The PRISMA-trAIce track must dispatch on SLR lineage even when the directly-producing `origin_mode` is `full` (G2 invariant). Either: (a) the artifact registry adds a version-label-to-passport resolver so `upstream_dependencies` chain can be walked, OR (b) an explicit `slr_lineage=true|false` renderer input is set by the pipeline orchestrator, OR (c) a hybrid where the pipeline sets `slr_lineage` and cold-start uses an explicit `mode=` parameter. Implementation issue picks.
2. **Renderer input contract — tool identity.** PRISMA M2.a and v3.2 disclosure mode both require `tool_name` / `version` / `developer-or-provider` (verbatim "Specify the name, version number (if applicable), and developer/provider"). The renderer must collect these per AI tool used (in addition to whatever `tool_type` signal drives the G5 gate). Resolution: implementation issue specifies whether tool identity is auto-detected from session metadata (v3.2 already does this for Claude model versions per `disclosure_mode_protocol.md` Phase 4) or supplied explicitly per tool, and where the collection prompt lives.
3. **Renderer input contract — prompt scope.** PRISMA M6.a is verbatim "for each specific task". When the same tool is used across multiple SLR tasks (search / screening / data extraction / Risk of Bias / synthesis / drafting), per-task prompt records are required, not per-tool aggregation. Implementation issue specifies the (tool × task) record format and the per-tuple "not supplied" annotation granularity for missing tasks.
4. **Renderer input contract — IEEE section locator.** IEEE #6 is explicit-mandate on "specific sections of the article that use AI-generated content shall be identified". The renderer requires a per-category or per-tool section-locator input when `--policy-anchor=IEEE`. Implementation issue specifies the closed-enum vs free-form list shape and the missing-input failure surface (per G8 invariant: render is non-conformant when paired with `level_of_involvement` either direction).
5. **Renderer input contract — Nature image metadata.** Nature #16 default-deny + 3 carve-outs + labelling requires per-image metadata (which figure is AI-generated, which carve-out applies, what caption / label is rendered). The renderer cannot satisfy Nature mandate without this input. Implementation issue specifies the per-image record shape AND the labelling-instruction output channel (separate annotation block vs in-source manuscript modification — discovery doc §5.5 evidence bullet 2 already flagged this as a scope question for implementation).
6. **Renderer input contract — UNCERTAIN-state per-facet finalization rule.** §2.3 row 3 admits a partial mix (≥1 category USED with one or more UNCERTAIN still unresolved) into "full anchor-specific disclosure render", but the per-facet behaviour for those still-UNCERTAIN categories inside the render is the implementation issue's call. Acceptable rules: (a) prompt the user to resolve all UNCERTAIN categories before any render emits (effectively defers row 3 until clean), (b) emit USED categories at full strength + surface per-facet "not supplied" annotation for each still-UNCERTAIN category, (c) emit the whole disclosure with a "draft pending UNCERTAIN resolution" header until all UNCERTAIN resolve, or (d) some other rule that does not violate the G3/G10 invariant. **Forbidden** (Decision-Doc invariant — restating §2.3 row 3 constraint): rendering a still-UNCERTAIN category as though USED, in any of the four anchor outputs. The implementation tests must enforce both the chosen acceptable rule and the forbidden auto-promotion case.
7. **Renderer input contract — venue + anchor conflict resolution.** When the user passes both `--venue=<v>` and `--policy-anchor=<a>` and the two map to incompatible policies (e.g., `--venue=Nature` selects v3.2 Nature renderer with Methods placement; `--policy-anchor=IEEE` selects IEEE acknowledgments-only placement), the renderer must not silently pick one. Implementation issue picks: (a) reject conflicting selectors with an error, (b) require the venue to map consistently with the anchor or refuse, (c) some other deterministic resolution. Decision Doc requires only that silent precedence is forbidden.
8. **Three-state input completeness flag — full specification.** §2.3 table gives the high-level rule; the implementation issue specifies the field-level computation logic (which inputs count toward "category marked USED", how the v3.2 UNCERTAIN-confirmation prompt is invoked, how partial-state cases compose with §4.4 concern #6).
9. **Test set scope.** The renderer test suite must cover all 8 G-invariants in §4.3 plus all 10 prior concerns in §4.4 (concerns 1–8, 10, 11; this test-scope concern is the 9th and refers to itself rather than to a substantive contract gap). Per-concern: each acceptable implementation path needs a positive test demonstrating it works; each forbidden path — e.g., auto-promote UNCERTAIN, silent venue precedence — needs a negative test demonstrating it fails. Test set is sized to the implementation chosen in concerns 1–8 + 10 + 11; not pre-frozen here.

10. **`ai_used: true` substantive-content gate** (codex R11 P2, audit-trail-deferred). When a user supplies `ai_used: true` *without* completing the v3.2 Phase 2 categorization (cold-start manual invocation with the bare-flag input only, or `ai_used: true` paired with all categories still marked NOT USED), §3 G10 table row 4 would emit a "full anchor-specific disclosure render" but the renderer has no substantive content to render (no tool identity, no tasks, no sections). Implementation issue resolves this gap. Acceptable paths: (a) the renderer treats bare `ai_used: true` as a prompt-trigger that forces the v3.2 categorization flow before emitting any render, (b) the renderer requires `ai_used: true` to be paired with ≥1 category marked USED at row-4 evaluation time (effectively redefining row 4 to require category support, with bare `ai_used:true` falling through to row 7 cold-start), or (c) the renderer emits a "draft pending category confirmation" render that surfaces the disclosure scaffolding but flags every facet as "not supplied" until categories resolve. **Forbidden:** rendering a complete anchor disclosure with empty per-facet content when only `ai_used:true` is supplied. Decision Doc captures this as an open concern rather than picking a path because the choice interacts with §4.4 concerns #2 (tool identity collection path), #3 (prompt scope), #4 (IEEE locator shape), and #5 (Nature image metadata) — picking one here without aligning the others would re-trigger the same cascade pattern this Decision Doc just exited. See §5 closure notes for the audit-trail rationale.

11. **G1 invariant scope — data layer vs pipeline plumbing** (codex R11 P2, audit-trail-deferred). §4.3 G1 invariant reads "Renderer is the only new code path; data layer is untouched", but §4.4 concern #1's acceptable resolution paths (b) and (c) require **non-renderer code changes** outside the corpus entry schema: a pipeline orchestrator that sets `slr_lineage` (concern #1b) is not renderer code, and an artifact registry that adds a version-label-to-passport resolver (concern #1a) is not renderer code. The G1 invariant's "Renderer is the only new code path" is therefore over-broad as written. Implementation issue resolves this by narrowing the invariant: G1 forbids new fields *in the corpus entry data schema* (`literature_corpus_entry.schema.json`) at this issue; non-renderer code changes that are needed to satisfy §4.4 concern #1 (or any other lineage-plumbing path) are **permitted** as long as no entry-level disclosure field is added. The narrower G1 statement is the one frozen by the G1 Decision in §2.1 (which speaks of "no `ai_disclosure` field added"); the §4.3 invariant phrasing inherited a broader "renderer is the only path" claim from the R5 reframe that contradicts §4.4 concern #1 by accident. Implementation issue MUST treat the §2.1 G1 Decision (no schema field) as authoritative; the §4.3 invariant phrasing is to be corrected to "data layer is untouched; non-renderer code changes needed for §4.4 concerns are permitted" in a follow-up amendment to this Decision Doc.

Further concerns surfaced by the implementation review SHOULD extend this list. A follow-up Decision Doc amendment is required only if a new concern touches a §4.3 invariant.

---

## 5. Closure notes

This Decision Doc selects one direction from the four discovery outcomes (defer policy to renderer, with no entry-level `ai_disclosure` field added at this issue) and answers G1–G10 with §5 / §4 / §6 cites and named weaknesses per #108 Anti-goals. The chosen direction is **not** an unprincipled hybrid; each axis is decided on its own evidence. The composite shape that emerges (defer at C, two-track at B, soft+renderer-honest at D, multi-per-anchor at E) is a description of the result, not a pre-commitment.

The discovery doc's §6 open questions Q1–Q10 are answered here at the maintainer level. Per the framing note in #108 (single-maintainer repo, no community thread), the open-questions thread is replaced by this Decision Doc — Q1 maps to G1, Q2 to G2, Q3 to G5, Q4 to G3, Q5 to G6, Q6 (hybrid axis) is resolved by §2.1's multi-axis decision pattern, Q7 to G7, Q8 to G8, Q9 to G9, Q10 to G10.

**Decision acceptance — 11-round review trajectory + audit-trail-complete interpretation.** #108 acceptance criterion #4 originally read "codex gpt-5.5 xhigh review on the Decision Doc ≥ 2 rounds → 0 P1/P2 before implementation starts". This Decision Doc underwent 11 rounds of codex review (R1–R11) with the following P2 / P3 trajectory:

| Round | P2 | P3 | Nature of findings |
|---|---|---|---|
| R1 | 2 | 0 | Fact-check vs schema (`ai_disclosure` field, `origin_mode` name) |
| R2 | 3 | 0 | Internal consistency cascade (G3↔G10, SLR handoff, §4 stale refs) |
| R3 | 3 | 0 | Contract gap (lineage resolver, raw mode key, missing inputs) |
| R4 | 3 | 0 | Anchor-faithful gap (per-task prompts, IEEE locator, UNCERTAIN gating) |
| R5 | 4 | 0 | Renderer engineering (tool_name, UNCERTAIN partial, image metadata, venue/anchor conflict) |
| R6 | 3 | 1 | Reframe cascade cleanup (post-§4-reframe consistency) |
| R7 | 2 | 0 | PRISMA gate scope + UNCERTAIN whole-vs-facet |
| R8 | 2 | 0 | §4.3 invariants sync with §3 + §2.3 |
| R9 | 1 | 0 | §2.3 row split for mixed NOT-USED + UNCERTAIN |
| R10 | 1 | 1 | §2.3 totality (7-row partition with construction proof) + invariant ref |
| R11 | 2 | 1 | `ai_used:true` substantive-content gate; G1 invariant scope |

Findings did not reach 0 P2 in 11 rounds. The trajectory oscillates in the 1–3 P2 band after the R5 architectural reframe; the rebound to 2 P2 at R10 and R11 indicates that doc-level lexical patching of cross-referenced sections (§3 G-tables ↔ §4.3 invariants ↔ §4.4 concerns) is reaching a capacity limit in the current LLM/codex review setup — every fix at one section surfaces a stale reference or new conflict at another. The pattern matches the maintainer's documented rules for stopping whack-a-mole cycles (`feedback_lint_cap_rule_when_lexical_enumeration_loops` — 5+ rounds same lint family means change the cap rule, not the lexical patch; `feedback_llm_defect_class_problems_may_have_no_current_fix` — patch two rounds of structural contradiction then surface the architectural inflection rather than patching infinitely).

**Acceptance reinterpretation.** Per the maintainer's R11 inflection decision (recorded via AskUserQuestion R11 choice A): #108 criterion #4 is reinterpreted from "0 P2 after 2 rounds" to **"audit-trail complete; deep P2 contract gaps captured as §4.4 open concerns the implementation issue MUST resolve"**. The R11 two P2 findings are captured as §4.4 concerns #10 (`ai_used:true` substantive-content gate) and #11 (G1 invariant scope narrowing — data-layer vs pipeline-plumbing). The implementation issue's acceptance criteria inherit these concerns. The original 0-P2-after-2-rounds reading is preserved as the *initial* target; the reinterpreted version is the *audit-trail-honest* outcome of an 11-round review that surfaced real contract gaps no doc-level patching could close. ARS v3.7.3 spec converged at round 10 with 0 findings; this Decision Doc is closer to ARS v3.6.7 step 6 territory (18-round convergence per discovery doc §4 cross-anchor observation precedent) but the maintainer chose to ship at 11 rounds with documented concerns rather than push to 18+.

---

## 6. Related

- Discovery doc: `docs/design/2026-05-13-ai-disclosure-schema-discovery.md` (commit 299c4b6, PR #107)
- #106 (discovery issue, closed via #107)
- #108 (implementation issue, blocked-by this Decision Doc)
- v3.2 disclosure mode protocol: `academic-paper/references/disclosure_mode_protocol.md`
- v3.7.3 spec (locator infrastructure prior art): `docs/design/2026-05-12-ars-v3.7.3-claim-faithfulness-and-contaminated-source-spec.md`
- #102 (v3.7.4 triangulation) — orthogonal advisory pattern
- #103 (v3.8 L3 audit agent) — disclosure granularity may feed audit signal
- #105 (v3.7.3 migration tool) — orthogonal pattern reference (not invoked since G3 D3 needs no migration)
