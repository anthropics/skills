# AI Disclosure Schema — Discovery Document

**Status:** COMPLETE — all 6 phases shipped; PR #107 ready for merge (matrix 64/64 + design space 5 dimensions + 10 open questions + 4-anchor snapshot integrity verified)
**Date:** 2026-05-13
**Issue:** [#106](https://github.com/Imbad0202/academic-research-skills/issues/106)
**Author:** Cheng-I Wu
**Scope:** Discovery — NO schema commitment, NO implementation
**Discovery output is a PR adding this document; PR merge closes #106. Implementation issue (deferred) blocked-by #106.**

---

## 0. Phase tracking

This discovery is split into three execution phases. Each phase ships as a PR commit.

| Phase | Deliverable | Status |
|---|---|---|
| Phase 1 | Doc scaffold + 4 anchor snapshots locked (Wayback + SHA-256) + manifest | shipped (PR #107 c1) |
| Phase 2 | Fill cells for PRISMA-trAIce + ICMJE (32 of 64 cells) | shipped (PR #107 c2) |
| Phase 3a | Fill cells for Nature Portfolio (16 of remaining 32 cells; 48 of 64 total) | shipped (PR #107 c3) |
| Phase 3b.1 | Fill cells for IEEE (remaining 16 cells; 64 of 64 total) | shipped (PR #107 c4) |
| Phase 3b.2 | Deliverable 2 design space (5 dimensions A–E + trade-off matrix) | shipped (PR #107 c5) |
| Phase 3b.3 | Deliverable 3 open questions (6 baseline + 4 surfaced) | shipped (PR #107 c6) |

**Phase 1 explicitly does NOT fill any cells.** Cells carry `phase: 1-scaffold` placeholder until Phase 2/3. This is intentional — Phase 1 builds the provenance infrastructure so Phase 2/3 cell-filling can cite verbatim with byte-level integrity.

---

## 1. Background

ARS currently has a minimal `ai_disclosure` field (boolean / narrative). Three downstream pressures suggest this **may** need structural expansion:

1. **v3.7.x trust-chain infrastructure** (`docs/design/2026-05-12-ars-v3.7.3-claim-faithfulness-and-contaminated-source-spec.md`) records source provenance + citation anchors. Per-stage AI disclosure has been **hypothesized** as a complement on the production side, but should be tested rather than assumed.
2. **Zhao et al. arXiv:2605.07723 (2026-05)** corpus-scale evidence suggests AI-usage stage **may** correlate with hallucination risk profile. Disclosure granularity has analytical value worth investigating.
3. **External normative anchors** (PRISMA-trAIce / ICMJE / Nature / IEEE, plus expansion candidates) **may** require disclosure beyond ARS's current boolean/narrative form. The actual requirement-vs-recommendation strength varies and must be classified per-item, not aggregated.

**Honest about uncertainty:** discovery output may conclude that the right answer is to align ARS to a single anchor verbatim, construct a hybrid, defer policy mapping to a renderer layer, OR retain the current minimal `ai_disclosure` field. All four outcomes are valid discovery results.

A prior draft attempted to propose a concrete schema directly. Codex pre-open review flagged 5 P1 structural problems. These were symptoms of skipping discovery. This document is the discovery reset.

---

## 2. Scope

### 2.1 In scope

- Source-by-field disclosure matrix across a minimum required set of normative anchors with auditable provenance
- Design space documentation (enumeration of design choices, NOT a chosen solution)
- Open questions for community feedback

### 2.2 Out of scope (per #106)

- Schema file
- Renderer skill
- Migration tooling
- Lint
- Tests

These are reserved for the follow-up implementation issue, which is blocked-by this discovery's completion.

---

## 3. Provenance infrastructure (Phase 1)

All `explicit-mandate` / `explicit-recommend` / `conditional-mandate` cells filled in Phase 2/3 MUST cite a snapshot from this provenance bundle. Snapshot manifest is canonical; live URLs may drift after capture.

**Manifest:** `docs/design/snapshots/2026-05-13-ai-disclosure-discovery/manifest.yaml`

| Anchor | Wayback ID | Local SHA-256 (truncated) | Scope |
|---|---|---|---|
| PRISMA-trAIce | `20260513075443` | `f95fc59f…` | SLR-specific living guideline |
| ICMJE | `20260513075516` | `52f9e6bc…` | Medical journals, broad |
| Nature Portfolio | `20260513075542` | `cf691cba…` | Nature Portfolio (publisher-level guidance) |
| IEEE | `20260513075605` | `3ab8db50…` | IEEE author guidelines |

Verification protocol (per manifest): re-compute SHA-256 of local mirror before writing a mandate/recommend cell; mismatch → re-fetch from `wayback_url` + re-hash before continuing.

---

## 4. Deliverable 1: Source-by-field disclosure matrix

### 4.1 Classification scheme

Each cell carries:

| Field | Required? | Rule |
|---|---|---|
| `source_strength` | yes | `explicit-mandate` / `explicit-recommend` / `conditional-mandate` / `implicit` / `not-addressed` / `unknown` |
| `verbatim_quote` | yes for mandate/recommend/conditional cells | Paraphrase forbidden; ≤ 50 words verbatim from primary source |
| `inference_passage` | yes for `implicit` cells | The passage(s) used for inference, verbatim |
| `locator` | yes for mandate / recommend / conditional / implicit cells | Section / item / heading within source (e.g., "PRISMA-trAIce Table 1 M6.a"). `not-addressed` cells use `—` because the read scope is the entire source (per the `not-addressed` rule below); `unknown` cells use `—` because the source was not fully read. |
| `expected_value_type` | yes for mandate / recommend / conditional / implicit cells | boolean / structured / narrative. `not-addressed` / `unknown` cells use `—`. |
| `conditional_trigger` | required for `conditional-mandate` | Plain-text trigger description |
| `snapshot_ref` | required for mandate / recommend / conditional / implicit cells | `{anchor_slug}:wayback={wayback_id}`. `not-addressed` / `unknown` cells do not require snapshot_ref (the read-scope is the full snapshot, recorded once at the per-anchor matrix header). |

**`not-addressed` rule:** a cell may be `not-addressed` only when the matrix author has read the **entire** primary source AND can affirmatively state the field is absent. Cells where the source has not been fully read must be `unknown`.

**`unknown` ceiling:** matrix may close with up to **10 of 64** cells marked `unknown` (subjective ceiling, adjustable upward per #106 acceptance criteria if author finds source genuinely hard to fully read — document why).

### 4.2 Candidate disclosure fields (16-field core list)

These 16 fields anchor the 4×16 = 64-cell minimum matrix. Additional fields may be added during Phase 2/3 if material to ARS's design decision; subtractions require rationale.

1. **AI tool name**
2. **AI tool version**
3. **AI tool developer / manufacturer**
4. **Stage / phase of use**
5. **Specific task within stage**
6. **Affected manuscript sections / content locator**
7. **Date(s) of use**
8. **Prompts** (full text or summary, depending on source)
9. **Human oversight method** (reviewer count, qualifications)
10. **Human responsibility statement**
11. **Performance evaluation method**
12. **Performance evaluation results** (quantitative)
13. **Limitations / known failure modes**
14. **Disclosure location** (acknowledgments / Methods / cover letter)
15. **Copyediting exemption predicate**
16. **AI-generated image / figure / content rights**

### 4.3 Per-anchor matrix — PRISMA-trAIce

**Snapshot:** [`prisma-trAIce` @ wayback 20260513075443](https://web.archive.org/web/20260513075443/https://ai.jmir.org/2025/1/e80247/)
**Source-strength caveat:** PRISMA-trAIce is a **pre-Delphi proposal** (Holst et al. 2025, §Methods: *"this work is explicitly intended as a well-founded proposal that provides an immediate solution and can serve as the foundation for a subsequent, community-driven formal consensus process"*). It has not undergone formal consensus. **No item carries `explicit-mandate` strength** — the framework explicitly invites community refinement. Items within the framework use reporting-guideline directive verbs ("describe", "report", "include") classified here as `explicit-recommend` *within the proposed framework*. The framework itself is `conditional-mandate` on "AI tool used as methodological tool in an SLR" — outside that condition the framework does not apply. Cells below distinguish item-level recommend from framework-level conditional via the `conditional_trigger` column.

| # | Field | Source strength | Verbatim quote (or inference passage) | Locator | Value type | Conditional trigger |
|---|---|---|---|---|---|---|
| 1 | AI tool name | explicit-recommend | "For each AI tool or system used: a. Specify the name, version number (if applicable), and developer/provider." | Table 1, M2.a | narrative | AI tool used in SLR |
| 2 | AI tool version | explicit-recommend | "Specify the name, version number (if applicable), and developer/provider." | Table 1, M2.a | narrative | AI tool used in SLR; "if applicable" softens to recommend-when-versioned |
| 3 | AI tool developer / manufacturer | explicit-recommend | "Specify the name, version number (if applicable), and developer/provider." | Table 1, M2.a | narrative | AI tool used in SLR |
| 4 | Stage / phase of use | explicit-recommend | "For each AI tool, clearly describe: a. The specific SLR stage(s) where it was applied (e.g., search, screening, data extraction, Risk of Bias assessment, synthesis, drafting)." | Table 1, M3.a | structured (SLR stage enum) + narrative | AI tool used in SLR |
| 5 | Specific task within stage | explicit-recommend | "b. The precise task(s) the AI was intended to perform at each stage." | Table 1, M3.b | narrative | AI tool used in SLR |
| 6 | Affected manuscript sections / content locator | implicit | (inference passage) Items T1, A1, I1, R1, D1, D2 each prescribe a *manuscript section* for disclosure but the framework does not require an explicit per-task content-locator field. | Table 1 row headings (Title / Abstract / Introduction / Results / Discussion) | narrative | — |
| 7 | Date(s) of use | not-addressed | (Read entire checklist Table 1 + Methods §; no item requests date-of-use disclosure. Confirmed against M1–M10, R1–R2, D1–D2, T1, A1, I1.) | — | — | — |
| 8 | Prompts | explicit-recommend | "For each LLM/GenAI tool used, report: a. The full prompt(s) employed for each specific task. If prompts are extensive, provide a detailed description of their structure, key instructions, context provided..." | Table 1, M6.a | narrative (or repository link) | LLM/GenAI tool used (M6 header: "Prompt Engineering (if any)") |
| 9 | Human oversight method | explicit-recommend | "Describe the process of human interaction with and oversight of the AI tool(s) at each stage: a. How many reviewers interacted with/validated the AI outputs for each task? b. Did reviewers work independently when validating AI outputs? c. What were the qualifications or training of reviewers..." | Table 1, M8.a–g | narrative | AI tool used in SLR |
| 10 | Human responsibility statement | not-addressed | (Read entire Methods §; M8 covers oversight process but no item assigns explicit author-responsibility statement for AI output correctness. Distinct from ICMJE which mandates this separately.) | — | — | — |
| 11 | Performance evaluation method | explicit-recommend | "Describe methods used to evaluate the AI tool(s) performance for the specific tasks within the review (if applicable and feasible). This may include: a. The reference standard used for evaluation... b. The metrics used..." | Table 1, M9 | narrative | AI tool used in SLR; "if applicable and feasible" softens further |
| 12 | Performance evaluation results | explicit-recommend | "Report the results of any performance evaluations of the AI tool(s) for the specific tasks within the review (as described in P-trAIce M9). Include quantitative results (see M9) and measures of agreement between AI and human reviewers if assessed." | Table 1, R2 | structured (quantitative metrics) + narrative | M9 performance evaluation was conducted |
| 13 | Limitations / known failure modes | explicit-recommend | "Discuss any limitations encountered in using the AI tool(s) (eg, technical issues, biases identified, challenges in prompt engineering, unexpected outputs, limitations in AI performance for specific sub-tasks)." | Table 1, D1 | narrative | AI tool used in SLR |
| 14 | Disclosure location | implicit | (inference passage) Each Table 1 item is row-categorized by manuscript section (Title / Abstract / Introduction / Methods / Results / Discussion), implying section-of-record per item. No single "disclosure_location" field; location is structural property of the checklist itself. | Table 1 row groupings | structured (manuscript section enum) | — |
| 15 | Copyediting exemption predicate | not-addressed | (Read entire checklist; PRISMA-trAIce scope is "AI as methodological tool in an SLR"; copyediting exemption is not in scope — distinct concern handled by venue-level policies, not this framework.) | — | — | — |
| 16 | AI-generated image / figure / content rights | implicit | (inference passage) "Describe how data handled by AI tools (input, output, intermediate data) was managed and stored, and any measures taken to ensure data privacy, security, and compliance with copyright or terms of service, especially when using third-party cloud-based AI tools." M10 covers copyright/terms-of-service compliance for *data handled by AI tools* — touches AI-generated content rights indirectly without dedicated field. | Table 1, M10 | narrative | AI tool used in SLR |

**Snapshot ref:** all explicit-recommend / implicit cells above cite `prisma-trAIce:wayback=20260513075443` (`sha256: f95fc59f…`).
**Cell count:** 16 cells filled; source-strength distribution: 0 explicit-mandate / 10 explicit-recommend / 0 conditional-mandate / 3 implicit / 3 not-addressed / 0 unknown.

### 4.4 Per-anchor matrix — ICMJE

**Snapshot:** [`icmje` @ wayback 20260513075516](https://web.archive.org/web/20260513075516/https://www.icmje.org/recommendations/browse/artificial-intelligence/ai-use-by-authors.html)
**Source-strength caveat:** ICMJE Recommendations are **adopted** (not draft) and used by 1000+ journals as baseline. Strength language is consistent: "should require", "should describe", "must ensure", "is not acceptable". The page on AI Use by Authors (§V.A) is short — just two paragraphs — and is deliberately framework-level, not field-by-field. Many disclosure fields ARS tracks (tool version, prompts, performance metrics, date of use) are **not addressed** by ICMJE because ICMJE delegates section-level detail to individual journals. Where ICMJE uses "should require" addressed at *journals*, the effective strength to *authors* (post journal adoption) is `explicit-mandate`; where it addresses authors directly with "should describe" / "must ensure" / "is not acceptable", strength is recorded as written.

| # | Field | Source strength | Verbatim quote (or inference passage) | Locator | Value type | Conditional trigger |
|---|---|---|---|---|---|---|
| 1 | AI tool name | implicit | (inference passage) "the journal should require authors to disclose at submission whether they used AI-assisted technologies (such as LLMs, chatbots, or image creators)". Tool identity is implied by "such technology... how they used it" but no field-level requirement to name the specific tool. | §V.A, paragraph 1 | narrative | AI-assisted technology used |
| 2 | AI tool version | not-addressed | (Read entire §V.A; no mention of version-level granularity. ICMJE delegates this detail to individual journal instructions.) | — | — | — |
| 3 | AI tool developer / manufacturer | not-addressed | (Read entire §V.A; no mention of developer/manufacturer disclosure.) | — | — | — |
| 4 | Stage / phase of use | implicit | (inference passage) "Authors who use such technology should describe... how they used it". "How they used it" implies stage but no enumerated stage taxonomy. | §V.A, paragraph 1 | narrative | AI-assisted technology used |
| 5 | Specific task within stage | implicit | (inference passage — same source as #4) "how they used it" implies task-level description without explicit field. | §V.A, paragraph 1 | narrative | AI-assisted technology used |
| 6 | Affected manuscript sections / content locator | not-addressed | (Read entire §V.A; "the submitted work in the appropriate section if applicable" prescribes a disclosure section but not per-content-affected-location.) | — | — | — |
| 7 | Date(s) of use | not-addressed | (Read entire §V.A; no date-of-use disclosure required.) | — | — | — |
| 8 | Prompts | not-addressed | (Read entire §V.A; no prompt-disclosure requirement. ICMJE delegates this to journal-level policy.) | — | — | — |
| 9 | Human oversight method | explicit-recommend | "Authors should carefully review and edit the AI-generated content as the output can be incorrect, incomplete, or biased." | §V.A, paragraph 1 | narrative | AI-assisted technology used |
| 10 | Human responsibility statement | explicit-mandate | "Therefore, humans are responsible for any submitted material that included the use of AI-assisted technologies." | §V.A, paragraph 1 | narrative or boolean | AI-assisted technology used |
| 11 | Performance evaluation method | not-addressed | (Read entire §V.A; no performance-evaluation method disclosure required.) | — | — | — |
| 12 | Performance evaluation results | not-addressed | (Read entire §V.A; no performance-evaluation results disclosure required.) | — | — | — |
| 13 | Limitations / known failure modes | not-addressed | (Read entire §V.A; output limitations *mentioned* in oversight context — "output can be incorrect, incomplete, or biased" — but no requirement to disclose specific limitations encountered.) | — | — | — |
| 14 | Disclosure location | explicit-recommend | "Authors who use such technology should describe, in both the cover letter and the submitted work in the appropriate section if applicable, how they used it" | §V.A, paragraph 1 | structured (closed enum: cover-letter + manuscript-section) | AI-assisted technology used. Note: ICMJE's "should describe" reads as recommend at the language layer; adopting journals may upgrade to mandate via their own instructions. |
| 15 | Copyediting exemption predicate | not-addressed | (Read entire §V.A; no copyediting carve-out. ICMJE treats all AI-assisted technologies uniformly within §V.A — distinct from Nature §AI authorship which carves out "AI assisted copy editing" at no-disclosure strength, and from IEEE Paragraph 2 which carves out editing/grammar-enhancement at downgrade-to-recommend strength. Both Phase 3a/3b verifications confirmed the carve-out is anchor-specific.) | — | — | — |
| 16 | AI-generated image / figure / content rights | explicit-mandate | "Humans must ensure there is appropriate attribution of all quoted material, including full citations." + "Referencing AI-generated material as the primary source is not acceptable." | §V.A, paragraph 1 | narrative + negative-constraint flag | AI-assisted technology used (text or image). Both clauses are mandate strength ("must ensure" + "is not acceptable"). |

**Snapshot ref:** all explicit-mandate / explicit-recommend / implicit cells above cite `icmje:wayback=20260513075516` (`sha256: 52f9e6bc…`).
**Cell count:** 16 cells filled; source-strength distribution: 2 explicit-mandate / 2 explicit-recommend / 3 implicit / 9 not-addressed / 0 unknown.

**Cross-anchor observation:** ICMJE's distribution skews toward `not-addressed` (9/16) by design — it's deliberately framework-level, delegating field-level granularity to adopting journals. This contrasts with PRISMA-trAIce (9 explicit-recommend) which provides item-level granularity within its SLR-only scope. The two anchors are complementary, not competitive: ICMJE sets the *policy floor* (must disclose, must take responsibility); PRISMA-trAIce sets the *content ceiling* (these are the specific things to report when AI is used).

### 4.5 Per-anchor matrix — Nature Portfolio

**Snapshot:** [`nature` @ wayback 20260513075542](https://web.archive.org/web/20260513075542/https://www.nature.com/nature-portfolio/editorial-policies/ai)
**Source-strength caveat:** The Nature Portfolio AI editorial policy is **adopted** (not draft) and applies across all Nature Portfolio journals. The author-facing surface is structured as four short sections: AI authorship, Generative AI images, AI use by peer reviewers, Editorial use. ARS's matrix covers author-side obligations only (sections §AI authorship + §Generative AI images); peer-reviewer-side use and Springer Nature's own editorial use are out of scope per §2.2. Strength language is mixed: "do not currently satisfy our authorship criteria" + "unable to permit" + "must be labelled" carry mandate strength; "should be properly documented" + "should be disclosed" + "does not need to be declared" carry recommend strength. The policy is **framework-level for text** (Methods-section documentation is called for via should-language, with no field-level granularity — no version / no developer / no prompt / no performance metric requirement) and **prohibition-level for images** (generative AI images banned by default with three carve-outs; non-generative ML manipulations carry a recommend-strength caption-disclosure rule). Many text-side disclosure fields ARS tracks are therefore `not-addressed`; image-side rights field carries a hard `explicit-mandate` carrying a negative-constraint + labelling-mandate composite.

| # | Field | Source strength | Verbatim quote (or inference passage) | Locator | Value type | Conditional trigger |
|---|---|---|---|---|---|---|
| 1 | AI tool name | implicit | (inference passage) "Use of an LLM should be properly documented in the Methods section (and if a Methods section is not available, in a suitable alternative part) of the manuscript." Documentation requirement implies tool identity disclosure but no field-level name requirement. | §AI authorship | narrative | LLM used (non-copyediting) |
| 2 | AI tool version | not-addressed | (Read entire §AI authorship + §Generative AI images; no version-level granularity required. Nature delegates Methods-section detail to author and journal-level instructions.) | — | — | — |
| 3 | AI tool developer / manufacturer | not-addressed | (Read entire §AI authorship + §Generative AI images; no developer/manufacturer disclosure required.) | — | — | — |
| 4 | Stage / phase of use | implicit | (inference passage) "Use of an LLM should be properly documented in the Methods section". "Use" implies stage/task description in Methods but no explicit stage taxonomy. | §AI authorship | narrative | LLM used (non-copyediting) |
| 5 | Specific task within stage | implicit | (inference passage — same source as #4) "properly documented in the Methods section" implies task-level description without dedicated field. | §AI authorship | narrative | LLM used (non-copyediting) |
| 6 | Affected manuscript sections / content locator | implicit | (inference passage) "in the relevant caption upon submission" for non-generative ML image tools; for LLM text use, Methods-section documentation implies which sections used AI but no per-content-affected-location requirement. | §Generative AI images (caption rule); §AI authorship (Methods rule) | narrative | AI tool used |
| 7 | Date(s) of use | not-addressed | (Read entire §AI authorship + §Generative AI images; no date-of-use disclosure required.) | — | — | — |
| 8 | Prompts | not-addressed | (Read entire §AI authorship + §Generative AI images; no prompt disclosure required. Methods-section documentation requirement does not enumerate prompts as a required element.) | — | — | — |
| 9 | Human oversight method | explicit-mandate | "In all cases, there must be human accountability for the final version of the text and agreement from the authors that the edits reflect their original work." | §AI authorship | narrative | LLM / AI-tool used in manuscript text ("In all cases" generalizes the rule beyond the copyediting carve-out) |
| 10 | Human responsibility statement | explicit-mandate | "an attribution of authorship carries with it accountability for the work, which cannot be effectively applied to LLMs" + "there must be human accountability for the final version of the text" | §AI authorship | narrative or boolean | LLM used in manuscript |
| 11 | Performance evaluation method | not-addressed | (Read entire §AI authorship + §Generative AI images; no performance-evaluation method disclosure required.) | — | — | — |
| 12 | Performance evaluation results | not-addressed | (Read entire §AI authorship + §Generative AI images; no performance-evaluation results disclosure required.) | — | — | — |
| 13 | Limitations / known failure modes | not-addressed | (Read entire §AI authorship + §Generative AI images; §Generative AI images mentions general legal-copyright and research-integrity risks but does not require authors to disclose tool-specific limitations or failure modes. AI-tool limitations are characterized in §AI use by peer reviewers — out of scope for author-side matrix.) | — | — | — |
| 14 | Disclosure location | explicit-recommend | "Use of an LLM should be properly documented in the Methods section (and if a Methods section is not available, in a suitable alternative part) of the manuscript." + (for non-generative ML on images) "should be disclosed in the relevant caption upon submission" | §AI authorship + §Generative AI images | structured (closed enum: Methods + image-caption + suitable-alternative) | AI tool used; location varies by use type |
| 15 | Copyediting exemption predicate | explicit-recommend | (carve-out) "The use of an LLM (or other AI-tool) for "AI assisted copy editing" purposes does not need to be declared." (predicate, partial verbatim) "AI-assisted improvements to human-generated texts for readability and style... [but] do not include generative editorial work and autonomous content creation." | §AI authorship | structured (boolean carve-out + predicate definition) | AI use limited to copyediting-as-defined |
| 16 | AI-generated image / figure / content rights | explicit-mandate | "Springer Nature journals are unable to permit its use for publication." + "All exceptions must be labelled clearly as generated by AI within the image field." | §Generative AI images | structured (default-prohibit + 3-carve-out enum + labelling-required flag) | Generative AI image/video proposed for publication (default-deny); non-generative ML caption rule handled at #14 as recommend-strength |

**Snapshot ref:** all explicit-mandate / explicit-recommend / implicit cells above cite `nature:wayback=20260513075542` (`sha256: cf691cba…`).
**Cell count:** 16 cells filled; source-strength distribution: 3 explicit-mandate / 2 explicit-recommend / 0 conditional-mandate / 4 implicit / 7 not-addressed / 0 unknown.

**Cross-anchor observation:** Nature Portfolio's distribution skews to `not-addressed` (7/16) for the same structural reason as ICMJE — it is a framework-level policy that delegates field-level granularity to Methods-section author practice and journal instructions, not a reporting-guideline with item-level disclosure schema. Nature's distinctive contribution to the 4-anchor set is the **image-rights mandate package** (#16: default-deny + 3 carve-outs + labelling-required), which is more prescriptive than ICMJE's text-only attribution rule (ICMJE #16 forbids citing AI as primary source; Nature #16 forbids publishing the image at all unless a carve-out applies). The **copyediting exemption predicate (#15)** is the second distinctive contribution: Nature is the first anchor in the matrix to define an explicit carve-out boundary ("AI assisted copy editing" with prose definition) — PRISMA-trAIce and ICMJE both leave this `not-addressed`. Three-anchor hybrid emerging: ICMJE = policy floor (must disclose + must take responsibility), PRISMA-trAIce = SLR content ceiling (item-level granularity), Nature = section-of-record + carve-out shape (Methods location + copyediting predicate + image-rights regime).

### 4.6 Per-anchor matrix — IEEE

**Snapshot:** [`ieee` @ wayback 20260513075605](https://web.archive.org/web/20260513075605/https://open.ieee.org/author-guidelines-for-artificial-intelligence-ai-generated-text/)
**Source-strength caveat:** IEEE's guideline page (dated April 16, 2024) is **adopted** (not draft) and applies across IEEE publications. The snapshot HTML mirror is 212 KB, but the substantive policy text is **two short paragraphs** (~150 words combined; webinar reference and Author Center pointer carry no normative content, video content is out of scope as it is a separate medium without byte-stable transcript). The policy is therefore the **tersest of the four anchors**: it makes 3 stacked mandates within the opening paragraph (Claim A: disclosure-in-acknowledgments mandate carrying images/figures/code in scope; Claim B: tool-identity-mandate; Claim C: section-locator + level-of-use mandate), then 1 recommend (Claim D: copyediting carve-out with disclosure-still-recommended). Many fields ARS tracks are `not-addressed` because IEEE delegates field-level granularity to author practice within the acknowledgments section. Notable absences vs the other three anchors: **no explicit human-responsibility statement** (no ICMJE-style "humans are responsible" sentence), **no human-oversight requirement** (no Nature-style "human accountability for the final version"), and **no image-rights regime distinct from text** (images/figures/code fold into the same acknowledgments-disclosure mandate; Nature-style default-deny on generative images is absent). The disclosure-location mandate is **closed-enum tighter than Nature/ICMJE** (acknowledgments only; no Methods / no cover letter / no caption alternatives).

| # | Field | Source strength | Verbatim quote (or inference passage) | Locator | Value type | Conditional trigger |
|---|---|---|---|---|---|---|
| 1 | AI tool name | explicit-mandate | "The AI system used shall be identified" | Paragraph 1, sentence 2 | narrative | AI-generated content used in article |
| 2 | AI tool version | not-addressed | (Read entire policy page — 2 paragraphs of substantive content; no version-level granularity required. IEEE delegates Acknowledgments-section detail to author practice.) | — | — | — |
| 3 | AI tool developer / manufacturer | not-addressed | (Read entire policy page; no developer/manufacturer disclosure required.) | — | — | — |
| 4 | Stage / phase of use | implicit | (inference passage) "accompanied by a brief explanation regarding the level at which the AI system was used to generate the content". "Level at which the AI system was used" implies stage/extent description but no enumerated stage taxonomy; "level" reads as degree-of-involvement rather than SLR-style stage enum. | Paragraph 1, sentence 2 | narrative | AI-generated content used in article |
| 5 | Specific task within stage | explicit-mandate | "specific sections of the article that use AI-generated content shall be identified and accompanied by a brief explanation regarding the level at which the AI system was used to generate the content" | Paragraph 1, sentence 2 | narrative | AI-generated content used in article |
| 6 | Affected manuscript sections / content locator | explicit-mandate | "specific sections of the article that use AI-generated content shall be identified" | Paragraph 1, sentence 2 | structured (per-section locator) + narrative | AI-generated content used in article |
| 7 | Date(s) of use | not-addressed | (Read entire policy page; no date-of-use disclosure required.) | — | — | — |
| 8 | Prompts | not-addressed | (Read entire policy page; no prompt disclosure required. "Brief explanation" of usage level does not enumerate prompts as a required element.) | — | — | — |
| 9 | Human oversight method | not-addressed | (Read entire policy page; no human-oversight method requirement. IEEE is silent on reviewer count, qualifications, or validation workflow — contrasts with Nature §AI authorship "In all cases, there must be human accountability" and PRISMA-trAIce M8 a–g.) | — | — | — |
| 10 | Human responsibility statement | not-addressed | (Read entire policy page; no explicit author-responsibility statement for AI output correctness. Contrasts with ICMJE "humans are responsible for any submitted material that included the use of AI-assisted technologies" and Nature "there must be human accountability for the final version of the text".) | — | — | — |
| 11 | Performance evaluation method | not-addressed | (Read entire policy page; no performance-evaluation method disclosure required.) | — | — | — |
| 12 | Performance evaluation results | not-addressed | (Read entire policy page; no performance-evaluation results disclosure required.) | — | — | — |
| 13 | Limitations / known failure modes | not-addressed | (Read entire policy page; no limitations / failure-modes disclosure required. IEEE makes no general statement about AI output reliability — contrasts with ICMJE "output can be incorrect, incomplete, or biased".) | — | — | — |
| 14 | Disclosure location | explicit-mandate | "shall be disclosed in the acknowledgments section of any article submitted to an IEEE publication" | Paragraph 1, sentence 1 | structured (closed enum: acknowledgments-section only) | AI-generated content used in article. Note: IEEE's enum is tighter than Nature (Methods or alternative) and tighter than ICMJE (cover letter + manuscript section). |
| 15 | Copyediting exemption predicate | explicit-recommend | "The use of AI systems for editing and grammar enhancement is common practice and, as such, is generally outside the intent of the above policy. In this case, disclosure as noted above is recommended." | Paragraph 2 | structured (boolean carve-out + predicate definition) + downgrade-strength flag | AI use limited to editing-and-grammar-enhancement-as-defined. Note: the carve-out **does not eliminate** disclosure — it downgrades strength from mandate to recommend while keeping location/content rules intact. |
| 16 | AI-generated image / figure / content rights | implicit | (inference passage) "The use of content generated by artificial intelligence (AI) in an article (including but not limited to text, figures, images, and code) shall be disclosed in the acknowledgments section" — images/figures/code fold into the same acknowledgments-disclosure mandate as text; no separate image-rights regime, no default-prohibition (contrasts with Nature §Generative AI images "unable to permit its use for publication"), no labelling-required flag distinct from the general acknowledgments rule. | Paragraph 1, sentence 1 | narrative (within general acknowledgments disclosure) | AI-generated content (text/figures/images/code) used in article |

**Snapshot ref:** all explicit-mandate / explicit-recommend / implicit cells above cite `ieee:wayback=20260513075605` (`sha256: 3ab8db50…`).
**Cell count:** 16 cells filled; source-strength distribution: 4 explicit-mandate / 1 explicit-recommend / 0 conditional-mandate / 2 implicit / 9 not-addressed / 0 unknown.

**Cross-anchor observation:** IEEE's distribution skews to `not-addressed` (9/16) on a different basis from ICMJE — ICMJE is framework-level *delegating to adopting journals*; IEEE is framework-level *delegating to author practice within the acknowledgments section*. The two converge on the same `not-addressed` count by very different routes, which is itself a discovery signal: framework-level brevity reaches the same `not-addressed` floor regardless of delegation target. IEEE's distinctive contribution to the 4-anchor set is **disclosure-location closed enum** (#14: acknowledgments-only — the tightest enum across all four anchors; PRISMA-trAIce uses 6-section row enum across the checklist, ICMJE uses cover-letter + appropriate-section, Nature uses Methods + image-caption + suitable-alternative). The **copyediting carve-out (#15)** is also distinctive in its downgrade-not-eliminate construction: IEEE explicitly says disclosure is **still recommended** under the carve-out, whereas Nature says the carve-out use "does not need to be declared". This is the cleanest split in the 4-anchor set on whether copyediting carve-out means *no disclosure* (Nature) or *softer-strength disclosure at the same location* (IEEE). The **absence** of human-oversight (#9), human-responsibility (#10), and image-rights-regime (#16) means a schema chasing IEEE-only alignment would omit three fields that at least one of ICMJE / Nature treats at mandate strength: #9 is mandate only in Nature (ICMJE #9 is recommend, PRISMA-trAIce #9 is recommend); #10 is mandate in both ICMJE and Nature (PRISMA-trAIce leaves it `not-addressed`); #16 is mandate in both ICMJE (text-attribution clause) and Nature (default-deny + labelling). IEEE-only alignment loses all three at mandate strength. 4-anchor hybrid emerging: ICMJE = policy floor (must-disclose + must-take-responsibility) / PRISMA-trAIce = SLR content ceiling (item-level granularity) / Nature = section-of-record + carve-out shape (Methods location + copyediting predicate + image-rights regime) / IEEE = location closed-enum tightener + carve-out downgrade-not-eliminate construction.

### 4.7 Expansion anchors (Phase 3, optional)

COPE / CSE / WAME / JAMA / PLOS — partial expansion allowed; each cell column added must follow the same provenance rules. Snapshot capture deferred until Phase 3 author elects to include.

---

## 5. Deliverable 2: Design space document

Enumeration of design choices across 5 dimensions (A–E), with trade-off matrix per option across at least 4 axes (alignment depth / schema simplicity / backward-compat burden / integration cost). Per #106, **options are credible alternatives — not a quota — and choosing among them is OUT of scope for this discovery.**

Each dimension below presents the §4-matrix evidence that bears on the option set (advisory, not prescriptive), then enumerates options, then offers a trade-off table. Where the matrix gives an asymmetric signal across the four anchors, the asymmetry is noted but not resolved.

**Trade-off rubric (consistent across all 5 dimensions):**

- **Alignment depth**: how many of the 4 anchors does the option satisfy at mandate strength? `H` (3–4) / `M` (2) / `L` (0–1).
- **Schema simplicity**: complexity at the JSON/YAML schema level. `H` simple (single field / closed enum), `M` moderate (structured object), `L` complex (event log / multi-field separation).
- **Backward-compat burden**: cost to existing ARS users whose data is boolean/narrative legacy. `H` low burden (legacy stays valid), `M` moderate (migration tool with auto-mapping), `L` high (mass-edit required).
- **Integration cost**: cost to ARS internal infrastructure (literature_corpus_entry schema, citation emission, validators, downstream agents). `H` low cost (fits existing schemas), `M` moderate (one schema/agent touched), `L` high (multi-component change).

Higher letter = better trade-off on that axis. No option is universally `H/H/H/H` — that is the discovery point. The dimensions are largely orthogonal but some option pairs interact (noted under each table).

### 5.1 Dimension A: Value-type / event model

**Matrix evidence:**

- Nature #9 and #10 cite the same source sentence at different facets — a single disclosure clause may map to multiple structured fields (one-to-many at the value level).
- ICMJE #16 = text-attribution clause; Nature #16 = default-prohibit + 3 carve-outs + labelling-required; IEEE #16 = fold into general acknowledgments rule. The "AI-generated image rights" field is **anchor-specific enum-of-policies, not a flat boolean**. A schema flat enough to be a boolean would lose all three anchor-specific policy shapes; a schema rich enough to carry the Nature regime alone would be over-engineered for IEEE.
- PRISMA-trAIce M9 (`if applicable and feasible`) and M6 (`if any`) attach **conditional applicability** to a recommend-strength field. Conditional structure exists in the matrix even before mandate strength.
- IEEE #15 carve-out is **downgrade-not-eliminate** (recommend stays at the same location); Nature #15 carve-out is **eliminate** ("does not need to be declared"). Carve-outs carry **strength semantics**, not just boolean exemption.

**Options:**

- **A1: Pure boolean per stage** — `ai_used: true | false` for each stage. Tool name / version / prompt / etc. are not modeled.
- **A2: Structured object per stage** — `{ ai_used: bool, tool_name: str, version: str?, prompts: [str]?, oversight_method: str?, … }` with required sub-fields gated by `ai_used: true`.
- **A3: Hybrid — boolean required, narrative description optional** — `{ ai_used: bool, narrative: str? }`. ARS's current shape extended with structured boolean.
- **A4: Per-stage tier** — `disclosure_tier: none | minimal | extensive` with tier→fields mapping defined externally.
- **A5: Event-log model** — `disclosure_events: [{ stage_id, tool_id, task, timestamp, claim_anchor_id?, performance_metric_ref?, … }]` linked to v3.7.x trust-chain anchors.

**Trade-off table:**

| Option | Alignment depth | Schema simplicity | Backward-compat burden | Integration cost | Notes |
|---|:---:|:---:|:---:|:---:|---|
| A1 Boolean per stage | L | H | H | H | Satisfies no mandate beyond "ai used yes/no"; cannot carry IEEE #5/#6 task+section locator, ICMJE #10 responsibility statement, Nature #16 image rights. Renderer would have to invent fields. |
| A2 Structured object | M | M | L | M | Carries ICMJE/IEEE/Nature text-side mandates. Cannot carry one-sentence-→-many-facets pattern without redundancy (Nature #9 = #10). Required sub-fields gated by ai_used create flat schema with 8–12 optional fields. |
| A3 Hybrid bool+narrative | L | H | H | H | Today's ARS shape. Auditability low — narrative is free text. Satisfies no anchor at mandate strength beyond #14 location (only if narrative happens to include location). |
| A4 Per-stage tier | L–M | M | M | M | Tier mapping captures Nature `not-addressed`-heavy vs PRISMA-trAIce field-rich asymmetry, but the tier→fields rule lives outside the data — auditability depends on the external rule being versioned. Tier semantics drift if not pinned. |
| A5 Event-log | H | L | L | L | Carries v3.7.x trust-chain alignment, one-sentence-→-many-facets pattern natural (one event, multiple `facet_ids`), conditional applicability via `applies_when` predicate, IEEE #6 section locator native (event linked to claim anchor). High cost everywhere: schema is the most complex, migration from legacy boolean is mass-edit. |

**Interaction notes:** A1↔C1 (Boolean per stage + single policy field) collapses 4-anchor matrix to a single bit + a single string. A5↔E1 (Event-log + single ARS render) creates a renderer whose output may exceed what venue policy requires; an A5↔E4 (Event-log + schema-only) combination keeps the audit trail rich and lets the user format for venue manually — at the cost of no native render.

**Matrix asymmetry not resolved by this dimension:** the 4 anchors disagree at the field level about which structured sub-fields belong in the schema (PRISMA-trAIce demands version + developer + prompts + performance evaluation; ICMJE/Nature/IEEE all leave version + developer `not-addressed`). A1 underfits, A2/A5 risk overfit to PRISMA-trAIce-shaped data, A4 only works if `tier` is pinned to a specific anchor.

### 5.2 Dimension B: Stage taxonomy

**Matrix evidence:**

- PRISMA-trAIce explicitly enumerates SLR-specific stages (M3.a: search, screening, data extraction, Risk of Bias assessment, synthesis, drafting). Closed enum. Domain-specific.
- ICMJE / Nature / IEEE all use "stage" implicitly via "how they used it" / "level at which" / "Methods" language — no enumerated taxonomy.
- IEEE #4 "level at which the AI system was used" reads as **degree-of-involvement** not stage. A stage taxonomy that conflates degree-of-involvement with workflow-stage will misalign with IEEE at the semantic level.
- PRISMA-trAIce M6 prompt rule applies "if LLM/GenAI" — tool-type-conditioned, independent of stage.

**Options:**

- **B1: Closed enum (canonical stage_id)** — one fixed list (e.g., PRISMA-trAIce 6 stages + a "drafting" alias) applied universally.
- **B2: Open enum (any string, recommended values per ARS mode)** — user supplies stage label freely; ARS validates against recommended-list per mode (deep-research / academic-paper / etc.) but does not reject novel values.
- **B3: Closed enum + `other_label` escape hatch** — fixed list with a single fallback bucket carrying user-provided free text.
- **B4: Two-track schema (PRISMA-trAIce SLR stages vs general writing stages, by mode)** — `systematic-review` mode uses PRISMA-trAIce 6-stage enum; other modes use a 4-stage writing enum (research / drafting / revision / copyediting).
- **B5: Hierarchical taxonomy (controlled top-level + mode-specific substage aliases)** — top-level (research / production / review) with mode-specific aliases (`research → search → screening` for SLR; `production → outlining → drafting` for academic-paper).

**Trade-off table:**

| Option | Alignment depth | Schema simplicity | Backward-compat burden | Integration cost | Notes |
|---|:---:|:---:|:---:|:---:|---|
| B1 Closed enum | M | H | L | M | Aligns with PRISMA-trAIce only; ICMJE/Nature/IEEE are agnostic so any closed enum is compatible at the policy layer, but a PRISMA-shaped enum may surprise non-SLR authors. Migration from legacy free-text narrative requires mass-classification. |
| B2 Open enum | L–M | H | H | H | Maximally compatible — every anchor is agnostic, every legacy entry survives. Auditability low — same stage may appear under 5 different labels across the corpus. |
| B3 Enum + escape hatch | M | M | M | M | Captures PRISMA-trAIce 6-stage alignment for SLR mode while letting other modes use `other_label`. Audit still soft because escape hatch encourages unsystematic use. |
| B4 Two-track by mode | H | L | M | M | Highest alignment depth: SLR mode satisfies PRISMA-trAIce field-by-field; other modes satisfy ICMJE/Nature/IEEE's stage-agnostic policy. Schema is most complex — two enums in one schema gated by mode. Mode-detection logic must be reliable. |
| B5 Hierarchical | M–H | L | L | L | Top-level satisfies ICMJE/Nature/IEEE; substage satisfies PRISMA-trAIce. Schema complexity is highest of the five options. Future expansion (COPE / WAME / JAMA) plugs in as new substage groups. |

**Interaction notes:** B1↔A2 (PRISMA-shaped closed enum + Structured object) keeps both dimensions at their simplest, and aligns well *inside* SLR mode; outside SLR the alignment comes from A2's anchor-mandate coverage, not from B1 (B1's stage labels do not match ICMJE/Nature/IEEE language). B4↔C5 (Two-track + Versioned policy profile) is the highest alignment depth combination — but introduces two cross-cutting axes (mode + policy profile) that must compose without conflict.

**Matrix asymmetry not resolved by this dimension:** the IEEE "level" semantics (degree-of-involvement, not stage) is not addressed by any of the 5 stage-taxonomy options. A schema that needs to satisfy IEEE #4/#5 at mandate strength must add a separate `level_of_involvement` field independent of stage taxonomy. This may belong in Dimension A (value model) rather than B.

### 5.3 Dimension C: Disclosure policy expression

**Matrix evidence:**

- 4-anchor disclosure-location enum has no intersection: PRISMA-trAIce (6 manuscript sections) ∩ ICMJE (cover-letter + appropriate-section) ∩ Nature (Methods + image-caption + suitable-alternative) ∩ IEEE (acknowledgments-only) = ∅.
- Copyediting carve-out splits 2-2: Nature/IEEE define it (eliminate vs downgrade); PRISMA-trAIce/ICMJE leave `not-addressed`. A schema that supports the carve-out without specifying which anchor variant is in force is ambiguous; a schema that hardcodes one variant under-aligns with the other.
- Nature #16 image-rights regime (default-prohibit + 3 carve-outs + labelling) is structurally different from ICMJE #16 (text-attribution clause). The two cannot be merged into a single boolean without information loss.
- ICMJE's "should require" language is **policy-routed** — addressed at journals, who upgrade to mandate via their own instructions. The same source text can have different effective strength depending on which adopting journal applies it.

**Options:**

- **C1: Single field `declaration_mode: strict | lenient | none`** — schema records the policy stance, not field-level structure.
- **C2: Pure carve-out list `exempted_uses: ["copyediting", …]`** — schema records what is exempted, not what is required.
- **C3: Multi-field separation** — `{ ai_used_any: bool, disclosure_required: bool, exempted_uses: [], policy_aligned_with: anchor_id }`. Each axis a separate field.
- **C4: Defer policy semantics entirely to renderer** — schema records facts (tool name, stage, task, prompts, locator); a renderer layer applies anchor-specific policy to decide what to surface.
- **C5: Versioned policy-profile / ruleset mapping** — `{ policy_profile: anchor_slug, profile_version: date, profile_source: locator_url }`. Policy is named, versioned, and source-anchored.

**Trade-off table:**

| Option | Alignment depth | Schema simplicity | Backward-compat burden | Integration cost | Notes |
|---|:---:|:---:|:---:|:---:|---|
| C1 Single declaration_mode | L | H | H | H | "strict / lenient" hides which anchor's strictness; ambiguous at audit time. Copyediting carve-out is one bit, losing eliminate-vs-downgrade distinction. |
| C2 Carve-out list | M | H | H | M | Captures Nature/IEEE #15 carve-out shape natively. Cannot express Nature #16 default-deny regime — that is a mandate, not a carve-out. |
| C3 Multi-field separation | M | L | M | L | Each axis explicit; carve-outs + alignment anchor + strictness composable. Schema has 4+ correlated fields that may drift (`exempted_uses` set without `disclosure_required: false` is inconsistent). Validator burden is high. |
| C4 Defer to renderer | H | H | H | M | Schema stays minimal; policy mapping lives in renderer skill. Aligns with all 4 anchors simultaneously because schema does not commit to one. **Audit-quality depends on renderer correctness, not data correctness** — bug in renderer breaks all venue alignments at once. |
| C5 Versioned policy-profile | H | M | M | L | Each entry pins to a named profile (`icmje-v2024` / `nature-2025-01` / `ieee-2024-04` / `prisma-traice-pre-delphi`); changes traceable. New profiles plug in. Profile registry is a separate artifact to maintain. |

**Interaction notes:** C4↔E2 (Defer + multiple per-policy renders) is the most policy-faithful combination — facts in data, policy in renderer, one renderer per anchor. C4↔E1 (single render) hides the policy choice behind a single rendered output. C5↔A5 (Versioned profile + Event log) gives temporal + policy provenance simultaneously; cost is the most complex schema in the design space.

**Matrix asymmetry not resolved by this dimension:** ICMJE's policy-routed strength (adopting journals upgrade) is not addressable by C1–C5 alone. A schema may need an `effective_strength_via` field separate from the `policy_aligned_with` field to distinguish ICMJE's source-level recommend from a specific journal's mandate uptake. Whether this matters for ARS depends on whether ARS authors target named journals (which would override anchor defaults).

### 5.4 Dimension D: Legacy disclosure handling

**Matrix evidence:**

- ARS's current `ai_disclosure` field is boolean/narrative. Existing literature_corpus entries and bibliography entries may carry no AI disclosure at all.
- The 4 anchors all describe **forward-looking** policy: none of them obligate retrospective disclosure of past AI use. A migration tool that requires backfill would over-reach beyond anchor scope.
- Matrix #14 (disclosure location) has 4 distinct enums none of which is "no disclosure". A legacy entry with empty narrative satisfies no anchor.
- Phase 2 observation #4: PRISMA-trAIce has zero mandate strength because it is pre-Delphi. A schema that **rejects** entries lacking PRISMA-shaped fields would treat a not-yet-formal-consensus framework as binding. Over-strict.

**Options:**

- **D1: Strict (reject legacy entries)** — pipeline refuses to process entries without the new disclosure structure.
- **D2: Hybrid (accept for storage, exclude from renderer output)** — legacy entries stored as-is, but renderer skips them (no disclosure surfaced).
- **D3: Soft (accept everywhere, `legacy: true` marker, renderers degrade gracefully)** — legacy entries flagged, renderer emits a "legacy disclosure" note.
- **D4: Forced backfill (pipeline refuses to run on legacy entries)** — pipeline halts; user must edit existing data before continuing.

**Trade-off table:**

| Option | Alignment depth | Schema simplicity | Backward-compat burden | Integration cost | Notes |
|---|:---:|:---:|:---:|:---:|---|
| D1 Strict reject | M | H | L | M | Forces clean data from day-1. Breaks existing pipelines until users migrate every entry. Over-strict relative to anchor scope (no anchor requires retrospective disclosure). |
| D2 Hybrid (storage-yes / render-no) | L | M | M | M | Data survives; render hides legacy. Renderer output may be misleading — looks like no AI use when in fact disclosure status is unknown. |
| D3 Soft + legacy marker | M | M | H | H | All entries survive, renderer surfaces "legacy disclosure unavailable" honestly. Schema adds 1 boolean + acknowledgment text. **Closest to anchor scope** — forward-looking policy with explicit unknown surfacing. |
| D4 Forced backfill | L | H | L | L | Even more disruptive than D1; backfilling AI use that happened months ago may not be reliably recoverable. Most likely to produce **fabricated** retrospective disclosures, which violates ICMJE #10 (human-responsibility) in spirit. |

**Interaction notes:** D3↔A1/A3 (Soft + Boolean or Hybrid bool-narrative) lets ARS keep current shape and add the legacy marker as a single new field. D1/D4↔A2/A5 (Strict or Forced + Structured / Event-log) creates the harshest migration — schema change + retroactive data fill.

**Matrix asymmetry not resolved by this dimension:** the matrix is silent on whether *no AI use* is itself a disclosable statement. PRISMA-trAIce M1 implies "if AI tool used"; ICMJE/Nature/IEEE all condition on AI use. A schema that defaults to `ai_used: false` for legacy entries may be assigning a positive fact (no AI used) that was never recorded by the original author. Dimension D options interact with this concern: D3's `legacy: true` marker partially addresses it; D1/D4 do not; D2 hides the ambiguity.

### 5.5 Dimension E: Renderer target

**Matrix evidence:**

- 4-anchor #14 enums do not intersect — a single ARS-native render format cannot satisfy all four anchors at the location level. The four enums are: PRISMA-trAIce (6 manuscript-section row labels across Table 1) / ICMJE (cover letter + appropriate manuscript section) / Nature (Methods + image-caption + suitable-alternative) / IEEE (acknowledgments-only).
- Nature #16 image-rights regime requires labelling text "generated by AI" at the location "within the image field" (verbatim, §4.5 #16). Distinct from Nature #14's caption-disclosure rule for non-generative ML tools. A pure JSON/YAML output cannot satisfy either Nature image-side rule — the schema must produce per-image annotation that integrates with the figure metadata.
- The four anchors call for different surface placements (cover letter, Methods, Acknowledgments, caption, image-field metadata). The same data renders correctly across all of them only if the renderer knows the venue.
- Authors submit to venues with venue-specific templates. If ARS renderer output does not match venue template, the author edits it manually anyway.

**Options:**

- **E1: Single ARS-native render format** — one canonical rendered output, applied to all venues.
- **E2: Multiple per-policy renders (one per anchor)** — ARS provides 4 distinct rendered outputs (one each for PRISMA-trAIce / ICMJE / Nature / IEEE); user picks venue.
- **E3: ARS render + user-supplied template format** — ARS provides one canonical render, plus a template-substitution mode where the user supplies a venue-specific format string.
- **E4: No renderer (schema only, user manually formats for target venue)** — ARS outputs structured data, user is responsible for venue rendering.

**Trade-off table:**

| Option | Alignment depth | Schema simplicity | Backward-compat burden | Integration cost | Notes |
|---|:---:|:---:|:---:|:---:|---|
| E1 Single ARS-native | L | H | H | M | Aligns with at most one anchor — others see render that mismatches their location/format requirements. Lowest user friction once user accepts ARS format. |
| E2 Multiple per-anchor | H | M | H | L | Each anchor's renderer is correct. Maintenance burden grows with anchor set (4 today; if expansion adds 5 candidates from §4.7, that's 9 renderers). Each renderer is a separate code path that can drift from anchor policy updates. |
| E3 ARS render + user template | M | M | H | M | Default render satisfies one anchor; advanced users override per-venue. Two-track UX may confuse users into thinking default render is universally venue-safe (it isn't). |
| E4 No renderer (schema only) | M | H | H | H | Schema-only output can in principle support any anchor (since user does mapping), but in practice depends entirely on author labour — alignment-depth in delivered manuscripts is unverifiable at the ARS layer. Honest about the fact that no single render fits all venues. **Lowest cost** to ARS infrastructure, but every user reimplements rendering per venue. |

**Interaction notes:** E4↔C4 (No renderer + Defer policy) is the **most discovery-honest** combination: schema records facts, user maps facts to venue. E2↔C5 (Multiple renders + Versioned policy profile) gives the **most venue-correct** combination but at the highest maintenance cost. E1↔A1 (Single render + Boolean per stage) is the **lowest-cost** combination but aligns with no anchor at mandate strength beyond bare disclosure presence.

**Matrix asymmetry not resolved by this dimension:** Nature #16's in-image-field labelling and #14's caption-disclosure cannot be produced by a schema-only output without a renderer — yet a renderer that touches image-field metadata or captions has to integrate with the manuscript-production pipeline (LaTeX / Word / Markdown source), not just emit a separate rendered text block. This is a **scope question** for the implementation issue (deferred): does ARS render into the manuscript source or produce a separate disclosure artifact?

### 5.6 Dimension-pair interactions (advisory)

The 5 dimensions are largely orthogonal, but the per-dimension Interaction notes (§5.1–§5.5) surfaced **13 distinct option-pairs** with load-bearing properties. They are consolidated here for easy reference, in the order they first appeared. Pairs labelled X↔Y and Y↔X are treated as the same pair (e.g. C5↔A5 in §5.3 is the same pair regardless of which dimension surfaces it).

| Pair | Source § | Interaction |
|---|---|---|
| A1↔C1 | §5.1 | Boolean per stage + single policy field = collapses 4-anchor matrix to a single bit + a single string; lowest-information combination in the space. |
| A5↔E1 | §5.1 | Event-log + Single ARS render = renderer may emit more disclosure than the venue requires; under-aligns by overshooting. |
| A5↔E4 | §5.1 | Event-log + No renderer = keeps audit trail rich but pushes all rendering to user. |
| B1↔A2 | §5.2 | Closed enum + Structured object = simplest combined schema; alignment outside SLR comes from A2's anchor-mandate coverage, not from B1. |
| B4↔C5 | §5.2 | Two-track + Versioned profile = highest alignment-depth pairing; introduces two cross-cutting axes (mode + policy profile) that must compose without conflict. |
| C4↔E2 | §5.3 | Defer policy + Multiple per-anchor renders = most policy-faithful pairing (facts in data, policy in renderer, one renderer per anchor). |
| C4↔E1 | §5.3 | Defer policy + Single ARS render = hides the policy choice inside a single rendered output; auditability degraded. |
| C5↔A5 | §5.3 | Versioned profile + Event-log = temporal + policy provenance simultaneously; highest schema complexity in the space. |
| D3↔A1/A3 | §5.4 | Soft legacy + Boolean / Hybrid = lowest-friction migration path that preserves current ARS shape; adds the `legacy: true` marker as a single new field. |
| D1/D4↔A2/A5 | §5.4 | Strict / Forced legacy + Structured / Event-log = harshest migration; schema change combined with retroactive data fill. |
| E4↔C4 | §5.5 | No renderer + Defer policy = most discovery-honest combination; schema records facts, user maps facts to venue. |
| E2↔C5 | §5.5 | Multiple renders + Versioned policy profile = highest venue-correctness; highest maintenance cost (one renderer per profile per anchor). |
| E1↔A1 | §5.5 | Single render + Boolean per stage = lowest-cost combination but aligns with no anchor at mandate strength beyond bare disclosure presence. |

The 13 pairs are not exhaustive — the implementation issue (deferred) would need to enumerate the full Cartesian space (5×5×5×4×4 = 2,000 option combinations) only if a non-orthogonal interaction surfaces during selection.

---

## 6. Deliverable 3: Open questions for community feedback

These questions are open by design — Deliverable 2 enumerated credible options without choosing among them; Deliverable 3 names the questions whose answers should drive that choice. The 6 baseline questions from #106 are kept verbatim and given matrix-derived framing context. Phase 2/3 cell-filling surfaced 4 additional questions that were not in the baseline set and are added below. **No question here is rhetorical.** Each one is a genuine open issue where the matrix evidence supports more than one defensible answer.

A GitHub Discussions thread will be linked from #106 when this PR merges. Discovery closure requires the thread to be **linked and open**, not "answered" or "consensus reached" (per #106 acceptance criteria).

### 6.1 Baseline questions from #106 (with matrix context)

**Q1 — Should ARS schema force a single declaration policy, or be policy-agnostic?**

The 4-anchor matrix gives no clear answer. The four anchors' disclosure-location enums do not intersect (PRISMA-trAIce 6-section / ICMJE cover-letter+section / Nature Methods+caption+alt / IEEE acknowledgments-only). Forcing a single policy means picking one anchor and losing the others; staying policy-agnostic means deferring policy semantics to a renderer layer (Dimension C option C4) and trusting downstream correctness. The matrix is silent on whether ARS authors target named journals — if they do, ICMJE's policy-routed strength (adopting journals upgrade) would make a journal-aware schema preferable to either pure single-policy or pure policy-agnostic.

**Q2 — Should stage taxonomy be SLR-centric, general, or hierarchical?**

PRISMA-trAIce specifies a 6-stage SLR taxonomy (M3.a); ICMJE / Nature / IEEE all use unstructured stage language. The matrix supports SLR-centric (B1) only for `systematic-review` mode; for other ARS modes (deep-research / academic-paper), a B2/B3/B4/B5 option may serve better. Open question: should ARS treat `systematic-review` mode as a special case, or unify under one hierarchical taxonomy (B5) that absorbs SLR as a sub-tree?

**Q3 — Is per-stage prompt disclosure mandatory or conditional on policy choice?**

PRISMA-trAIce M6 calls for prompts (or detailed structure) when LLM/GenAI is used, but at explicit-recommend strength only (pre-Delphi). ICMJE / Nature / IEEE do not mandate prompts. A schema that mandates prompts unconditionally over-aligns with PRISMA-trAIce (and treats a pre-consensus framework as binding). A schema that omits prompts loses the SLR-specific content ceiling. Open question: should the schema gate prompts on `mode == systematic-review` AND `tool_type ∈ {LLM, GenAI}`, or leave both gates to user/renderer?

**Q4 — What's the failure mode if disclosure is incomplete? (Pipeline halt / warning / silent log)**

This is a runtime-policy question that ties to Dimension D options. D1 / D4 mean pipeline halt or forced backfill (strictest). D2 means render skip (silent). D3 means warning surfaced with a `legacy: true` marker. None of the 4 anchors specifies a failure mode — they describe what to disclose, not what happens when disclosure is absent. Open question: does ARS prefer to be strict (halt + force user attention), defensive (silent log + audit later), or transparent (warning + render the gap)?

**Q5 — Backward compatibility horizon: how long do we accept legacy boolean entries?**

ARS has existing literature_corpus entries with boolean/narrative `ai_disclosure`. The matrix does not impose retrospective disclosure obligation (Dimension D evidence). Open question: is "indefinite" the right horizon (D3 soft acceptance forever), or should the implementation issue set a deprecation date (e.g., 12 months from schema-issue close → reject legacy)? Implementation cost trades off audit honesty.

**Q6 — Is a hybrid schema warranted? This is itself a hypothesis to test.**

The 4-anchor matrix surfaces three structural facts that argue for some form of hybrid:
- ICMJE / Nature / IEEE all skew to `not-addressed` (9, 7, 9 of 16) but each contributes a distinct shape no other anchor provides. A single-anchor schema loses two-thirds of the design space.
- PRISMA-trAIce field-rich content does not transfer cleanly outside SLR.
- 4-anchor #14 location enums have empty intersection.

These three facts make "single-anchor verbatim alignment" hard to defend. But "hybrid" itself can mean Dimension A2 (Structured object covering ICMJE/Nature/IEEE text-side) OR A5 (Event-log with anchor-conditional applicability) OR B4 (Two-track by mode) OR C5 (Versioned policy profile). Open question: which hybrid axis (data model / stage taxonomy / policy expression) is the load-bearing one?

### 6.2 Additional questions surfaced by Phase 2/3 cell-filling

These questions did not appear in the #106 baseline. They emerged from specific matrix patterns observed during cell-filling.

**Q7 — Does the copyediting carve-out have semantics distinct from boolean exemption?**

Two of the 4 anchors address the copyediting carve-out (Nature, IEEE); the other two (PRISMA-trAIce, ICMJE) leave it `not-addressed`. Among the two addressed anchors, Nature **eliminates** disclosure ("does not need to be declared") and IEEE **downgrades** strength while preserving location and content ("disclosure as noted above is recommended"). If ARS schema supports the carve-out, it must choose whether `exempted_uses: [copyediting]` means "boolean off" (matches Nature) or "strength downgrade preserving location/content" (matches IEEE). Open question: should the carve-out be a single field or a struct with strength + location preserved?

**Q8 — Should the schema model "level of involvement" separately from stage?**

IEEE #5 carries explicit-mandate strength for a "brief explanation regarding the level at which the AI system was used to generate the content"; §4.6 #4 interprets that level language as degree-of-involvement rather than workflow stage (and classifies #4 as implicit on this basis). The distinction matters because degree-of-involvement (e.g., "full drafting" vs "outline only" vs "paragraph-level suggestion") is not the same axis as workflow stage. None of Dimensions A–E's options model degree-of-involvement separately from stage. If IEEE #5's mandate is in scope, the schema needs a 17th field (`level_of_involvement` or similar) that may or may not belong in Dimension A.

**Q9 — Should image-rights regimes be unified or anchor-specific?**

ICMJE #16 (text attribution + no-AI-as-primary-source) and Nature #16 (default-prohibit publication + 3 carve-outs + labelling) handle the same field by structurally different policies. IEEE #16 folds images into the general acknowledgments mandate. PRISMA-trAIce #16 is implicit. Open question: does ARS unify image-rights into a single field (losing Nature's regime-specific shape) or carry per-anchor variants (with anchor-conditional rendering)?

**Q10 — Is "no AI use" itself a disclosable statement, or is silence default-OK?**

The matrix is silent on whether legacy entries with no AI disclosure should be interpreted as "no AI was used" (positive fact) or "disclosure status unknown" (epistemic gap). All 4 anchors describe forward-looking obligations conditional on AI use. ARS's current schema treats absence of disclosure as silence. Open question: does the new schema require an explicit `ai_used: false` for the no-AI case, or accept silence as backward-compatible default?

### 6.3 Notes on scope

These 10 questions are **input to the implementation issue**, not closure gates for this discovery. Discovery closes when the matrix + design space + open-questions thread are linked. Whether the implementation issue answers all 10, a subset, or reframes them entirely is a separate decision the community + maintainer thread will surface.

---

## 7. Phase closure notes

### 7.1 Phase 1 (shipped)

Phase 1 was **scaffold + provenance** only. It deliberately filled zero cells. The infrastructure it locked:

- 4 anchor URLs Wayback-archived (capture timestamps recorded in §3)
- 4 local HTML mirrors with SHA-256 hashes (in `snapshots/manifest.yaml`)
- Document structure for Deliverable 1 (4 × 16 = 64 cell placeholders) + Deliverable 2 (5 dimensions) + Deliverable 3 (6 open questions)
- Verification protocol for downstream cell-fillers

### 7.2 Phase 2 (shipped — commit 2 of PR #107)

Phase 2 fills **32 of 64 cells**: PRISMA-trAIce (§4.3) and ICMJE (§4.4). Both anchors fully read end-to-end before any `not-addressed` cell was emitted.

**Cell distribution summary** (32 cells total across two anchors):

| Anchor | explicit-mandate | explicit-recommend | conditional-mandate | implicit | not-addressed | unknown |
|---|---|---|---|---|---|---|
| PRISMA-trAIce | 0 | 10 | 0 | 3 | 3 | 0 |
| ICMJE | 2 | 2 | 0 | 3 | 9 | 0 |
| **Phase 2 total** | **2** | **12** | **0** | **6** | **12** | **0** |

**Key observations** (advisory; Deliverable 2/3 will weigh these):

1. **Anchor complementarity**: ICMJE sets the *policy floor* (must-disclose, human-responsibility, no-plagiarism); PRISMA-trAIce sets the *content ceiling* (tool name, version, prompts, performance metrics — SLR-specific granularity). Neither anchor alone covers ARS's 16-field aspiration.
2. **Zero `unknown` cells**: both anchors were fully readable in single sessions (PRISMA-trAIce 14 checklist items + Methods §; ICMJE §V.A two paragraphs). The 10-cell `unknown` ceiling from §4.1 stays available for Nature + IEEE in Phase 3 if needed.
3. **`not-addressed` skew on ICMJE** (9/16): expected given ICMJE's deliberate framework-level scope. This is a discovery signal, not a flaw in ICMJE — it means a schema chasing ICMJE-only alignment would have a small core (mandate-only) and large optional space.
4. **No `explicit-mandate` in PRISMA-trAIce**: by design, the proposal is pre-Delphi. Any schema that treats PRISMA-trAIce items as hard requirements would be over-reading the source.
5. **Tool-type-conditioned recommendation** in PRISMA-trAIce M6 (Prompts): "if any" / "LLM/GenAI tool used" → this is the only cell where applicability shifts based on tool *type*, not just AI-use binary. Strength stays explicit-recommend (consistent with the pre-Delphi no-mandate rule); the conditioning is on whether the field *applies*, not on whether it is mandatory. Suggests stage-taxonomy Dimension B (Phase 3) may need to handle tool-type-conditioned fields independent of mandate strength.

**Acceptance for Phase 2** (commit 2 of PR #107): 32 cells filled with source-strength classification + verbatim quote (or inference passage) + locator; SHA-256 of 4 snapshot HTML files unchanged from Phase 1; document parses as valid Markdown.

### 7.3 Phase 3a (shipped — commit 3 of PR #107)

Phase 3a fills **16 more cells** (Nature Portfolio §4.5), bringing the running total to **48 of 64 cells**. Nature was fully read end-to-end across §AI authorship and §Generative AI images before any `not-addressed` cell was emitted. Sections §AI use by peer reviewers and §Editorial use are out of scope per §2.2 (author-side obligations only).

**Cell distribution after Phase 3a** (48 cells across three anchors):

| Anchor | explicit-mandate | explicit-recommend | conditional-mandate | implicit | not-addressed | unknown |
|---|---|---|---|---|---|---|
| PRISMA-trAIce | 0 | 10 | 0 | 3 | 3 | 0 |
| ICMJE | 2 | 2 | 0 | 3 | 9 | 0 |
| Nature Portfolio | 3 | 2 | 0 | 4 | 7 | 0 |
| **Phase 3a total** | **5** | **14** | **0** | **10** | **19** | **0** |

**Key observations from Nature** (advisory; Deliverable 2/3 will weigh these):

1. **3-anchor hybrid emerging**: ICMJE = policy floor (must-disclose + must-take-responsibility); PRISMA-trAIce = SLR content ceiling (item-level granularity); Nature = section-of-record + carve-out shape (Methods location + copyediting predicate + image-rights regime). Each anchor contributes a distinct shape no other anchor provides.
2. **#15 (copyediting exemption predicate) lights up for the first time**: PRISMA-trAIce and ICMJE both leave this `not-addressed`. Nature is the first anchor to define an explicit carve-out boundary with prose definition. Dimension C (Phase 3) needs to handle whether copyediting carve-out is in scope.
3. **#16 (image rights) is anchor-specific enum-of-policies, not a single boolean**: ICMJE #16 = text-attribution rule (forbids citing AI as primary source); Nature #16 = default-prohibit publication + 3 carve-outs + labelling-required. The two anchors handle the same field by structurally different policies. Dimension A (Phase 3) value-type design space needs to accommodate per-policy structure, not a flat boolean.
4. **Same source sentence reused across cells (#9 + #10)**: Nature's "In all cases, there must be human accountability for the final version of the text" sentence is cited from both #9 (oversight method) and #10 (responsibility) because it carries both facets simultaneously. This pattern (one source sentence → multiple cell facets) is allowed under §4.1 and is informative for Dimension A (data model): a single disclosure clause may map to multiple structured fields.

**Acceptance for Phase 3a** (commit 3 of PR #107): 48 cells filled cumulatively; Nature SHA-256 unchanged from Phase 1; document parses; codex gpt-5.5 xhigh review converged to 0 findings in 2 rounds.

### 7.4 Phase 3b.1 (shipped — commit 4 of PR #107)

Phase 3b.1 fills the **final 16 cells** for IEEE (§4.6), bringing the matrix to **64 of 64 cells complete**. IEEE was fully read end-to-end — the substantive policy text is 2 short paragraphs (~150 words combined) inside `<div itemprop="articleBody">`. The 212 KB snapshot HTML is mostly IEEE.org site chrome / menu / footer. The webinar reference and Author Center pointer carry no normative content; the linked video is out of scope as a separate medium without byte-stable transcript.

**Cell distribution after Phase 3b.1** (64 cells across four anchors):

| Anchor | explicit-mandate | explicit-recommend | conditional-mandate | implicit | not-addressed | unknown |
|---|---|---|---|---|---|---|
| PRISMA-trAIce | 0 | 10 | 0 | 3 | 3 | 0 |
| ICMJE | 2 | 2 | 0 | 3 | 9 | 0 |
| Nature Portfolio | 3 | 2 | 0 | 4 | 7 | 0 |
| IEEE | 4 | 1 | 0 | 2 | 9 | 0 |
| **Matrix total** | **9** | **15** | **0** | **12** | **28** | **0** |

**Key observations from IEEE** (advisory; Deliverable 2/3 will weigh these):

1. **4-anchor hybrid complete**: ICMJE = policy floor / PRISMA-trAIce = SLR content ceiling / Nature = section-of-record + carve-out shape / IEEE = location closed-enum tightener + carve-out downgrade-not-eliminate construction. Each anchor contributes a distinct shape, but **the four shapes do not perfectly compose** — Dimension A and Dimension C (Phase 3) must decide whether to merge or preserve the divergences.
2. **Length is not a reliable signal of normative density**: IEEE's snapshot is 212 KB (largest of the four anchors as a file), but its substantive policy is 2 paragraphs — shorter than PRISMA-trAIce's Table 1 (longest) and equal to ICMJE in paragraph count. The opposite is also true: PRISMA-trAIce is the longest as a document but pre-Delphi, so it has zero mandate strength. A schema designer comparing anchors must read substance, not byte count.
3. **Disclosure-location closed enum widens to 4 distinct options across the matrix**: PRISMA-trAIce (6-section row enum) / ICMJE (cover-letter + appropriate-section) / Nature (Methods + image-caption + suitable-alternative) / IEEE (acknowledgments-only). None of the 4 enums match. Dimension C (policy expression) must decide whether ARS prescribes one location, accepts a venue-supplied location, or carries policy-aware location resolution.
4. **Two carve-out shapes for copyediting (#15)**: Nature ("does not need to be declared" — eliminate) vs IEEE ("disclosure as noted above is recommended" — downgrade-not-eliminate). PRISMA-trAIce and ICMJE leave #15 `not-addressed`. This is the cleanest binary split across the 4 anchors and informs Dimension D (legacy disclosure handling): how should ARS treat copyediting-only AI use?
5. **`not-addressed` count converges at 9 for both framework-level anchors (ICMJE, IEEE)** by different delegation routes. PRISMA-trAIce (3 not-addressed) and Nature (7 not-addressed) sit below this floor because they specify more fields directly. This suggests there is a **structural ceiling on what framework-level brevity can specify**, independent of which audience the policy delegates to. Dimension B (Phase 3) stage taxonomy can leverage this: a stage taxonomy that aligns with framework-level scope will be `not-addressed`-heavy regardless of which framework is chosen.
6. **No `unknown` cells across the entire matrix**: All four anchors were fully read end-to-end. The 10-cell `unknown` ceiling from §4.1 went unused.

**Acceptance for Phase 3b.1** (commit 4 of PR #107): 64 of 64 cells filled cumulatively; IEEE SHA-256 (`3ab8db50…`) unchanged from Phase 1; document parses; codex gpt-5.5 xhigh review converged to 0 findings in 2 rounds (Round 1 P1 = cross-anchor "mandate in ICMJE and Nature" overstatement fixed to "at least one of ICMJE/Nature treats at mandate strength").

### 7.5 Phase 3b.2 (shipped — commit 5 of PR #107)

Phase 3b.2 builds §5 Deliverable 2 design space: 5 dimensions A–E (Value-type / Stage taxonomy / Policy expression / Legacy handling / Renderer target), each with 4–5 credible options enumerated, each option scored across 4 trade-off axes (alignment depth / schema simplicity / backward-compat burden / integration cost). §5.6 consolidates 13 distinct option-pairs surfaced as load-bearing in the per-dimension Interaction notes. No option is selected.

**Acceptance for Phase 3b.2** (commit 5 of PR #107): 5 dimensions, 23 options, 4-axis scoring per option, 13-pair interaction inventory; document parses; codex gpt-5.5 xhigh review converged to 0 findings in 3 rounds (Round 1 = 6 findings incl. 3 P1; Round 2 = 2 P2; Round 3 = 0).

### 7.6 Phase 3b.3 (shipped — commit 6 of PR #107)

Phase 3b.3 surfaces §6 Deliverable 3 open questions: 6 baseline questions from #106 (Q1–Q6) verbatim with matrix-derived framing context, plus 4 additional questions (Q7–Q10) surfaced from Phase 2/3 cell-filling patterns not in the baseline set. §6.3 scope note clarifies these 10 questions are input to the implementation issue, not closure gates for this discovery.

**Acceptance for Phase 3b.3** (commit 6 of PR #107): 6 baseline questions verbatim + 4 surfaced; each question has matrix-evidence context paragraph and remains genuinely open (more than one defensible answer per matrix); no implicit option selection. Discovery acceptance criterion from #106 is "thread linked and open" — the GitHub Discussions thread will be linked when this PR merges.

---

## 8. Related

- v3.7.3 spec: `docs/design/2026-05-12-ars-v3.7.3-claim-faithfulness-and-contaminated-source-spec.md` (locator infrastructure prior art)
- #102 (v3.7.4 triangulation) — orthogonal advisory-signal pattern reference
- #103 (v3.8 L3 audit agent) — disclosure granularity may feed audit signal; RubricEM integration section in #103 references stage-aware disclosure (Borrow 2 mention)
- #104 (README Zhao et al. motivation) — corpus-scale evidence backing for why disclosure granularity matters
- #105 (v3.7.3 migration tool) — orthogonal pattern reference if AI disclosure schema migration is later needed
