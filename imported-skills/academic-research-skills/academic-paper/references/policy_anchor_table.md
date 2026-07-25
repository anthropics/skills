# Policy Anchor Table

**Status**: #108 implementation (parented to Decision Doc 20ed72d)
**Parent skill**: `academic-paper`
**Consumer**: `policy_anchor_disclosure_protocol.md` (the LLM-prose renderer reads this table at runtime when in `disclosure` mode with `--policy-anchor=<a>` selector).
**Provenance**: cells below carry verbatim policy quotes lifted from the discovery doc §4.3-4.6 source-of-truth (`docs/design/2026-05-13-ai-disclosure-schema-discovery.md`). Each anchor section records its snapshot id + truncated sha256 so the lint validator can confirm provenance integrity. Live URLs may drift after capture; the wayback snapshot is canonical.

**Lint contract**: `scripts/check_policy_anchor_table.py` enforces 4-anchor coverage, 16-field-per-anchor canonical order, source_strength enum membership, and verbatim-quote presence for mandate/recommend/conditional cells. Mutation tests live at `scripts/test_check_policy_anchor_table.py`.

**Nature ↔ v3.2 venue de-dup**: the Nature anchor below shares its substantive policy content with the v3.2 Nature venue renderer in `venue_disclosure_policies.md`. Both files cross-reference the canonical source pointer `shared/policy_data/nature_policy.md` so a future single-source-of-truth refactor can byte-compare imported substrings without breaking either consumer. The dedup pointer presence is lint-enforced via `verify_nature_dedup_with_venue` in `check_policy_anchor_table.py`.

**Forbidden by Decision Doc §4.3 (renderer must honour these):**
- G1 — no `ai_disclosure` field is added to the corpus entry schema; the renderer reads this table at runtime, no schema change.
- G9 — image-rights regimes stay anchor-specific; the renderer MUST NOT unify field #16 into a single boolean across the four tables.
- The shared `shared/policy_data/nature_policy.md` source MUST live outside any anchor-specific or venue-specific file so neither consumer can drift unilaterally.

---

## Anchor: prisma-trAIce

**Snapshot:** `prisma-trAIce:wayback=20260513075443` (sha256: f95fc59f…)
**Anchor caveat:** PRISMA-trAIce is a **pre-Delphi proposal** (Holst et al. 2025). It has not undergone formal consensus; no item carries `explicit-mandate` strength. Item-level directives use reporting-guideline verbs ("describe", "report", "include") classified here as `explicit-recommend` within the proposed framework. The framework itself is `conditional-mandate` on "AI tool used as methodological tool in an SLR" — outside that condition the framework does not apply.
**Track gate:** the renderer routes to this anchor only when the upstream pipeline (or cold-start `mode=` input) sets `slr_lineage=true`. See `policy_anchor_disclosure_protocol.md` §4.4 #1 resolution.

| # | Field | Source strength | Verbatim quote | Locator | Value type |
|---|---|---|---|---|---|
| 1 | AI tool name | explicit-recommend | "For each AI tool or system used: a. Specify the name, version number (if applicable), and developer/provider." | Table 1, M2.a | narrative |
| 2 | AI tool version | explicit-recommend | "Specify the name, version number (if applicable), and developer/provider." | Table 1, M2.a | narrative |
| 3 | AI tool developer / manufacturer | explicit-recommend | "Specify the name, version number (if applicable), and developer/provider." | Table 1, M2.a | narrative |
| 4 | Stage / phase of use | explicit-recommend | "For each AI tool, clearly describe: a. The specific SLR stage(s) where it was applied (e.g., search, screening, data extraction, Risk of Bias assessment, synthesis, drafting)." | Table 1, M3.a | narrative |
| 5 | Specific task within stage | explicit-recommend | "b. The precise task(s) the AI was intended to perform at each stage." | Table 1, M3.b | narrative |
| 6 | Affected manuscript sections / content locator | implicit | (inference passage) Items T1, A1, I1, R1, D1, D2 each prescribe a *manuscript section* for disclosure but the framework does not require an explicit per-task content-locator field. | Table 1 row headings | narrative |
| 7 | Date(s) of use | not-addressed | — | — | — |
| 8 | Prompts | explicit-recommend | "For each LLM/GenAI tool used, report: a. The full prompt(s) employed for each specific task. If prompts are extensive, provide a detailed description of their structure, key instructions, context provided..." | Table 1, M6.a | narrative |
| 9 | Human oversight method | explicit-recommend | "Describe the process of human interaction with and oversight of the AI tool(s) at each stage: a. How many reviewers interacted with/validated the AI outputs for each task? b. Did reviewers work independently when validating AI outputs?" | Table 1, M8.a–g | narrative |
| 10 | Human responsibility statement | not-addressed | — | — | — |
| 11 | Performance evaluation method | explicit-recommend | "Describe methods used to evaluate the AI tool(s) performance for the specific tasks within the review (if applicable and feasible). This may include: a. The reference standard used for evaluation... b. The metrics used..." | Table 1, M9 | narrative |
| 12 | Performance evaluation results | explicit-recommend | "Report the results of any performance evaluations of the AI tool(s) for the specific tasks within the review (as described in P-trAIce M9). Include quantitative results (see M9) and measures of agreement between AI and human reviewers if assessed." | Table 1, R2 | narrative |
| 13 | Limitations / known failure modes | explicit-recommend | "Discuss any limitations encountered in using the AI tool(s) (eg, technical issues, biases identified, challenges in prompt engineering, unexpected outputs, limitations in AI performance for specific sub-tasks)." | Table 1, D1 | narrative |
| 14 | Disclosure location | implicit | (inference passage) Each Table 1 item is row-categorized by manuscript section (Title / Abstract / Introduction / Methods / Results / Discussion), implying section-of-record per item. | Table 1 row groupings | narrative |
| 15 | Copyediting exemption predicate | not-addressed | — | — | — |
| 16 | AI-generated image / figure / content rights | implicit | (inference passage) "Describe how data handled by AI tools (input, output, intermediate data) was managed and stored, and any measures taken to ensure data privacy, security, and compliance with copyright or terms of service, especially when using third-party cloud-based AI tools." M10 covers copyright/terms-of-service compliance for *data handled by AI tools* without dedicated AI-generated content rights field. | Table 1, M10 | narrative |

**Distribution:** 0 explicit-mandate / 10 explicit-recommend / 0 conditional-mandate / 3 implicit / 3 not-addressed / 0 unknown.
**Renderer rules (PRISMA-trAIce track):**
- Disclosure location: each Table 1 row's manuscript-section row label drives placement (Title / Abstract / Introduction / Methods / Results / Discussion). The renderer emits per-section disclosure fragments, not a single paragraph.
- Per-(tool × task) prompt scope: M6.a says verbatim "for each specific task" — the renderer produces one prompt record per (tool, task) tuple across M3.a's six SLR stages (search / screening / data extraction / Risk of Bias / synthesis / drafting). Missing tuples emit "not supplied" annotation per tuple, not per tool.
- PRISMA M6 prompt disclosure fires only when **all three** G5 gates hold: (i) PRISMA-trAIce track selected, (ii) `tool_type ∈ {LLM, GenAI}`, (iii) AI use is methodological-in-SLR (not pure copyediting). Gate (iii) fail routes to the G7 copyediting carve-out path.

---

## Anchor: icmje

**Snapshot:** `icmje:wayback=20260513075516` (sha256: 52f9e6bc…)
**Anchor caveat:** ICMJE Recommendations are **adopted** and used by 1000+ journals as baseline. Strength language is consistent ("should require" / "should describe" / "must ensure" / "is not acceptable"). The page on AI Use by Authors (§V.A) is two short paragraphs, deliberately framework-level. Many fields are `not-addressed` because ICMJE delegates section-level detail to individual journals.

| # | Field | Source strength | Verbatim quote | Locator | Value type |
|---|---|---|---|---|---|
| 1 | AI tool name | implicit | (inference passage) "the journal should require authors to disclose at submission whether they used AI-assisted technologies (such as LLMs, chatbots, or image creators)". Tool identity implied by "such technology... how they used it" but no field-level naming requirement. | §V.A, paragraph 1 | narrative |
| 2 | AI tool version | not-addressed | — | — | — |
| 3 | AI tool developer / manufacturer | not-addressed | — | — | — |
| 4 | Stage / phase of use | implicit | (inference passage) "Authors who use such technology should describe... how they used it". "How they used it" implies stage. | §V.A, paragraph 1 | narrative |
| 5 | Specific task within stage | implicit | (inference passage — same source as #4) "how they used it" implies task-level description without explicit field. | §V.A, paragraph 1 | narrative |
| 6 | Affected manuscript sections / content locator | not-addressed | — | — | — |
| 7 | Date(s) of use | not-addressed | — | — | — |
| 8 | Prompts | not-addressed | — | — | — |
| 9 | Human oversight method | explicit-recommend | "Authors should carefully review and edit the AI-generated content as the output can be incorrect, incomplete, or biased." | §V.A, paragraph 1 | narrative |
| 10 | Human responsibility statement | explicit-mandate | "Therefore, humans are responsible for any submitted material that included the use of AI-assisted technologies." | §V.A, paragraph 1 | narrative |
| 11 | Performance evaluation method | not-addressed | — | — | — |
| 12 | Performance evaluation results | not-addressed | — | — | — |
| 13 | Limitations / known failure modes | not-addressed | — | — | — |
| 14 | Disclosure location | explicit-recommend | "Authors who use such technology should describe, in both the cover letter and the submitted work in the appropriate section if applicable, how they used it" | §V.A, paragraph 1 | narrative |
| 15 | Copyediting exemption predicate | not-addressed | — | — | — |
| 16 | AI-generated image / figure / content rights | explicit-mandate | "Humans must ensure there is appropriate attribution of all quoted material, including full citations." + "Referencing AI-generated material as the primary source is not acceptable." | §V.A, paragraph 1 | narrative |

**Distribution:** 2 explicit-mandate / 2 explicit-recommend / 3 implicit / 9 not-addressed / 0 unknown.
**Renderer rules (ICMJE track):**
- Disclosure location: two-channel — cover letter (cite ICMJE language verbatim) + manuscript "appropriate section". Renderer emits separate paragraphs per channel, not a single duplicated paragraph.
- Field #10 mandate triggers a human-responsibility sentence using ICMJE's verbatim language. This sentence appears regardless of which other facets are USED, as long as at least one AI category is USED in the run.
- Field #16 mandate produces a paragraph noting (a) appropriate attribution + full citations for AI-quoted material, (b) AI-generated material may not be cited as primary source. The renderer surfaces this paragraph even when no images are involved (the rule covers text-attribution).

---

## Anchor: nature

**Snapshot:** `nature:wayback=20260513075542` (sha256: cf691cba…)
**Source-of-truth pointer:** see `shared/policy_data/nature_policy.md` for the canonical substantive policy text; the v3.2 venue renderer (`venue_disclosure_policies.md` Nature entry) shares this source. **De-dup invariant:** edits to Nature-specific policy quotes must go through `shared/policy_data/nature_policy.md` first; both consumers re-cite from there. Lint contract enforced by `verify_nature_dedup_with_venue` in `check_policy_anchor_table.py`.
**Anchor caveat:** Nature Portfolio AI editorial policy is **adopted** and applies across all Nature Portfolio journals. Author-facing surface covers four sections (AI authorship / Generative AI images / AI use by peer reviewers / Editorial use). ARS matrix covers author-side obligations only (AI authorship + Generative AI images). The policy is framework-level for text and prohibition-level for images (generative AI images banned by default with three carve-outs).

| # | Field | Source strength | Verbatim quote | Locator | Value type |
|---|---|---|---|---|---|
| 1 | AI tool name | implicit | (inference passage) "Use of an LLM should be properly documented in the Methods section (and if a Methods section is not available, in a suitable alternative part) of the manuscript." Documentation requirement implies tool identity disclosure. | §AI authorship | narrative |
| 2 | AI tool version | not-addressed | — | — | — |
| 3 | AI tool developer / manufacturer | not-addressed | — | — | — |
| 4 | Stage / phase of use | implicit | (inference passage) "Use of an LLM should be properly documented in the Methods section". "Use" implies stage/task description in Methods. | §AI authorship | narrative |
| 5 | Specific task within stage | implicit | (inference passage — same source as #4) "properly documented in the Methods section" implies task-level description without dedicated field. | §AI authorship | narrative |
| 6 | Affected manuscript sections / content locator | implicit | (inference passage) "in the relevant caption upon submission" for non-generative ML image tools; LLM text use implies Methods-section documentation. | §Generative AI images (caption rule); §AI authorship (Methods rule) | narrative |
| 7 | Date(s) of use | not-addressed | — | — | — |
| 8 | Prompts | not-addressed | — | — | — |
| 9 | Human oversight method | explicit-mandate | "In all cases, there must be human accountability for the final version of the text and agreement from the authors that the edits reflect their original work." | §AI authorship | narrative |
| 10 | Human responsibility statement | explicit-mandate | "an attribution of authorship carries with it accountability for the work, which cannot be effectively applied to LLMs" + "there must be human accountability for the final version of the text" | §AI authorship | narrative |
| 11 | Performance evaluation method | not-addressed | — | — | — |
| 12 | Performance evaluation results | not-addressed | — | — | — |
| 13 | Limitations / known failure modes | not-addressed | — | — | — |
| 14 | Disclosure location | explicit-recommend | "Use of an LLM should be properly documented in the Methods section (and if a Methods section is not available, in a suitable alternative part) of the manuscript." + (for non-generative ML on images) "should be disclosed in the relevant caption upon submission" | §AI authorship + §Generative AI images | narrative |
| 15 | Copyediting exemption predicate | explicit-recommend | "The use of an LLM (or other AI-tool) for \"AI assisted copy editing\" purposes does not need to be declared." (partial-verbatim predicate) "AI-assisted improvements to human-generated texts for readability and style... [but] do not include generative editorial work and autonomous content creation." | §AI authorship | narrative |
| 16 | AI-generated image / figure / content rights | explicit-mandate | "Springer Nature journals are unable to permit its use for publication." + "All exceptions must be labelled clearly as generated by AI within the image field." | §Generative AI images | narrative |

**Distribution:** 3 explicit-mandate / 2 explicit-recommend / 0 conditional-mandate / 4 implicit / 7 not-addressed / 0 unknown.
**Renderer rules (Nature track):**
- Disclosure location: Methods section by default (or "suitable alternative" if Methods is not present in the manuscript type). Renderer emits placement instruction citing the verbatim "Methods section (and if a Methods section is not available, in a suitable alternative part)" language.
- Field #15 carve-out semantics: **eliminate** strength — copyediting-only use produces **no disclosure paragraph**, only an internal log entry. Renderer MUST NOT collapse this into a boolean shared with IEEE's downgrade semantics (Decision Doc §4.3 G7 invariant).
- Field #16 mandate: image-rights handled via the §4.4 #5 hybrid output channel. Renderer emits (a) standalone `image_disclosure_instructions.md` block describing per-image carve-out classification and Nature label text; (b) a suggested patch diff against manuscript source figure metadata (caption / alt-text / image-field caption) for the author to optionally apply. ARS does not modify manuscript source autonomously.

---

## Anchor: ieee

**Snapshot:** `ieee:wayback=20260513075605` (sha256: 3ab8db50…)
**Anchor caveat:** IEEE's guideline page (April 16, 2024) is **adopted** and applies across IEEE publications. Substantive policy is **two short paragraphs** (~150 words combined). 3 stacked mandates within paragraph 1; 1 recommend (copyediting carve-out) within paragraph 2. Notable absences vs other anchors: **no explicit human-responsibility statement** (contrasts with ICMJE/Nature), **no human-oversight requirement** (contrasts with Nature), **no image-rights regime distinct from text** (images/figures/code fold into general acknowledgments-disclosure rule).

| # | Field | Source strength | Verbatim quote | Locator | Value type |
|---|---|---|---|---|---|
| 1 | AI tool name | explicit-mandate | "The AI system used shall be identified" | Paragraph 1, sentence 2 | narrative |
| 2 | AI tool version | not-addressed | — | — | — |
| 3 | AI tool developer / manufacturer | not-addressed | — | — | — |
| 4 | Stage / phase of use | implicit | (inference passage) "accompanied by a brief explanation regarding the level at which the AI system was used to generate the content". "Level" reads as degree-of-involvement rather than SLR-style stage enum. | Paragraph 1, sentence 2 | narrative |
| 5 | Specific task within stage | explicit-mandate | "specific sections of the article that use AI-generated content shall be identified and accompanied by a brief explanation regarding the level at which the AI system was used to generate the content" | Paragraph 1, sentence 2 | narrative |
| 6 | Affected manuscript sections / content locator | explicit-mandate | "specific sections of the article that use AI-generated content shall be identified" | Paragraph 1, sentence 2 | narrative |
| 7 | Date(s) of use | not-addressed | — | — | — |
| 8 | Prompts | not-addressed | — | — | — |
| 9 | Human oversight method | not-addressed | — | — | — |
| 10 | Human responsibility statement | not-addressed | — | — | — |
| 11 | Performance evaluation method | not-addressed | — | — | — |
| 12 | Performance evaluation results | not-addressed | — | — | — |
| 13 | Limitations / known failure modes | not-addressed | — | — | — |
| 14 | Disclosure location | explicit-mandate | "shall be disclosed in the acknowledgments section of any article submitted to an IEEE publication" | Paragraph 1, sentence 1 | narrative |
| 15 | Copyediting exemption predicate | explicit-recommend | "The use of AI systems for editing and grammar enhancement is common practice and, as such, is generally outside the intent of the above policy. In this case, disclosure as noted above is recommended." | Paragraph 2 | narrative |
| 16 | AI-generated image / figure / content rights | implicit | (inference passage) "The use of content generated by artificial intelligence (AI) in an article (including but not limited to text, figures, images, and code) shall be disclosed in the acknowledgments section" — images/figures/code fold into the same acknowledgments-disclosure mandate as text; no separate image-rights regime. | Paragraph 1, sentence 1 | narrative |

**Distribution:** 4 explicit-mandate / 1 explicit-recommend / 0 conditional-mandate / 2 implicit / 9 not-addressed / 0 unknown.
**Renderer rules (IEEE track):**
- Disclosure location: acknowledgments section only — the tightest closed enum across all four anchors. Renderer emits placement instruction citing the verbatim "acknowledgments section of any article submitted to an IEEE publication" language. **No Methods placement**, no cover-letter channel.
- Field #5 + field #6 are a paired mandate (Decision Doc §4.3 G8 invariant). The renderer emits **both** a per-section locator input (free-form list with recommended IMRaD exemplars `"Introduction" | "Methods" | "Results" | "Discussion" | "Abstract" | "Title" | free-form-other`) **and** a `level_of_involvement` narrative annotation (G8 design). Emitting one without the other is non-conformant.
- Field #15 carve-out semantics: **downgrade-not-eliminate** strength — copyediting-only use still produces a disclosure paragraph at the same acknowledgments location, but with recommend-strength rather than mandate language. Renderer MUST NOT collapse this into a boolean shared with Nature's eliminate semantics (Decision Doc §4.3 G7 invariant).

---

## Related

- Decision Doc (parent): `docs/design/2026-05-14-ai-disclosure-schema-decision.md`
- Implementation spec (parent): `docs/design/2026-05-14-ai-disclosure-impl-spec.md`
- Discovery doc (verbatim quote source-of-truth): `docs/design/2026-05-13-ai-disclosure-schema-discovery.md` §4.3-4.6
- Renderer protocol (consumer): `policy_anchor_disclosure_protocol.md` (forthcoming in this branch)
- v3.2 venue policy database (Nature de-dup peer): `venue_disclosure_policies.md`
- v3.2 disclosure mode protocol (extension target): `disclosure_mode_protocol.md`
- Shared Nature policy source (canonical pointer, forthcoming): `shared/policy_data/nature_policy.md`
