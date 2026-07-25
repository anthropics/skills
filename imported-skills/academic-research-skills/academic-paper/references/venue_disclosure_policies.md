# AI-Usage Disclosure Policy Database — v1

**Snapshot date**: 2026-04-09 (original v1 database build; individual rows carry their own "access date" recording when each was last re-verified)
**Scope**: v1 covers 6 ML/NLP-focused venues. Education/QA journals deferred to v2.
**Maintenance**: policies drift. Before submission, the user should verify against the venue's current page. The "source URL" and "access date" below record when ARS last verified each policy.

---

## How to use this file

This file is consumed by `disclosure_mode_protocol.md`. The mode looks up the venue by name, reads the structured fields below, and generates a tailored disclosure. Do NOT use this file as a standalone template — use disclosure mode.

If the venue is not listed here, the mode halts and asks the user to paste the current policy.

---

## Venue: ICLR (International Conference on Learning Representations)

| Field | Value |
|---|---|
| Source URL | https://iclr.cc/public/AuthorGuide |
| Access date | 2026-04-09 |
| Policy summary | Authors may use LLMs and AI assistants for writing and code. Authors must disclose AI use and are fully responsible for all content. AI cannot be listed as an author. |
| Required phrasing elements | Must state specific tool(s) used and specific tasks assisted. Must include "the authors take full responsibility for the content." |
| Preferred disclosure location | Paper body — a dedicated paragraph in the paper, typically at the end of the Introduction or in Acknowledgements |
| Prohibited uses | None explicitly prohibited, but fabricated citations or results would violate general scientific integrity policies |
| Authorship rule | AI tools cannot be listed as authors |

---

## Venue: NeurIPS (Conference on Neural Information Processing Systems)

| Field | Value |
|---|---|
| Source URL | https://neurips.cc/public/EthicsGuidelines |
| Access date | 2026-04-09 |
| Policy summary | Authors must disclose any use of generative AI or LLMs during manuscript preparation, including writing, coding, and data analysis. Full responsibility lies with the human authors. |
| Required phrasing elements | Must specify tool name, version if known, and specific tasks. Must state authors reviewed all AI-generated content. |
| Preferred disclosure location | Acknowledgements section or a separate "Use of AI Tools" subsection before References |
| Prohibited uses | Cannot use AI to fabricate or falsify data. Cannot list AI as author. |
| Authorship rule | AI tools cannot be listed as authors |

---

## Venue: Nature (Nature Publishing Group)

**Policy-source dedup pointer:** Nature's substantive AI policy text is co-cited by the #108 policy-anchor renderer (`policy_anchor_table.md` Nature section, verbatim quotes per 16 fields). Both consumers reference the canonical source pointer `shared/policy_data/nature_policy.md` so a future single-source-of-truth refactor can extract Nature's policy text without breaking either consumer's substantive content. Dedup invariant lint: `verify_nature_dedup_with_venue` in `scripts/check_policy_anchor_table.py`.

**Derivation note (#108 scope limitation):** the venue-track summary fields below (Policy summary / Required phrasing elements / Preferred disclosure location / Prohibited uses / Authorship rule) **are derived** from `shared/policy_data/nature_policy.md` but are **not auto-generated from it** — the v3.2 venue path predates the canonical source and continues to drive runtime rendering off these summary rows. If Nature's source policy drifts, **the canonical source file MUST be updated first** (per the G4 invariant) and these summary rows **MUST be reviewed and updated in the same change**. A future refactor (out of #108 scope) can replace these summary rows with an extract from the canonical source so the dedup contract is auto-enforced; until then this section is a derived view that requires manual sync.

| Field | Value |
|---|---|
| Source URL | https://www.nature.com/nature/editorial-policies/ai |
| Access date | 2026-04-09 |
| Policy summary | Authors who use AI tools — including LLMs — in the writing of a manuscript, production of images, or other elements of the research must document this use transparently in the Methods or Acknowledgements section. LLMs cannot be listed as authors. Authors are responsible for the accuracy of AI-generated content. |
| Required phrasing elements | Must name the tool and describe how it was used. Must state authors verified and take responsibility for all content. Nature encourages detailed descriptions. |
| Preferred disclosure location | **Methods section** (recommended by Nature) or Acknowledgements. Also mention in the cover letter. |
| Prohibited uses | AI-generated text or images cannot be presented as original human work without disclosure. Fabrication of references or data is prohibited under general integrity policy. |
| Authorship rule | AI tools cannot meet authorship criteria (accountability requirement) and must not be listed as authors |
| Notes | Lu et al. (2026, Nature 651:914-919) provides a worked example: their AI Scientist paper includes full disclosure in Methods and Ethics Statement, with explicit IRB-style approval for the human reviewer participation. |

---

## Venue: Science (AAAS)

| Field | Value |
|---|---|
| Source URL | https://www.science.org/content/page/science-journals-editorial-policies |
| Access date | 2026-04-09 |
| Policy summary | Authors must disclose any use of AI-generated text, figures, or data in the manuscript. The use of AI writing tools must be documented in the Acknowledgements section or in Materials and Methods. AI tools are not authors. |
| Required phrasing elements | Must identify the AI tool by name. Must indicate which parts of the manuscript were aided by the tool. Must affirm that authors verified the accuracy of all AI-generated content. |
| Preferred disclosure location | **Acknowledgements** (preferred) or **Materials and Methods** |
| Prohibited uses | AI-generated text submitted without disclosure violates editorial policy. Fabricated figures or data are prohibited. |
| Authorship rule | AI tools cannot be listed as authors; all listed authors must meet ICMJE criteria |

---

## Venue: ACL (Association for Computational Linguistics)

| Field | Value |
|---|---|
| Source URL | https://www.aclweb.org/adminwiki/index.php/ACL_Policy_on_Publication_Ethics#Guidelines_for_Generative_Assistance_in_Authorship |
| Access date | 2026-06-07 |
| Policy summary | Use of generative AI to create content must be fully disclosed in the **Acknowledgements** section (the policy's own example: "Section 3 was written with inputs from ChatGPT"). Disclosure is graduated by use type: language-only assistance (paraphrasing/polishing) and short-form input assistance (predictive keyboards) do **not** require disclosure; low-novelty text generation and AI-suggested new ideas **do**. AI literature-search tools require no special disclosure but the usual citation-accuracy and thoroughness requirements still apply. Authors are fully responsible for all submitted content. |
| Required phrasing elements | Name the tool and the specific content it produced (the policy example states the section and the tool). For low-novelty generated text, also affirm the output was checked for accuracy and carries appropriate citations for both the source text and the source idea(s). |
| Preferred disclosure location | The **Acknowledgements** section (per the ACL Admin Wiki current guidance). The 2023-era separate "Use of AI Assistance" subsection is no longer the canonical location. |
| Prohibited uses | Listing a generative AI tool as an author. Using automated tools that rephrase existing work as one's own without attribution (treated as plagiarism). Generated text that copies existing work is subject to the plagiarism policy. |
| Authorship rule | AI tools cannot be listed as authors; ACL does not consider a generative model an entity that can fulfill co-authorship requirements |
| Notes | Source is the org-wide ACL Admin Wiki policy (ACL Exec-approved, current through 2025), which ARR / EMNLP 2026 link to for current paper-integrity guidance. Supersedes the 2023 ACL conference blog URL (still live but stale: it pointed disclosure at a dedicated subsection rather than Acknowledgements). |

---

## Venue: EMNLP (Empirical Methods in Natural Language Processing)

| Field | Value |
|---|---|
| Source URL | https://2026.emnlp.org/paper-integrity-policy/ (refers authors to ACL's generative-authorship guidelines; canonical text at the ACL Admin Wiki — see ACL row) |
| Access date | 2026-06-07 |
| Policy summary | For AI-assistance disclosure, EMNLP refers authors to ACL's generative-authorship guidelines. Same requirements apply. See ACL row. |
| Required phrasing elements | Same as ACL |
| Preferred disclosure location | Same as ACL: the **Acknowledgements** section |
| Prohibited uses | Same as ACL |
| Authorship rule | Same as ACL |
| Notes | EMNLP 2026 maintains its own Paper Integrity Policy page that refers authors to ACL's generative-authorship guidelines for this issue (and carries additional EMNLP/ARR-specific integrity policies beyond AI disclosure). The canonical source for the AI-disclosure rules below is the ACL Admin Wiki (see ACL row). |

---

## Adding a new venue (v2 and beyond)

To add a venue to this database:

1. Find the venue's current AI-usage policy page (not a third-party summary).
2. Copy the structured fields above.
3. Fill in each field with verbatim or closely-paraphrased policy text.
4. Record the source URL and date accessed.
5. Add the venue entry to this file in alphabetical order.
6. Update the "Scope" line at the top.

For venues without a published AI policy: record "No explicit AI-usage policy found as of {date}" and flag this in disclosure mode output so the user knows they are using the generic template as fallback.

**Education/QA journals** targeted for v2: Higher Education, Quality in Higher Education, Studies in Higher Education, Assessment & Evaluation in Higher Education, Journal of Higher Education Policy and Management. These will require separate research as their policies are less standardized than ML/NLP venues.
