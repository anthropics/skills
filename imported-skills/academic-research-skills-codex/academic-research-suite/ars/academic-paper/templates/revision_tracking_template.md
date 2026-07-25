# Revision Tracking Template

## Usage

Use this template to systematically track all reviewer comments and their resolutions during the revision process. Copy this template at the start of each revision round, fill in the paper information, then add one row per reviewer comment.

This template works with both:
- **Revision mode** (`revision` in SKILL.md): when you have a draft and structured reviewer feedback
- **Revision Coach mode** (`revision-coach` in SKILL.md): when you have unstructured reviewer comments that need parsing first

---

## Paper Information

| Field | Value |
|-------|-------|
| Paper Title | [title] |
| Revision Round | [1 / 2] |
| Date | [YYYY-MM-DD] |
| Previous Decision | [Major Revision / Minor Revision] |
| Target Journal | [journal name] |
| Original Word Count | [N words] |
| Revised Word Count | [N words] |

---

## Revision Tracking Table

| # | Issue Description | Reviewer | Type | Section | Resolution Summary | Location of Change | Status | Reason (if not resolved) | Commitment Ledger |
|---|-------------------|----------|------|---------|-------------------|-------------------|--------|--------------------------|-------------------|
| 1 | [description] | [R1/R2/R3/DA] | [Major/Minor/Editorial] | [section] | [what was done] | [page/paragraph] | [status] | [if applicable] | See per-row nested ledger below (concern 1) |
| 2 | [description] | [R1/R2/R3/DA] | [Major/Minor/Editorial] | [section] | [what was done] | [page/paragraph] | [status] | [if applicable] | See per-row nested ledger below (concern 2) |
| 3 | [description] | [R1/R2/R3/DA] | [Major/Minor/Editorial] | [section] | [what was done] | [page/paragraph] | [status] | [if applicable] | _(empty — positive comment, no commitment)_ |

**Per-row Commitment Ledger (nested-object shape, #268).** Each concern's commitments are authored as a single nested YAML block keyed by `concern_id` — one object per commitment, with `fulfillment_status` / `unfulfilled_rationale` nested **inside** the object. There are no separate parallel cells to keep aligned, so a dropped separator or mis-numbering can no longer desynchronize status from commitment.

Placeholders use `<...>` (angle brackets) — replace each with a literal scalar. Do NOT use `[...]`: inside a YAML block square brackets parse as a flow sequence, so a half-filled `[R1-1]` becomes a one-element list, not the string `R1-1`. (The only real list here is `commitment_extracted: []`, the empty-list marker.)

```yaml
# concern 1 (multi-commitment example)
- concern_id: <R1-1>
  commitment_extracted:
    - commitment_text: "<commitment 1 text>"
      commitment_type: <add_experiment | add_analysis | add_clarification | add_citation | restructure | other>
      required_evidence_type: <new_section | new_figure | new_table | new_citation | methods_paragraph | discussion_paragraph | prose_edit | acknowledgment_only | other>
      fulfillment_status: <fulfilled | partial | not-fulfilled | explicitly-rejected-with-rationale>   # appended during revision execution
      # unfulfilled_rationale: "..."  # required iff status is non-fulfilled; OMIT when fulfilled
    - commitment_text: "<commitment 2 text>"
      commitment_type: ...
      required_evidence_type: ...
      fulfillment_status: ...

# concern 2 (single commitment)
- concern_id: <R2-1>
  commitment_extracted:
    - commitment_text: "<commitment text>"
      commitment_type: ...
      required_evidence_type: ...
      fulfillment_status: ...

# concern 3 carries no commitments (positive comment) → commitment_extracted: []
```

---

## Status Values

### RESOLVED
Change made; reviewer concern fully addressed.
- **Must specify**: exact location of change (section, paragraph, page number)
- **Must include**: brief description of what was changed
- **Example**: "Added three additional references supporting the methodology choice (Section 3.2, paragraph 2)"

### DELIBERATE_LIMITATION
Acknowledged as a boundary condition of the study design (not a flaw).
- **Must provide**: justification for why this is a design boundary, not an oversight
- **Must include**: reference to the Limitations section where this is discussed
- **Example**: "Cross-sectional design is acknowledged in Limitations (Section 5.3). Longitudinal follow-up is recommended as future research."

### UNRESOLVABLE
Would require fundamentally different research design to address.
- **Must explain**: the specific constraint that prevents resolution
- **Must recommend**: as a direction for future research
- **Example**: "Addressing this would require a randomized controlled trial, which was not feasible given ethical constraints. Added to Future Research (Section 5.4)."

### REVIEWER_DISAGREE
Respectful disagreement with the reviewer's suggestion on methodological or theoretical grounds.
- **Must provide**: evidence-based rebuttal with citations
- **Must demonstrate**: that the reviewer's concern was carefully considered
- **Example**: "We respectfully maintain our analytical approach. Smith (2022) and Chen (2023) both validate this method for our sample size and data structure. Response letter includes detailed justification."

---

## Commitment Ledger (Kong A1 / v3.11)

Per Schema 11 v3.11, each row of the Revision Tracking Table may carry an extracted commitment list. Each commitment has a `fulfillment_status` chosen from:

### fulfilled
The commitment was addressed. Required evidence (per `required_evidence_type`) is present and substantively addresses the `commitment_text`. The verification site depends on the evidence type:
- For the seven **manuscript-evidence** types (`new_section` / `new_figure` / `new_table` / `new_citation` / `methods_paragraph` / `discussion_paragraph` / `prose_edit`), the evidence lives at `revision_location` in the revised manuscript. `prose_edit` covers sentence- or paragraph-level changes (typo fixes, terminology clarifications, equation formatting, citation-style corrections) too granular for the other categories.
- For `acknowledgment_only`, the evidence lives in the Response to Reviewers (Schema 8); the manuscript does NOT need to change. `revision_location` may be empty or point to the response letter.
- For `other` (escape hatch for uncategorizable evidence), re-review surfaces an `EVIDENCE_TYPE_UNSPECIFIED` advisory prompting the author to specify the actual evidence location; verify at `revision_location` if populated.

### partial
Evidence exists but does not fully address the commitment. Example: reviewer asked for ablation on dataset X; revision adds ablation on dataset Y. Author must populate `unfulfilled_rationale` with the gap explanation.

### not-fulfilled
Required evidence is absent. Author must populate `unfulfilled_rationale` with one of:
- "done elsewhere, see §X" pointer
- "rejected, reasons: …" rationale
- "deferred to future work" acknowledgment

Silent omission triggers `COMMITMENT_GAP` advisory at re-review.

### explicitly-rejected-with-rationale
Author has decided not to address the commitment and has provided one of the three rationale forms above. This is **not** a failure — it is a documented, defensible decision. Re-review records it without raising `COMMITMENT_GAP`.

**Authoring guidance:** Fill in each commitment's extraction fields first (typically via `revision_coach_agent` Step 3.5 output — `commitment_text` / `commitment_type` / `required_evidence_type`); append `fulfillment_status` (and `unfulfilled_rationale` when non-fulfilled) **on the same commitment object** as revision execution progresses. By final submission, every non-fulfilled commitment must have a rationale on its own object.

**Nested-object shape (#268, supersedes the Kong A1 parallel-list cells):** Each commitment is one object in the concern's `commitment_extracted` list, carrying its own `fulfillment_status` and (when non-fulfilled) `unfulfilled_rationale`. There is no separate Fulfillment / Unfulfilled-Rationale column to align — status and rationale travel **with** the commitment they describe, so a dropped separator or numbering error cannot pair a status with the wrong commitment (the desync failure mode #268 closes). Omit `unfulfilled_rationale` entirely on a `fulfilled` commitment (no `""` placeholder). For positive comments with no extractable commitment, set `commitment_extracted: []` to mark the absence explicitly.

---

## Response Letter Structure

When preparing the response letter to accompany the revised manuscript, use this structure:

```
Dear Editor and Reviewers,

Thank you for the thoughtful and constructive feedback on our manuscript
"[Paper Title]" (Manuscript ID: [ID]).

We have carefully addressed all comments and provide point-by-point
responses below. Changes in the manuscript are highlighted in [yellow/
tracked changes].

---

## Response to Reviewer 1

### Comment R1-1: [Brief summary of comment]
**Type**: [Major/Minor/Editorial]
**Response**: [Your response]
**Changes made**: [Location and description of changes]

### Comment R1-2: ...

---

## Response to Reviewer 2
[Same format]

---

## Summary of Changes
- Total comments addressed: [N]
- Word count change: [±N words]
- New references added: [N]
- New figures/tables added: [N]

We believe these revisions have substantially strengthened the manuscript
and look forward to your further evaluation.

Sincerely,
[Author(s)]
```

---

## Summary Statistics

| Metric | Count |
|--------|-------|
| Total items | [N] |
| Resolved | [N] |
| Deliberate Limitation | [N] |
| Unresolvable | [N] |
| Reviewer Disagree | [N] |
| Word count change | [±N words] |
| New references added | [N] |
| New figures/tables added | [N] |

---

## Revision Completeness Checklist

Before submitting the revision, verify:

- [ ] Every reviewer comment has a corresponding row in the tracking table
- [ ] Every RESOLVED item specifies the exact location of the change
- [ ] Every DELIBERATE_LIMITATION item is discussed in the Limitations section
- [ ] Every UNRESOLVABLE item is mentioned in Future Research
- [ ] Every REVIEWER_DISAGREE item has an evidence-based rebuttal
- [ ] The response letter addresses all comments in order
- [ ] Word count is within the journal's limit after revisions
- [ ] All new references are added to the reference list
- [ ] No new errors were introduced during revision (re-run citation check)
- [ ] AI disclosure statement is updated to reflect revision assistance
