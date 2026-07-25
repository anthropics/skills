# Source Anchor Checklist

Use this checklist before creating `citation_handoff.csv`, `figure_handoff.csv`, or `review_handoff.md`.

## Source status

- [ ] PDF source has page anchors, figure/table labels, and visual asset status.
- [ ] DOI/HTML source has DOI or URL, section anchors, figure/table labels if available, and excerpt anchors.
- [ ] pasted text source has a user-provided source label, pasted-text block ID, and page/figure gaps marked.

## Required anchor fields

- [ ] `claim_id`
- [ ] `source_anchor`
- [ ] `source_location`
- [ ] `original_excerpt`
- [ ] `measured_evidence`
- [ ] `inferred_mechanism`
- [ ] `boundary_or_missing_test`
- [ ] `citation_role`
- [ ] `evidence_type`
- [ ] `figure_archetype`
- [ ] `reviewer_risk`
- [ ] `handoff_target`
- [ ] `confidence_label`
- [ ] `missing_evidence_flag`

## Confidence labels

- `high`: direct source anchor, page/section or figure/table location, original excerpt, and no unresolved visual or method gap.
- `medium`: source anchor and excerpt exist, but one boundary such as page verification, statistics, visual inspection, or durability evidence is incomplete.
- `low`: source is pasted text, page/figure status is unknown, mechanism is inferred, or the row is only background/gap evidence.

## Missing-evidence flags

Use one or more of: `none`, `source missing`, `page not verified`, `figure not inspected`, `mechanism inferred`, `durability missing`, `field missing`, `statistics missing`, `method detail missing`.

## Review safety check

- [ ] Measured evidence is separated from inferred mechanism.
- [ ] The row says what claim would be too strong.
- [ ] Every figure-worthy row has a figure archetype and reviewer-risk boundary.
- [ ] Every citation-worthy row has citation role and evidence type.
