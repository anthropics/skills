# Materials Science Table System

Use this reference when building review, reading, writing, data, or figure tables for WER-EA and materials manuscripts.

## Required table types

### literature-screening-table

Purpose: document how sources were selected and how each source can be used.

Required columns: citation, database/source, material system, evidence type, include/exclude decision, reason, review role, source anchor.

### mechanism-evidence-table

Purpose: separate direct mechanism evidence from performance-only evidence.

Required columns: citation, WER-EA formulation, claim, direct evidence, inferred mechanism, missing evidence, boundary, source anchor.

### test-method-table

Purpose: prevent invalid comparison across incompatible methods.

Required columns: citation, test method, standard, specimen/substrate, conditioning, measured property, units, replicate/statistics, comparability note.

### performance-comparison-table

Purpose: compare bonding, stability, rheology, and related performance without hiding conditions.

Required columns: citation, material system, dosage, test condition, control group, result, uncertainty, improvement wording, boundary.

### durability-evidence-table

Purpose: separate dry laboratory performance from wet, aged, freeze-thaw, UV, traffic, and field/service evidence.

Required columns: citation, durability condition, duration/cycle, measured property, retention/change, field relevance, missing service evidence, safe claim.

### journal-positioning-table

Purpose: map the review or manuscript angle to possible journal families.

Required columns: journal family, fit angle, evidence required, likely reviewer concern, formatting/live-check need, submission route.

## WER-EA rules

- Keep WER dosage, curing agent, emulsifier, asphalt source, and preparation route explicit.
- Do not merge SBR/WER, pure WER, and other composite systems without a material-system boundary.
- Attach every table row to a paper.md source anchor or source_map.json entry when available.
- A table cell can say `[not reported]`; it must not invent a standard, replicate count, field condition, or DOI.

Use `assets/templates/table-system-template.md` as the starting template.
