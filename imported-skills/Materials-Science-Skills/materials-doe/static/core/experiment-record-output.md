# Experiment Record Output

`materials-doe` emits an `experiment-record.yaml` by default whenever a finalized experimental design is produced.

## When to emit

- After the user confirms the factor-level table and response variables.
- After a design matrix (orthogonal, RSM, screening, or mixture) is finalized.
- Before handing off to `materials-data` or `materials-writing`.

## Output behavior

- If the user asks only for a textual summary, still provide the YAML as a downloadable artifact.
- If the user explicitly opts out (e.g., "just give me the table"), skip the YAML.
- Never emit a record before the design is confirmed.

## Record content

Use the schema in `_shared/core/experiment-record-schema.yaml`. At minimum include:

- `version`, `record_type`, `study_id`, `created_by`, `created_at`
- `response_variables` (from the design objective)
- `factors` and `levels` (from the factor-level table)
- `design.type` and `design.runs` (from the design matrix)
- `direction_profile` (from `.materials/profile.yaml` if available)

Optional but recommended:

- `materials`, `processing`, `characterization` (ask the user or leave placeholders)
- `evidence_links` (empty initially; populated during data analysis and writing)
- `terminology` (seed from user-provided terms)

## Placeholder rules

- Use `null` for unknown fields, never invent values.
- Surface placeholders such as `[needs supplier]` in the YAML comment or value when human readability matters.
