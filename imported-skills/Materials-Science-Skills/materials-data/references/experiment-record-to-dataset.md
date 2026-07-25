# Mapping experiment-record.yaml to a Dataset Package

## Metadata mapping

| Record field | metadata.md section |
|---|---|
| `study_id` | Study Identity → study_id |
| `title` | Study Identity → topic |
| `direction_profile.domain` | Study Identity → material_domain |
| `objectives` | Study Identity → objectives |
| `response_variables` | Materials Science Fields → measured_property, unit, replicate_count |
| `factors` | Experiment Design → factors and levels |
| `design.type` | Experiment Design → design_type |
| `design.runs` | Experiment Design → run_count |
| `materials` | Materials → list |
| `processing` | Processing → steps |
| `characterization` | Characterization → techniques and standards |

## CSV column mapping

Generate CSV headers from:

- `run_id` (from `design.runs`)
- Each `factors[].name`
- Each `response_variables[].name`
- `replicate_count` (as a column or metadata)
- `notes`

## Failure modes

- Missing `response_variables` → cannot generate CSV; ask user.
- Missing `design.runs` → cannot link data to runs; fall back to manual package.
- Validation failure → stop and report.
