# Experiment Record Input

`materials-data` can build a dataset package from an existing `experiment-record.yaml` produced by `materials-doe`.

## When to use

- The user says "build a dataset package from my DOE output" or provides `experiment-record.yaml`.
- The experimental design is already finalized and you want to avoid re-entering factors and levels.

## Validation

1. Confirm the file path.
2. Validate it against `_shared/core/experiment-record-schema.yaml` using `jsonschema`.
3. If validation fails, report the exact error and stop; do not silently ignore the record.

## Scaffolding

Use the record to pre-fill:

- `metadata.md` → `experiment_design`, `materials`, `processing`, `characterization`
- `raw_data/experiment_data_template.csv` → column headers derived from `response_variables`, `factors`, and run IDs
- `experiment_record_link.yaml` → a pointer back to the source record

Keep unknown fields as placeholders such as `[needs supplier]` or `[needs instrument]`.
