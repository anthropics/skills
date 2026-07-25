# Dataset Package

Use this structure for materials manuscript data packages:

```text
dataset-package/
  raw_data/
    experiment_data_template.csv
  processed_data/
  figures/
  metadata.md
  README.md
  data_availability_statement.md
  fair_audit.md
```

## Required Metadata

- topic
- material_domain
- target_journal
- sample_id logic
- formulation_id logic
- units
- test_standard
- replicate_count
- temperature
- humidity
- curing_condition
- aging_condition
- data_contact

## Raw Data Rules

- Keep instrument output or manually recorded raw values separate from processed data.
- Do not overwrite raw files after analysis.
- Use one row per replicate whenever possible.

## Processed Data Rules

- Processed tables should include formulas, aggregation logic, and uncertainty type.
- Figure-ready tables should keep links to raw sample IDs.

## Building a package from an experiment record

If `materials-doe` produced an `experiment-record.yaml`, pass it to the package builder:

```powershell
python plugins/materials-skills/skills/materials-data/scripts/build_fair_package.py `
  --topic "WER-EA optimization" `
  --domain asphalt `
  --journal CBM `
  --output-dir ./datasets `
  --experiment-record ./experiment-record.yaml
```

The builder will:

1. Validate the record against `_shared/core/experiment-record-schema.yaml`.
2. Pre-fill `metadata.md` with experiment design, factors, responses, materials, processing, and characterization.
3. Generate a CSV template whose columns match the record's factors and response variables.
4. Write `experiment_record_link.yaml` documenting the source record.
