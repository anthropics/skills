# Using experiment-record.yaml in materials-writing

## Workflow

1. If the user provides `experiment-record.yaml`, load it alongside the manifest fragments.
2. Seed the terminology ledger from `record.terminology`.
3. Pre-populate the evidence audit table from `record.evidence_links`.
4. Choose the appropriate section fragment:
   - `methods-from-record` → full Methods draft
   - `results-from-record` → full Results draft
   - `discussion-mechanism` → Discussion mechanism interpretation
   - `cover-letter` → submission cover letter
   - `highlights` → bullet highlights
5. Apply domain-specific rules and journal-family constraints on top of the generated draft.
6. Flag missing fields with placeholders, never invent content.

## When not to use the record

- If the user only provides free-text notes, use the standard section fragments.
- If the record is invalid or outdated, ask the user for clarification.
