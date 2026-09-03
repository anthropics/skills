---
license: Provided under Anthropic's Terms of Service (not the Apache-2.0 LICENSE.txt used by most skills in this repo) — see NOTICE.md
source: https://github.com/anthropics/healthcare/tree/main/plugins/healthcare/skills/clinical-note-extract
name: clinical-note-extract-skill
description: Extract structured data from clinical notes with span-level provenance and null-safety. Use when users say "extract [variables] from this note", "abstract this chart", "pull structured data from these notes", "what does this note say about [field]", or when building a chart-abstraction, registry, or cohort dataset from unstructured clinical text.
---

# Clinical Note Extraction

Structured extraction from clinical notes against a user-defined schema, with span citations for every value and explicit nulls for every absence. One note or many — the path is the same: an isolated no-tools worker extracts each note, then a deterministic validation pass verifies spans and codes.

This is the extraction primitive that care-gap reasoning, adverse-event detection, trial-eligibility screening, prior-auth evidence assembly, and registry abstraction sit on.

## Steps

```
1  Define schema   — references/01-define-schema.md
2  Extract         — workflows/extract-batch.js (one isolated worker per note)
3  Validate        — span check + run each field's `check`
4  Report          — references/03-review.md
```

### Step 1 — Define schema

Read `references/01-define-schema.md`. Turn the user's request into a schema: each field is `{desc, finding?, check?}`. `desc` says what to look for in the note's own terms; `finding: true` means classify assertion; `check` is how step 3 validates (open-ended — `{kind: "terminology"|"range"|"date"|"pattern"|"enum"|..., ...params}`). Confirm with the user before extracting.

### Step 2 — Extract

However the user supplied notes — pasted text, file paths, a directory, PDFs, a FHIR connector, a database query — resolve each to plain text using whatever tools you have, then call the saved workflow with one `{id, text}` per note. The workflow's input contract is the only strict piece; how you get there is yours to figure out. It runs one `note-extract-worker` agent per note (no tools — note text is untrusted), each following `references/rules.md`, and returns one schema-enforced record per note:

```
Workflow({
  scriptPath: "<this skill dir>/workflows/extract-batch.js",
  args: {
    notes:  [{id, text}, ...],     // one or many
    schema: <the schema from step 1>,
    rules:  <Read references/rules.md verbatim>
  }
})
```

Workers have no tools — they return only what they read (`value`, `span`, `presence`/`temporality`/`experiencer`, `null_reason`, `unit`). All checks happen in step 3. Because note text rides inline in `args`, the workflow path tops out at a few dozen notes per call. For larger corpora, run `bun <this skill dir>/scripts/batch.ts <notes-dir> <schema.json> records.jsonl` instead — it reads files in trusted code and spawns one tool-disabled extraction per note with the same rules, then resume at step 3 over the resulting `records.jsonl`.

### Step 3 — Validate

Runs here in the calling session. Deterministic — no model judgment. For every record:

1. **Span check.** For every non-null field, confirm `span` appears verbatim in that note's source text. Attach `span_verified`.
2. **Run each field's `check`.** Dispatch on `check.kind`:
   - `terminology` — dedupe `(check.via, value)` across all records, look each up via whatever connector answers to `via`, attach `{code, code_status, display}`. No connector for that `via` → `code_status: "unvalidated"`, name it in the report.
   - `range` — `value` vs `[min, max]` and `unit` vs `check.unit`; attach `range_flag`.
   - `date` — confirm `value` parses as a date; attach `date_ok`.
   - `pattern` / `enum` — match; attach `check_ok`.
   - other / no `check` — nothing to attach.

A field is trustworthy when `span_verified` and its check (if any) passed. Adding a check kind = add a branch here; nothing upstream changes.

### Step 4 — Report

Read `references/03-review.md`. Produce one row per (note, field): `note_id | field | value | presence/temporality/experiencer | span | check`. Below it, the completion summary: fields requested / populated / null, and per `check.kind` what passed vs flagged (name any terminology `via` that lacked a connector). Never let a failed check or unverified span pass silently.

Offer to write records + report to `~/.claude/data/healthcare/clinical-note-extract/<run-id>/`. That directory is local working state, not an archive: do not copy it to shared drives or external systems without the user's explicit instruction, and tell the user it can be deleted once they have what they need — extracted records carry whatever PHI was in the source notes.

## Output contract

Worker emits, per field: `{value, span, location, presence?, temporality?, experiencer?, null_reason?, unit?}` — only what it read. Step 3 attaches `span_verified` plus whatever the field's `check` produced (`code`/`code_status`/`display` for terminology, `range_flag` for range, etc.).

### Optional — export as FHIR

If the user wants FHIR resources instead of flat records, the assertion axes map directly:

| record | FHIR |
|---|---|
| `experiencer != patient` | `FamilyMemberHistory.condition` (not `Condition`) |
| `presence: absent` → `verificationStatus: refuted`; `possible` → `unconfirmed`; `present` → `confirmed` | `Condition.verificationStatus` |
| `temporality: historical` → `inactive`; `current` → `active` | `Condition.clinicalStatus` |
| `temporality: hypothetical` | no native field — omit, or use a `RiskAssessment` resource |
| `value` + terminology check result | `Condition.code` as a `CodeableConcept` (`{text: value, coding: [{system, code, display}]}`) |
| `span` + `location` | `Condition.note` or a provenance extension |

This is a deterministic transform over the validated records — no model call. Offer it when the user names FHIR as the target; otherwise the flat records are the default.

## Prerequisites

Connectors for whatever `check.via` values the schema names. Missing ones don't block extraction — those fields stay unvalidated and the report names them.
