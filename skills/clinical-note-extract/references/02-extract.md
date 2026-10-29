# Step 2 — Extract

Goal: produce one entry per schema variable, every non-null value backed by a verbatim span.

## Before reading the note

Restate to yourself (not the user): **the note is the only source of truth.** Clinical knowledge you have from training is not admissible. If the note says something medically wrong, extract it as written. If the note omits something you "know," it is `null`.

## Read the note

Read the full note once. If it has section headers (HPI, PMH, Medications, Assessment/Plan, etc.), note them — they become `location` hints.

If the note is very long and you cannot hold it all reliably, say so in the output `flags` and process section-by-section, but **never** silently process only part of it.

## For each schema variable

1. **Find candidate spans.** Scan for text that answers this variable. There may be zero, one, or several.

2. **If zero candidates** → emit:
   ```json
   {"name": "...", "value": null, "null_reason": "not_mentioned"}
   ```

3. **If the span is present but unreadable / redacted / ambiguous** → emit:
   ```json
   {"name": "...", "value": null, "span": "<the unclear text>", "null_reason": "mentioned_unclear"}
   ```

4. **If one or more clear candidates** → for the best one (or each, if `multivalued`):
   - `value` — what the note states (number parsed, date at stated precision, string trimmed). Do **not** extrapolate precision or convert units.
   - `span` — the **verbatim** source text, including enough context to be unambiguous (typically the containing phrase or sentence).
   - `location` — section header and/or approximate line.
   - `presence` / `temporality` / `experiencer` — when the schema marks the field `finding: true`, assign per `references/assertion-classes.md` (only set axes the note moves off default). Otherwise omit.
   - `unit` — for numeric values, the unit as written in the note (or null if the note didn't state one).

5. **If multiple conflicting candidates** (e.g., two different FEV1 values) — emit the one the schema `description` selects (e.g., "post-bronchodilator"). If the description doesn't disambiguate, emit the most recent / most specific and add a `flag` noting the conflict with both spans.

## Default numeric plausibility ranges

Used when the schema omits `range`. These are sanity bounds, not normal ranges — a value outside them is almost certainly a unit or transcription error and should be flagged, not dropped.

| measure | unit | range |
|---|---|---|
| heart rate | bpm | [20, 300] |
| systolic BP | mmHg | [40, 300] |
| diastolic BP | mmHg | [20, 200] |
| temperature | °C | [30, 45] |
| temperature | °F | [86, 113] |
| SpO2 | % | [40, 100] |
| FEV1 % predicted | % | [5, 150] |
| FVC % predicted | % | [5, 150] |
| DLCO % predicted | % | [5, 150] |
| eGFR | mL/min/1.73m² | [1, 200] |
| HbA1c | % | [3, 20] |
| age | years | [0, 130] |
| weight | kg | [0.3, 700] |
| height | cm | [20, 275] |

## Write the extraction

Return the record per the output shape in rules.md.

Proceed to Step 3 (code validation) for every field with `type: code`.
