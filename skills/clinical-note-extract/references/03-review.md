# Step 4 — Review output

Goal: present the extraction in a form a clinical reviewer can verify line-by-line in seconds, then hand off the structured JSON.

## Render the review table

One row per schema variable, in schema order:

| variable | value | assertion | span | status |
|---|---|---|---|---|
| fev1_percent_predicted | 47 % | — | "FEV1 47% of predicted" | ✓ |
| home_o2 | true | present | "on 2L home O2" | ✓ |
| dlco_percent_predicted | *(null)* | — | — | not mentioned |
| primary_dx_icd10 | J44.1 | — | "COPD with acute exacerbation" | ✓ validated |
| smoking_status | *(null)* | — | "tob: [REDACTED]" | redacted |

Status column legend: `✓` populated · `✓ validated` code confirmed via MCP · `⚠ range` out-of-bounds numeric · `⚠ unvalidated` code-typed but MCP unavailable/no-match · `not mentioned` / `unclear` / `redacted` for nulls.

## Below the table

- **Completeness:** "12 requested · 9 populated · 3 null (2 not mentioned, 1 redacted)"
- **Flags:** bullet list — range violations, unvalidated codes, conflicts, long-note caveat.
- **Files:** offer to write `records.json` and this review to `~/.claude/data/healthcare/clinical-note-extract/<run-id>/` or a path of the user's choosing.

## What the reviewer does with this

The span column lets a reviewer accept or reject each row without re-reading the note. If you are running inside a pipeline that captures accept/reject, those decisions are the gold labels for evaluating and improving this skill — preserve them.
