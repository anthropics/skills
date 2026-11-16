---
name: powerbi-query-integrity
description: Use whenever you run DAX queries against a Power BI / Fabric semantic model (for example through a Power BI MCP connector or the Execute Queries API). Verifies in the same call that results are not silently truncated, incomplete or stale, while spending as little context as possible.
license: MIT. See LICENSE.
metadata:
  author: Alberto Ramón López Franco
  version: "1.0.0"
---

# Power BI query integrity

Every answer built on Power BI data must come with an integrity check, and must not pull more data into the conversation than the answer needs.

## Why this exists

DAX query tools usually return a capped number of rows (a default cap of a few hundred is common; the platform's hard limit is much higher). **When the cap is hit, the result is typically cut silently**: no flag, no warning, just fewer rows. A total computed from those rows looks plausible and is wrong.

Separately, every returned row consumes context. The practical limit for row-level detail is a few hundred rows, far below any API limit. So the pattern is: **the semantic model computes, Claude only receives summaries, and every summary is checked against an independent control.**

## Golden rules

1. **Aggregate in DAX.** Use SUMMARIZECOLUMNS, SUM, COUNTROWS, TOPN. Never fetch detail rows in order to add them up yourself.
2. **Always set the row limit explicitly** (e.g. `maxRows` = 500). Never rely on the tool's default.
3. **Treat "rows returned = row limit" as truncated**, always.
4. **Never present a figure as complete unless it passed the checks below.**

## Standard pattern: one call, two queries

Send both queries in the same execute call (most tools accept several queries per call against the same model).

**Query 1: census (one row, nearly free)**

```dax
DEFINE
    VAR _t = <the SAME grouping and filters as query 2>
EVALUATE
ROW (
    "n",         COUNTROWS ( _t ),
    "sum_rows",  SUMX ( _t, [<additive control measure>] ),
    "total",     CALCULATE ( [<additive control measure>], <same filters> ),
    "last_data", <freshness expression, e.g. MAX ( Fact[Date] )>
)
```

**Query 2: data.** The real grouping, with minimal columns, short aliases, rounded amounts and an `ORDER BY`.

Ready-to-use templates are in `references/dax-patterns.md`.

## Validation (before answering)

| Check | Pass condition | If it fails |
|---|---|---|
| No truncation | rows received = `n` and < row limit | Re-aggregate higher, or use TOPN + "Rest" row |
| Reconciliation | `sum_rows` = `total` (rounding tolerance) | Look for blank groups, unmatched relationships or a non-additive measure |
| Blank groups | none, or explicitly reported | Report them as a finding (e.g. sales with no customer match); never hide them |
| Freshness | `last_data` is recent enough for the question | State the date; warn if older than expected |

## When `n` is large (more than ~300)

In order of preference:

1. Re-aggregate at a higher level (month, region, brand), or use TOPN plus a "Rest" row that closes to the total.
2. Ask the user what level of detail they actually need.
3. Only if unavoidable, paginate by key ranges, validating each page against its own census.

## Known traps

- **Snapshot tables.** Balances, receivables and inventory tables often store a full snapshot per date. Summing across dates produces absurd totals. Detect them (each date repeats the whole population) and always filter to a single date: the latest, or the one asked for.
- **Non-additive measures** (percentages, averages, distinct counts, ratios, measures typed as text) cannot serve as a control. Use an additive measure from the same fact table, or COUNTROWS.
- **Row-, object- or measure-level security.** Queries run with the user's identity. A blank result may mean "no permission", not "no data". Say so when relevant.
- **Inactive relationships and bidirectional filters** can make a grouped total legitimately differ from the grand total. If reconciliation fails, inspect the relationship path before reporting.
- **Several models loading the same fact table.** Their row counts and totals should match at the same moment; a mismatch means one was not refreshed. This is a free cross-check.

## Saving context

- Read a model's schema once and keep a short **catalog** (see below). Schemas are expensive; do not re-read them for every question.
- Only the columns you need; short aliases; `ROUND` on amounts.
- Avoid long text columns (addresses, free-text notes, UUIDs, tax IDs).
- Group questions about the same model into a single call.

## Optional: model catalog

For models queried repeatedly, keep a catalog (in a project file or in `references/`) with one row per model:

| Report / model | Model ID | Main fact table | Additive control measure | Freshness expression | Snapshot tables |
|---|---|---|---|---|---|

Validate each row once with a census query. Do not hard-code row counts or totals in a shared catalog: they change with every refresh and may be confidential.

## How to report

End every answer that uses Power BI data with one control line:

```
Control: ✓ 14/14 rows · total reconciles $X · data as of <date>
```

or

```
Control: ⚠ <what failed>, <what was done or proposed>
```
