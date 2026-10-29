# Fraud, Waste & Abuse Detection

Turn a claims dump into investigator-ready referral packets. 22 deterministic detectors catch
what rule engines catch — NCCI PTP/MUE edits, OIG/state exclusions, impossible days, global-period
unbundling, opt-out billing, TPL — then Claude adjudicates the judgment calls a rule engine can't:
was the modifier-59 pair clinically distinct? Is the utilization outlier explainable by case mix?
Does a secondary diagnosis satisfy the LCD? Every dollar traces to a deterministic source row;
every adjudication cites the policy text it relied on.

> **Not a determination of fraud.** Outputs describe "indicators consistent with [scheme]" and are
> rendered for SIU review only.

## What you get

A `~/.claude/data/healthcare/fraud-detection/out/run-<timestamp>/` directory with:

- **`index.html`** — ranked dashboard: every flagged provider, exposure $, scheme mix, finding
  count, top adjudication outcomes. Sortable, links into packets.
- **Per-provider referral packets** (`packet-<npi>.html` + `.xlsx`) — exposure $, scheme narrative,
  the exact NCCI/PFS/LEIE/LCD row that triggered each finding, the implicated claim lines, the
  adjudicator's reasoning, and a verbatim policy excerpt (MLN1783722, NCCI Policy Manual, the
  governing LCD/state-manual paragraph).
- **Stage snapshots** (`referrals.json`, `adjudicated.json`, `synthesized.json`) — full audit
  trail. Adjudicate may **dismiss or downgrade** a finding, never add one or change a dollar.
- **Medicaid + Medicare** — one `lob` flag routes the right NCCI tables, state exclusion lists,
  and state policy text per line of business.

## Quickstart

All fetched data + run output land at `~/.claude/data/healthcare/fraud-detection/` (override the
parent dir with `$CLAUDE_HEALTHCARE_DATA`) — never under the plugin install path.

```bash
cd skills/fraud-detection
export CLAUDE_HEALTHCARE_DATA="${CLAUDE_HEALTHCARE_DATA:-$HOME/.claude/data/healthcare}"
node scripts/fetch-reference.js 2026q3   # one-time: NCCI/PFS/LEIE/MCD/benchmarks → $CLAUDE_HEALTHCARE_DATA/fraud-detection/data-cache/ (~2GB)
# follow LOAD-CLAIMS.md to populate $CLAUDE_HEALTHCARE_DATA/fraud-detection/data-cache/corpus.duckdb from your claims extract
claude                                   # then: /fraud-detection
```

Watch the per-finding fan-out live with `/workflows`. Or run the deterministic floor alone:
`node scripts/screen.js "$CLAUDE_HEALTHCARE_DATA/fraud-detection/data-cache/corpus.duckdb" 2026q3 medicaid` → `$CLAUDE_HEALTHCARE_DATA/fraud-detection/out/run-*/referrals.json`.

## How it works

```
corpus.duckdb ──► [1] DETECT  — 22 deterministic detectors (D1–D22), zero model calls,
                                citation gate: every finding carries its source-row id
                       │
                       ▼
                 [2] ADJUDICATE — per-finding LLM judge on the gray-area detectors
                                (D2 unbundling · D4 medical-necessity · D7 outlier · D13 global-period);
                                $-audit: post-adjudication exposure ≤ tier-1 floor, always
                       │
                       ▼
                 [3] SYNTHESIZE — provider narratives + adversarially-verified novel leads
                                (cross-detector patterns, ownership rings, referral loops)
                       │
                       ▼
                 dashboard · referral packets · xlsx
```

Full detector grid, data lineage, and design rationale: [ARCHITECTURE.html](ARCHITECTURE.html).

## Bring your own claims

- **Your claims** → [LOAD-CLAIMS.md](LOAD-CLAIMS.md). Map your 837/encounter feed into six tables
  (`claims`, `claim_lines`, `claim_dx`, `members`, `enrollment`, `inpatient_stays`) per
  [`claims-schema.sql`](claims-schema.sql) and land them in `~/.claude/data/healthcare/fraud-detection/data-cache/corpus.duckdb`.
- **Public reference data** → [REFERENCE-DATA.md](REFERENCE-DATA.md). `fetch-reference.js` pulls
  NCCI, PFS RVU, LEIE, revoked/opt-out, MCD coverage, Part B/D/DME benchmarks, ownership, and
  51-state Medicaid policy text into a versioned `reference.duckdb`. All public, all reproducible.

## What it doesn't do

- **Not a real-time edit engine** — this is a retrospective sweep / SIU lead generator, not a
  pre-pay claims editor.
- **Not a determination** — every output is an indicator for human investigation.
- **Not a black box** — if a finding can't cite its NCCI/PFS/LCD/LEIE source row, the gate drops it
  before it ever reaches the model.

## CPT® / data licensing

CPT® codes and descriptions are copyright American Medical Association. CPT is a registered
trademark of the AMA. Use of CPT in this tool requires a valid AMA CPT license; payers
processing claims typically hold one. The NCCI, PFS, and MCD datasets this tool ingests carry
the AMA's standard license notice — see the header of any fetched NCCI file. This tool does
not redistribute CPT content; it reads the files you fetch under your license.
