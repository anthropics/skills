---
license: Provided under Anthropic's Terms of Service (not the Apache-2.0 LICENSE.txt used by most skills in this repo) — see NOTICE.md
source: https://github.com/anthropics/healthcare/tree/main/plugins/healthcare/skills/fraud-detection
name: fraud-detection
description: Screen a Medicare/Medicaid claims corpus for fraud, waste, and abuse and produce ranked, fully-cited investigation referrals for an SIU / program-integrity team. Use when asked to run a fraud sweep, screen claims for FWA, find billing anomalies, or generate investigation referrals over a claims dataset.
---

# Fraud Detection — claims screening → cited investigation

Screens a Medicare/Medicaid claims corpus against the public rulebook (NCCI MUE, OIG LEIE,
CMS enrollment, PFS) and produces **ranked, fully-cited investigation referrals** for an SIU.
The skill **orchestrates a three-tier investigation**: a deterministic floor does the detection,
the model judges and narrates on top, and every dollar/rule allegation traces back to the floor.

## Output framing
- **"Indicators consistent with [scheme]," not "fraud."** A pattern match doesn't establish intent
  — that's a downstream investigative/legal determination. This is standard SIU language and the
  framing the renderers use.
- **Render for review.** The skill writes packets to `$CLAUDE_HEALTHCARE_DATA/fraud-detection/out/`; the payer's SIU workflow
  decides what to do with them. The model does not send/publish on its own.

## Inputs
- **The payer's claims** in `corpus.duckdb` (canonical 6-table schema: `claims-schema.sql`). Getting
  this is **step 1** below — without it nothing else matters.
- **Quarter** (the NCCI/PFS rule set to cite against, e.g. `2026q3`).
- **Line of business** (`medicare` / `medicaid`).

## Data root
All fetched/generated state lives **outside** the plugin install path (which is wiped on upgrade)
at `~/.claude/data/healthcare/fraud-detection/` — override the parent dir with
`$CLAUDE_HEALTHCARE_DATA` (each skill appends its own name). Below, `data-cache/` and `out/` are
subdirectories of `$CLAUDE_HEALTHCARE_DATA/fraud-detection`. Resolve it once at the start of a run:
```bash
export CLAUDE_HEALTHCARE_DATA="${CLAUDE_HEALTHCARE_DATA:-$HOME/.claude/data/healthcare}"
```

## Steps
1. **Get the payer's claims into `corpus.duckdb`.** Open with: *"Where do your adjudicated claims
   live?"* and follow `${CLAUDE_PLUGIN_ROOT}/skills/fraud-detection/LOAD-CLAIMS.md` — it walks you
   and the user from "I don't know" to a populated `$CLAUDE_HEALTHCARE_DATA/fraud-detection/data-cache/corpus.duckdb`. If they
   already have a `.duckdb` with the canonical tables (schema:
   `${CLAUDE_PLUGIN_ROOT}/skills/fraud-detection/claims-schema.sql`), use it directly.

   Draft the brief (corpusDb path, quarter, line of business) and confirm scope.
2. **Seed the public reference layer (first run / new quarter only).** Detectors cite against
   `$CLAUDE_HEALTHCARE_DATA/fraud-detection/data-cache/reference/<quarter>/reference.duckdb`. If that file is missing for the
   requested quarter, fetch it now — this prints per-source `✓ name (size)` progress as ~34 sources land:
   ```bash
   node "${CLAUDE_PLUGIN_ROOT}/skills/fraud-detection/scripts/fetch-reference.js" 2026q3
   node "${CLAUDE_PLUGIN_ROOT}/skills/fraud-detection/scripts/fetch-enrichment.js"
   ```
   Requires `unzip` and `pdftotext` (poppler) on PATH; both ship with most distros / `brew install
   poppler`. Needs real network egress — if you see "Could not resolve host" for cms.gov / oig.hhs.gov,
   the command sandbox is blocking it; re-run with sandbox disabled. Policy PDFs (NCCI manual, MLN articles) land under `reference/<q>/policy/*.txt`
   for grep; everything keyed lands in `reference.duckdb`. Skip if already present. If a fetch fails
   or a table is missing, see `REFERENCE-DATA.md` for source URLs and recovery.
3. **Create the run directory.** Each invocation lands in its own minute-stamped directory so prior
   runs are preserved side-by-side. Every script honors `FRAUD_OUT_DIR`:
   ```bash
   export FRAUD_OUT_DIR="$CLAUDE_HEALTHCARE_DATA/fraud-detection/out/run-$(date +%Y%m%d-%H%M)"
   mkdir -p "$FRAUD_OUT_DIR"
   echo "$FRAUD_OUT_DIR"
   ```
   Use the printed absolute path verbatim as `outDir` in the next step.
4. **Run the investigation** by calling the **Workflow** tool with:
   - `scriptPath`: `${CLAUDE_PLUGIN_ROOT}/skills/fraud-detection/workflows/investigate.js`
   - `args`: `{ "corpusDb": "<abs path to corpus.duckdb>", "quarter": "2026q3", "lob": "medicaid", "pluginRoot": "${CLAUDE_PLUGIN_ROOT}/skills/fraud-detection", "dataRoot": "<abs $CLAUDE_HEALTHCARE_DATA/fraud-detection>", "outDir": "<abs FRAUD_OUT_DIR from step 3>" }`

   The workflow runs three stages (see "How it works"):
   - **Detect** — runs the deterministic sweep (`scripts/screen.js`, zero model) → `$FRAUD_OUT_DIR/referrals.detect.json`.
   - **Adjudicate** — one agent per judgment-required finding (D2/D4/D7/D13) sets `status` + `adjudication.reason`; mechanical detectors auto-confirm. Adjudicate may dismiss or downgrade, never add.
   - **Synthesize** — one agent per provider writes the investigator narrative, plus novel-lead discovery with adversarial verification.

   Tell the user they can watch the fan-out live with `/workflows`.
5. **Materialize the stage snapshots + render** (required — this is the reviewable deliverable). The
   workflow sandbox has no filesystem, so write its return to disk and let `apply-stages.js` produce
   the auditable spine. **`FRAUD_OUT_DIR` does not persist across separate Bash calls** — re-export
   it (to the same absolute path you printed in step 3) at the top of every shell block that needs it:
   Use the **Write** tool to save the workflow's return JSON verbatim to
   `$FRAUD_OUT_DIR/workflow-result.json` (it can be 50KB+ — don't heredoc it through Bash). Then:
   ```bash
   export FRAUD_OUT_DIR="<abs path from step 3>"
   node "${CLAUDE_PLUGIN_ROOT}/skills/fraud-detection/scripts/apply-stages.js"
   ```
   This writes `$FRAUD_OUT_DIR/referrals.adjudicated.json`, `referrals.final.json`, `referrals.json`
   (canonical, = final), and the renderer sidecars (`source-excerpts.json`, `providers.json`).

   Then render the packets FIRST, then the dashboard (the dashboard only links a provider row to its
   packet if that packet file already exists), then the xlsx:
   ```bash
   export FRAUD_OUT_DIR="<abs path from step 3>"
   node "${CLAUDE_PLUGIN_ROOT}/skills/fraud-detection/scripts/render-packet.js" --all
   node "${CLAUDE_PLUGIN_ROOT}/skills/fraud-detection/scripts/render-dashboard.js"
   node "${CLAUDE_PLUGIN_ROOT}/skills/fraud-detection/scripts/render-xlsx.js"
   ```
   → `$FRAUD_OUT_DIR/provider-packet-<npi>.html` ×N, `index.html`, `referrals.xlsx`.
6. **Show the dashboard** so the user can validate it visually.
   - **Claude Code Desktop with the preview tool available**: serve the run directory and open it
     in the side-pane preview — `npx serve "$FRAUD_OUT_DIR"` (the dashboard is `index.html`,
     so the root URL is the dashboard; packet links resolve as siblings).
   - **Otherwise** (terminal CLI, no preview tool): use the OS opener on
     `$FRAUD_OUT_DIR/index.html` — try in order, stop at the first that works:
     ```bash
     f="$FRAUD_OUT_DIR/index.html"
     open "$f" 2>/dev/null \            # macOS
       || xdg-open "$f" 2>/dev/null \   # Linux
       || wslview "$f" 2>/dev/null \    # WSL
       || powershell.exe start "$(wslpath -w "$f")" 2>/dev/null \  # WSL→Windows fallback
       || cmd.exe /c start "" "$f" 2>/dev/null \                   # Windows
       || echo "Could not auto-open; open manually: $f"
     ```
   Skip this entirely in a headless/non-interactive run (eval, CI, Cowork) — just report the path.
   Don't fail the run if opening/serving fails.
7. **Relay**: the ranked referrals (NPI, schemes, exposure $, confidence) and total exposure from
   the workflow result, verbatim where it cites numbers. Surface `meta.disclaimer` if it is set. Do
   not add any dollar or rule the deterministic floor did not produce. **End the response with the
   run-directory path on its own line** so downstream graders/tools can locate the artifacts:
   ```
   Run directory: <absolute $FRAUD_OUT_DIR>
   ```
8. **Close the loop** (optional) — see `${CLAUDE_PLUGIN_ROOT}/skills/fraud-detection/PROPOSE-DETECTORS.md`
   to mine this run for new detector candidates and payer-specific adjudicate-time checks.

## The inviolable line
The model adjudicates, explores, and narrates freely, but **any dollar or rule allegation must trace
to a detect-stage deterministic recompute** (the gate in `scripts/gate.js`). Adjudicate may **dismiss
or downgrade** a finding (with an auditable reason) — it never adds one or changes its dollars.
Synthesize narratives are separate, clearly-marked model output and never introduce a number the
floor did not compute.

## Enrichment — local cached data (canonical), MCPs for interactive only
The deterministic pipeline reads enrichment from **local cached files** (`scripts/fetch-enrichment.js`
→ `$CLAUDE_HEALTHCARE_DATA/fraud-detection/data-cache/enrichment/`, loaded via `scripts/enrichment.js`) — no runtime auth, no drift, fully
reproducible. The healthcare plugin's bundled MCP servers (CMS Coverage / ICD-10 / NPI Registry) are
for **interactive adjudicate/synthesize exploration** only; the pipeline does not depend on them.
- **ICD-10-CM** — code validity / description (NLM Clinical Tables)
- **CMS Coverage (LCD/NCD)** — medical-necessity policy index; cached, feeds D4 adjudication
- **NPI Registry** — provider taxonomy/status

## How it works (plugin layout)
- **Entry skill** — this file; orchestrates the workflow, never does the math.
- **Workflow** — `workflows/investigate.js` (Claude Code dynamic Workflow): Detect → Adjudicate → Synthesize.
- **Deterministic sweep** — `scripts/screen.js <corpus.duckdb> <quarter> <lob>` runs all detectors and
  writes `$FRAUD_OUT_DIR/referrals.json`. Zero model calls.
- **Detectors** — `scripts/dNN-*.js` (one deterministic module each, sharing the Finding shape).
- **Pipeline** — `scripts/pipeline.js` (run → gate → roll up → rank → `referrals.json`).
- **Citation gate** — `scripts/gate.js` (independently recomputes every cited number; uncited or
  non-reproducing findings are dropped — "citation-or-zero").
- **Reference data** — `scripts/reference-data.js` loads `$CLAUDE_HEALTHCARE_DATA/fraud-detection/data-cache/reference/` (NCCI/MUE, LEIE, PFS,
  enrollment), fetched by `scripts/fetch-reference.js`, versioned by date-of-service quarter.
- **Enrichment** — `scripts/enrichment.js` loads `$CLAUDE_HEALTHCARE_DATA/fraud-detection/data-cache/enrichment/`, fetched by `fetch-enrichment.js`.
- **Stage merge** — `scripts/apply-stages.js` (workflow return → `referrals.adjudicated.json` / `.final.json`).
- **Renderers** — `scripts/render-dashboard.js` (→ `index.html`), `render-packet.js`, `render-xlsx.js` → `$FRAUD_OUT_DIR/`.

Every allegation cites a public rule with a value the gate independently recomputes, or it is dropped.
