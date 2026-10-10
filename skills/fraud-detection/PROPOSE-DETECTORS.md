# Propose new detectors — close the loop

Run after a sweep to mine patterns the 22 detectors don't cover. Produces TWO kinds of proposal:

- **Deterministic detector** — a `scripts/dNN-*.js` stub when the pattern is a SQL join + threshold
  against a citable reference table. Goes through a false-positive gate before it's worth review.
- **Adjudicate-time check** — a markdown file in `$CLAUDE_HEALTHCARE_DATA/fraud-detection/checks/`
  when the pattern needs judgment but recurs enough to codify. The adjudicate/synthesize prompts
  read this directory, so checks accumulate per payer without code changes.

## Run

After step 5 of SKILL.md (you have `$FRAUD_OUT_DIR/referrals.final.json`), call the Workflow tool:
- scriptPath: `${CLAUDE_PLUGIN_ROOT}/skills/fraud-detection/workflows/propose-detectors.js`
- args: `{ corpusDb, quarter, lob, pluginRoot, dataRoot, outDir: $FRAUD_OUT_DIR }`

Write the return to `$FRAUD_OUT_DIR/proposed-detectors.md` and surface it to the user.

## Scrutiny gates (why most candidates won't make it)

A candidate becomes a **deterministic detector** proposal only if it passes ALL of:
1. **Determinism** — expressible as a SQL predicate over corpus + reference tables (no LLM needed to fire)
2. **Citation** — names a public rule/table the finding traces to (NCCI, CFR, state policy, fee schedule)
3. **False-positive sweep** — predicate run against the corpus's clean claims; ≥1 hit → reject
4. **Non-duplication** — not already covered by D1-D22 (check `scripts/dNN-*.js` headers)
5. **Reference availability** — the cited table is in reference.duckdb OR REFERENCE-DATA.md says where to fetch it

Anything that fails gate 1 or 2 but is a real recurring pattern becomes an **adjudicate-time check** instead.

## Output

`$FRAUD_OUT_DIR/proposed-detectors.md`:
- Per deterministic proposal: id (next free dNN), scheme name, the SQL predicate, citation, exposure
  formula, FP-sweep result, a stub `dNN-*.js` body, why D1-D22 don't cover it
- Per adjudicate-check: the pattern, which existing detector it sharpens (D2/D4/D7/D13), the check
  text to write to `checks/<slug>.md`

Human reviews and merges. Nothing auto-commits.
