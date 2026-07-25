# Benchmark Report Pattern (v3.3.5+)

**Status**: v3.3.5 — hub doc for benchmark disclosure schema  
**Schema**: `shared/benchmark_report.schema.json`  
**Validator**: `scripts/check_benchmark_report.py`  
**Template**: `examples/benchmark_report_template.json`

---

## Why this exists

The Anthropic automated-w2s-researcher (2026) paper headlined a performance comparison:
"2 researchers × 7 days (PGR=0.23) vs 9 agents × 5 days (PGR=0.97)."

Dramatic. Also: n=2, author-conducted, no independence, self-scored. Not a scientific
comparison — a presentation artifact. The authors knew what the agent would produce before
sitting down to do the human baseline; their "7 days" is implicitly benchmarked against
their own foreknowledge. Unaware external researchers doing the same task cold would
likely score higher. The gap may partly be a sandbagged human baseline.

ARS inherits this risk the moment a user publishes an "ARS beats manual" claim. This
pattern defines a mandatory schema for anyone publishing an ARS benchmark comparison.
Reports that don't satisfy the schema aren't "ARS benchmarks" — they're anecdotes.

---

## The schema at a glance

Six required top-level fields in `benchmark_report.schema.json`:

- **`ars_version`** — exact semver the benchmark ran against; ties results to a specific
  skill version so readers can check whether that version is still current.
- **`task_definition`** — description, task_type (outcome-gradable or open-ended), and
  outcome_gradable flag; distinguishes rubric-scored tasks from genuinely open-ended ones.
- **`human_baseline`** — the five provenance fields that determine whether the human side
  of the comparison is credible (see field-by-field rationale below).
- **`ars_run`** — cost, time, skills used, and declared data access level; lets readers
  check the "agents are cheap" or "agents are fast" claims against concrete numbers.
- **`metrics`** — primary metric name, numeric value, and scoring independence; forces
  explicit disclosure of who scored the outputs.
- **`caveats`** — non-empty array of known limitations; at least one honest statement is
  required by schema enforcement.

---

## Field-by-field rationale

### `human_baseline`

This block exists because the human side of a comparison is where benchmark credibility
lives or dies. A weak human baseline inflates an agent's apparent advantage.

- **`sample_size`** (integer, minimum 1): Schema rejects zero, forces an explicit number.
  n=1 or n=2 get a validator warning rather than a hard failure — some tasks are
  expert-bounded — but the number must be stated. Silence is worse than admitting n=1.

- **`author_independence`** (enum: author-conducted | author-blinded | third-party-conducted):
  `author-conducted` is the "2 authors did it themselves" trap: allowed, but the schema
  flags the downward-bias risk. Authors know what a good ARS output looks like; their
  human effort is calibrated against that prior. `author-blinded` (authors worked without
  seeing ARS outputs first) is better. `third-party-conducted` eliminates experimenter
  bias entirely.

- **`hours_spent`** (number, minimum 0): Lets third parties sanity-check the time claim.
  "7 days" reads differently against 20 papers versus 400.

- **`recruitment`** (non-empty string): One sentence forces self-description of selection
  bias. "Authors," "hired on Upwork," "convenience sample" are all honest. Blank is not
  permitted.

- **`tools_allowed`** (array of strings): "No tools" vs "ChatGPT allowed" is not the same
  comparison as ARS. If the human baseline used no AI assistance while ARS ran full
  pipeline, the comparison is testing infrastructure access, not cognitive quality.

### `ars_run`

- **`cost_usd`** (number, minimum 0): A run costing $500 in API tokens is not "cheap"
  just because it took 3 hours. Hours and cost together are needed for a fair comparison.

- **`data_access_level_declared`** (enum: raw | redacted | verified_only): If ARS ran
  on `raw` data while the human baseline used redacted data, the benchmark is testing
  data privilege, not skill. Cross-references ground-truth isolation from v3.3.2.

- **`skills_used`** (array, minItems 1): A benchmark running `academic-pipeline`
  full-mode is not comparable to one running only `deep-research`. Both are ARS;
  they're different scope claims.

### `metrics.scoring_independence`

Four enum values: `authors-scored`, `third-party-scored`, `blind-scored`, `self-scored`.

`self-scored` parses and exits 0, but the validator emits a warning to stderr. Self-scoring
is the worst-case alignment failure: the same agents that produced the output are being
asked whether the output is good. `blind-scored` (human raters without knowledge of which
output came from ARS versus human baseline) is the minimum credible standard for any
claim that will be shared publicly.

### `caveats`

Non-empty array, items non-empty strings, minItems 1. The schema physically prevents an
empty caveats field. A benchmark report with no caveats either has no known limitations
(implausible for any real-world evaluation) or the author didn't think about limitations
(which disqualifies the report more than any specific limitation would).

The caveats field is where sample size warnings, scorer bias, task-selection bias, and
tool-access asymmetries should land when they don't rise to schema errors. It is the
honest disclosure box.

---

## How to use

1. Copy `examples/benchmark_report_template.json` to your benchmark directory.
2. Fill every `FILL IN:` field with real values.
3. Set `human_baseline.sample_size` to the actual number (schema rejects 0).
4. Run: `python scripts/check_benchmark_report.py your-report.json`
5. Fix all `ERROR:` lines (schema violations, exit 1).
6. Read the `WARNING:` lines (stderr, exit 0). Either address them in your methodology or
   document them explicitly in the `caveats` array.
7. Publish the JSON file in your repository alongside the benchmark write-up. The
   machine-readable format lets future scripts cross-check version-specific claims.

---

## What this pattern is NOT

- **Not a quality gate for your methodology.** A report can be schema-valid and still be
  methodologically weak. The schema forces disclosure; it does not evaluate task choice,
  rubric validity, or baseline skill. Compliance is necessary but not sufficient.

- **Not a way to launder self-scored or n=2 comparisons.** `self-scored` and
  `sample_size: 2` produce a valid document. The warnings are loud. Schema compliance
  means the claim is honest about its weaknesses — not that the claim is strong.

- **Not a substitute for peer review.** The schema is the minimum bar for internal
  credibility. Peer review catches confounded variables, cherry-picked tasks, post-hoc
  metric selection — problems the schema cannot see.

- **Not frozen.** A benchmark declaring `ars_version: 3.3.5` is always checked against
  the v3.3.5 schema. Future versions may add fields without invalidating existing reports.

---

## Honesty red lines

These are behaviors the schema is specifically designed to make visible. They are not
prohibited — the schema accepts all of them — but they will appear in validator output
or be apparent to any reader of the JSON.

- **Omitting sample size.** The field is required. There is no valid ARS benchmark report
  without a stated `human_baseline.sample_size`. n=1 is worse than n=10, but it is
  infinitely better than unstated.

- **Author-conducted with no caveat disclosure.** Using `author-conducted` is allowed.
  Not noting it in `caveats` as a limitation is an editorial failure, not a schema
  failure — but reviewers will notice.

- **Self-scoring with no warning acknowledgment.** `self-scored` produces a warning on
  every validator run. If you publish a report with `self-scored` and don't address it
  in caveats, the omission is visible in the JSON to anyone who checks.

- **Empty or single-word caveats.** The schema requires `minLength: 1` per item and
  `minItems: 1` for the array. A caveat of `"none"` is technically valid but signals
  that the author did not engage seriously with limitations.

- **Claiming ARS advantage without disclosing cost_usd.** The field is required. A claim
  that "ARS completed this in 4 hours vs 40 human hours" without a dollar figure omits
  the dimension where the trade-off may be reversed.

---

## Future evolution

Per-skill benchmark templates (a `deep-research`-specific template, an
`academic-paper-reviewer`-specific template) are likely as v3.4 adds domain-specific
evaluation protocols. The `cost_usd` field may split into `cost_usd_api` and
`cost_usd_compute` once cloud execution costs become a factor. The
`data_access_level_declared` enum may expand to match the v3.4 ground-truth tier
vocabulary if that spec evolves. None of these changes will break existing v3.3.5
reports, which remain valid against the version they declared in `ars_version`.
