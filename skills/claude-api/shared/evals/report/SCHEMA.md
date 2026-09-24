# Hillclimb state schema (v2)

`state.json` is the single handoff between an **adapter** (which reads
whatever your run directory looks like) and the **renderer** (which
produces `report.html`). Every field below is optional unless marked
**required** - the renderer shows what is present and hides what is
absent, so a minimal state with just `metrics`, `variants` and
`examples` renders fine, and a maximal one with reps, splits, judge
explanations, attachments and CIs renders all of those too.

Dialect: JSON. Arrays preserve order. Field names are `snake_case`.

> **Built-in adapter tolerance.** `adapter.load()` is forgiving about
> the on-disk input: in `results.jsonl` the case id may be spelled
> `prompt_id`, `id`, or `case_id`; if `_state.json` omits `metrics`
> they are inferred from the union of `grade` keys. The schema below
> is what the adapter *produces*, not what it requires.

## Top level

```ts
{
  schema: "hillclimb/v2",

  source?: {                      // provenance - shown as a grey header bar
    path:         string,         // relative path of the data dir
    n_files:      number,
    content_sha:  string,         // sha256 over sorted (relpath, file-sha) pairs
    generated_at: string,         // ISO 8601
  },

  metrics: Metric[],              // REQUIRED - what each example is graded on
  perf_fields?: PerfField[],      // runtime fields to surface (default set below)

  variants: Variant[],            // REQUIRED - baseline first
  examples: Example[],            // REQUIRED - every row in the eval set
  metrics_md?: string,            // free-text rubric (markdown)

  // The next three are stderr/--check only: load() returns them in memory for
  // build-report.mjs to print, but they are NOT written to state.json or
  // report.html (they can carry absolute paths and fs error text).
  warnings?: string[],            // adapter diagnostics - stderr under --check
  errors?:   string[],            // only; build-report strips all three before
  trace_stats?: object[],         // writing state.json / report.html

  strtab?: { [key]: string },     // report.html embed only (never state.json):
                                  // strings >=1 KB that repeat across transcripts
                                  // are stored once here and referenced as
                                  // "\u0001S:<key>"; hc-adapt.js resolves them at
                                  // load. Tool payloads >24 KB are also clipped
                                  // in the embed with a pointer to the trace file.

  summary?: {
    narrative?:   string,         // markdown - model-authored running exec
                                  // summary; rewritten after every round,
                                  // finalized as the 4-part summary in Step 5
    best_variant?: string,        // variant id
    headline_metric?: string,     // metric id that test/val/train below
                                  // were computed over; titles the
                                  // score-by-split chart
    test?:  SplitScore,           // headline - shown with CI bars
    val?:   SplitScore,
    train?: SplitScore,
  },
}
```

## `Metric`

```ts
{
  id:     string,                 // REQUIRED - key used in scores{}
  label?: string,                 // defaults to id; keep <=14 chars - the
                                  // legend has limited width and truncates
                                  // with an ellipsis
  kind:   "binary" | "float" | "judge",
                                  // binary -> % (n/N);  float -> mean±sd;
                                  // judge -> float score with per-rep `explanation`
  scale?: number,                 // upper bound of the raw score range;
                                  // default: 1 for binary, 10 for float/judge.
                                  // Set explicitly for anything else (e.g. 5, 100).
  better?: "higher" | "lower",    // default "higher"; drives delta colouring
}
```

## `PerfField`

```ts
{ id: string, label?: string, unit?: string }
```

If `perf_fields` is absent the renderer uses the default set:
`cost_usd`, `in_tokens`, `out_tokens`, `web_searches`, `tool_calls`,
`latency_s`. The built-in adapter passes `perf_fields` (and
`metrics`) through from `.claude/hillclimb/<flow>/_state.json` when
present, so writing that file is how you override the columns
without writing a custom adapter.

## `Variant`

```ts
{
  id:      string,                // REQUIRED - "baseline", "v1", ...
  label?:  string,
  description?: string,
  target?: "system_prompt" | "skill" | "tools" | "code",
  change_rationale?: string,      // markdown - rendered above the diffs
  diffs?: {
    incremental: [{ rel_path: string, unified_diff: string }],  // vN vs vN-1 (change.patch)
    cumulative:  [{ rel_path: string, unified_diff: string }],  // vN vs baseline (recomputed from snapshots)
  },
  model?: string | string[],      // distinct row.model values; "mixed" chip if >1
  suspicious?: { note: string },  // renderer shows a WARNING badge + tooltip
  errors?: { total: number, by_class: { [cls]: number }, truncated: number },
                                  // failed attempts from errors.jsonl + status:truncated rows;
                                  // shown as a "WARNING N not scored" badge, never in the means
  metrics?: { [metric_id]: number },
                                  // summary-only metrics ONLY - metrics that
                                  // appear in examples[].results are ignored
                                  // here (the UI derives those from the rows)
  paired?: { [split]: { [metric_id]: PairedDelta } },
                                  // paired per-case delta vs baseline, per
                                  // criterion. The renderer uses .significant
                                  // to gate cell heat-tinting (within-noise ->
                                  // neutral); the numbers stay here for audit.
}
```

The first variant is treated as the baseline. `summary.best_variant`
names the winner; if absent, the last variant is assumed.

## `PairedDelta`

```ts
{
  mean:  number,                  // mean of per-case (variant_mean - ref_mean)
  ci_lo: number, ci_hi: number,   // Wald CI over per-case deltas
  n:     number,                  // cases present in BOTH variants
  significant: boolean,           // CI excludes zero
}
```

A paired comparison: for each case present in both variants, take the
mean across that variant's reps minus the mean across the reference's
reps, then a CI over those per-case deltas. More powerful than
comparing two `SplitScore` CIs because between-case variance cancels - 
two variants' unpaired CIs can overlap while the paired delta is
clearly non-zero.

## `Example`

```ts
{
  id:       string,               // REQUIRED
  prompt:   string,               // REQUIRED
  split?:   "train" | "val" | "test",
  tags?:    string[],             // ORDERED - tags[0] is the primary
                                  // grouping key the UI clusters rows by
                                  // (replaces v1's singular `category`);
                                  // further entries are secondary filters
  meta?:    { [k]: any },         // arbitrary sidecar data
  attachments?: Attachment[],     // input artifacts - render above the first
                                  // user turn in the transcript view
  results: { [variant_id]: RepResult[] },   // REQUIRED (may be empty per variant)
}
```

## `Attachment`

```ts
{
  kind?: "image" | "svg" | "html" | "pdf" | "json" | "text" | "code"
       | "file" | "url",          // inferred from ref if omitted
  ref:  string,                   // path relative to the flow root, data: URI,
                                  // or URL. Paths under 2 MB are inlined as
                                  // data: at build time; larger -> download chip.
  alt?: string,
}
```

`image`/`svg` render inline; `html` in a sandboxed scrollable iframe; `pdf`
via the browser's native viewer in a scrollable embed; `json`/`text`/`code`
in a `<pre>`; `file` (docx/pptx/anything else) and `url` as a download/open
chip. Every kind has a Hide/Show toggle.

## `RepResult`

```ts
{
  rep?:        number,            // 0-based; default = array index
  status?:     string,            // present only when not 'ok' (e.g. 'truncated'); scores is {} then
  scores:      { [metric_id]: number },
  explanation?: { [metric_id]: string },    // judge rationale per metric
  model?:      string,            // model id that produced this rep (from the response)
  perf?:       { [perf_field_id]: number },
  attachment?: string,            // relative path to a per-rep output screenshot
  transcript?: Turn[],
}
```

## `Turn`

```ts
{
  role: "system" | "user" | "assistant" | "tool_call" | "tool_result",
  content:  string,               // markdown for user/assistant/system;
                                  // pretty-printed args/result for tool turns
  name?:    string,               // tool name (tool_call / tool_result)
  thinking?: string,              // assistant extended-thinking (collapsible)
  attachments?: Attachment[],     // artifacts produced/consumed at this turn - 
                                  // render below the turn content. Use this for
                                  // files the model wrote, generated plots, etc.
}
```

On the input side, the built-in adapter reads `traces/<id>.json`
directly as a `Turn[]` list - each tool call / result is its own
`{role: "tool_call", name, content}` / `{role: "tool_result", content}`
entry. See `build-eval.md` §Step 3 for the trace-writing spec.

## `SplitScore`

```ts
{
  score:  number,
  ci_lo?: number,
  ci_hi?: number,
  n?:     number,
  significant?: boolean,          // vs baseline - greys out & badges "within noise" when false
}
```

## Rendering rules

* Every aggregate in the UI is computed from `examples[].results` at
  render time, so the `% (n/N)` shown always matches the rows listed - 
  including under split/tag filters.
* `variants[].metrics` is a fallback for metrics that never appear in
  any example's `scores` (e.g. a `train_score` pulled from
  `summary.json`). If a metric does appear per-row, the per-variant
  `metrics` value is ignored.
* Binary metrics with `reps > 1`: the per-cell display is the
  rep-level pass rate, e.g. `67% (2/3)`. Float metrics: `mean ± sd`.
* A variant's `suspicious.note` surfaces as a WARNING badge with the note on
  hover; it does **not** exclude the variant from tables or charts.

## Writing your own adapter

`adapter.load(path) -> dict` is the only contract. If your data is not
laid out like `.claude/hillclimb/<flow>/`, write a function that reads
whatever you have and returns a dict matching this document, then call
`render.render(state)` directly (see `build-report.mjs` for the
one-liner). The renderer has no opinion about where the data came from.
