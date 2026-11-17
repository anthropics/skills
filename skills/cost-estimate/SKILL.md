---
name: cost-estimate
description: Estimates what a codebase would have cost to build with a traditional human team — the replacement cost to rebuild, not market value. Use when the user asks "how much did this cost?", "what's the ROI of Claude/Copilot on this repo?", "how long would a human team have taken?", or mentions COCOMO, LOCOMO, Function Points, LOC analysis, or codebase cost. Produces P10/P50/P90 ranges with a four-way cross-check (bottom-up × COCOMO II × Function Points × LOCOMO), real Claude-session token costs, market-rate research, org overhead, and a machine-readable artifact.
---

# Cost Estimate Skill

You are a senior software engineering consultant producing a defensible cost estimate for the current codebase.

## Philosophy (read first, do not skip)

**This skill estimates "replacement cost to rebuild"** — what it would cost a traditional human team to recreate this codebase from scratch today, starting from specs that already exist. It is **NOT** market value. It is **NOT** a quote. It does **NOT** capture discovery time, failed experiments, PMF iteration, institutional knowledge, or the customer-support feedback loop that shaped what's in the code.

Say this explicitly in the report — in the TL;DR, not buried. Readers (especially non-technical ones) will mistake the number for "what this codebase is worth," and the difference between those two things can be an order of magnitude in either direction.

## Core invariants (read and internalize)

1. **LOC is a proxy.** Ten lines of dense regex ≠ ten lines of boilerplate. Cross-validate with process signals (git history) and top-down models (COCOMO II, Function Points, LOCOMO).
2. **Exclude anything humans didn't write.** Generated code, vendored deps, minified bundles, lockfiles, binary blobs — filter before counting.
3. **Every number gets a range.** P10 (optimistic) / P50 (median) / P90 (pessimistic). Single-point estimates misrepresent confidence.
4. **Two kinds of signals.** *Code signals* = LOC + complexity + quality. *Process signals* = commits, contributors, duration, churn. Use both; when they disagree, investigate.
5. **Don't double-count.** A well-tested codebase earns a quality bump *or* a smaller integration-test overhead — not both.
6. **Compound overheads.** Architecture, debugging, review, docs multiply sequentially on base coding time — they don't sum.
7. **Size-aware.** Micro projects (<500 LOC) don't need 10-page reports. Macro projects (>500k LOC) need monorepo decomposition.
8. **State your limits.** Every report lists what's counted, what's excluded, what's fragile, and what the reader should spot-check.

If you catch yourself writing a single dollar figure without a range, stop and add one. If you find yourself reporting four significant figures of precision, drop to two — overly precise numbers signal false confidence.

## Bundled resources (progressive disclosure)

Read or execute these on demand — don't pre-load everything.

**Scripts** (execute, don't read as code):
- `scripts/resolve_outdir.py` — derives the platform-appropriate temp dir for artifacts
- `scripts/count_loc.sh` — LOC count via cloc/tokei/scc with graceful find+wc fallback
- `scripts/compute_dryness.py` — DRYness (ULOC/LOC) via scc
- `scripts/git_signals.sh` — duration, commits, contributors, churn
- `scripts/claude_token_cost.py` — ground-truth token usage + equivalent API cost from session logs
- `scripts/git_session_clustering.py` — fallback Claude-hour estimate when session logs are absent

**References** (read when the step runs):
- `references/category-rates.md` — category LOC/hr table + quality-signal scoring (Steps 1, 3)
- `references/cocomo-ii.md` — top-down COCOMO II (Step 4)
- `references/function-points.md` — QSM backfiring table (Step 4a)
- `references/locomo.md` — LLM-regeneration counterfactual (Step 4b)
- `references/overhead-multipliers.md` — Step 5 formula
- `references/market-rates.md` — Step 6 query templates + fallback anchors
- `references/team-cost.md` — org overhead + team composition (Steps 7, 8)
- `references/claude-roi.md` — session-aware ROI methodology (Step 9)
- `references/cross-validation.md` — sensitivity + Harvard + Capers Jones (Step 10)

**Assets** (used verbatim for output):
- `assets/report-template.md` — copy into the generated Markdown report (Step 11)
- `assets/artifact-schema.json` — shape of the JSON artifact (Step 12)

---

## Workflow — 12 steps

Copy this checklist and check items off as you complete them:

```
- [ ] Step 0:  Pick a strategy (size-aware)
- [ ] Step 1:  Measure the codebase (LOC, quality, stack)
- [ ] Step 2:  Gather process signals (git)
- [ ] Step 3:  Categorize & compute base hours (P10 / P50 / P90)
- [ ] Step 4:  Cross-check (COCOMO II + Function Points + LOCOMO)
- [ ] Step 5:  Apply overhead multipliers
- [ ] Step 6:  Research market rates
- [ ] Step 7:  Convert to calendar time
- [ ] Step 8:  Compute full-team cost
- [ ] Step 9:  Compute Claude ROI
- [ ] Step 10: Sensitivity + cross-validation
- [ ] Step 11: Generate the report
- [ ] Step 12: Write artifacts to temp dir + print to terminal
```

---

## Step 0: Pick a strategy (size-aware)

Run a size sniff:

```bash
bash .claude/skills/cost-estimate/scripts/count_loc.sh
```

| Project size | Strategy | Report shape |
|---|---|---|
| **Micro** (<500 LOC) | Nominal estimate only | One paragraph + one line item. Skip Steps 4 (full cross-check), 8 (full team), 10 (sensitivity). Output: "~X days of senior dev work; ~$Y-Z at typical rates; confidence: low." |
| **Small** (500 – 10k LOC) | Full methodology, short report | Keep all steps; drop Step 8 role-by-role table (keep stage totals only); single-sentence sensitivity. |
| **Normal** (10k – 500k LOC) | Full skill, full report | All steps, all tables. Default. |
| **Macro** (>500k LOC) | Decompose first | Break by top-level directory/service; run the full skill per subsystem; sum and report per-subsystem + aggregate. Don't categorize 500k lines in one pass. |

State which strategy you chose and why at the top of the report.

---

## Step 1: Measure the codebase (code signals)

### 1a. Count LOC

```bash
bash .claude/skills/cost-estimate/scripts/count_loc.sh
```

The script tries `cloc` → `tokei` → `scc` → `find+wc`, each with proper exclusions. Emits a single integer.

### 1b. DRYness / ULOC (copy-paste deflator)

```bash
python3 .claude/skills/cost-estimate/scripts/compute_dryness.py
```

Apply a deflator to base hours (only if DRYness is known):

```
dryness_deflator = 1 − (1 − DRYness) × 0.5       # 1.0 → no change; 0.6 → 0.80×
```

If DRYness can't be computed (no `scc`), skip — don't invent a number. Note it in the report.

### 1c. Explicit exclusions (do NOT count)

Report these separately as "excluded LOC" for transparency: vendored deps (`node_modules/`, `vendor/`, `.venv/`, `third_party/`, `target/`, `dist/`, `build/`); generated code (`*.pb.go`, `*_pb2.py`, `*.g.dart`, `*.freezed.dart`, `*_generated.*`, OpenAPI clients, Prisma client, GraphQL types; headers like `// Code generated by …`, `@generated`, `DO NOT EDIT`); minified / bundles (`*.min.js`, `*.min.css`, sourcemaps, webpack chunks); lockfiles (`package-lock.json`, `yarn.lock`, `Cargo.lock`, `poetry.lock`, `go.sum`, `Gemfile.lock`); binary / assets (images, fonts, PDFs, videos, `*.wasm`); framework auto-migrations.

### 1d. Detect quality signals

See `references/category-rates.md` section 1 for the per-signal scoring table. Compute `quality_multiplier` in the range 0.7 – 1.3 (max ±30%).

### 1e. Detect the stack

Examine: `package.json`, `Cargo.toml`, `go.mod`, `pyproject.toml`, `Gemfile`, `pom.xml`, `build.gradle`, `Dockerfile`, `docker-compose.yml`, `.github/workflows/`, `terraform/`, `k8s/`, framework configs. Output a one-paragraph stack summary before moving on.

---

## Step 2: Gather process signals (git)

```bash
bash .claude/skills/cost-estimate/scripts/git_signals.sh
```

Emits `first=… last=… duration_days=… commits=… contributors=… adds=… dels=… net=… churn_ratio=…` on one line.

### What the signals mean

| Signal | Interpretation |
|---|---|
| `churn_ratio` > 2.0 | Heavy rework — add 15% to Total hours to reflect iteration cost the LOC count misses |
| `contributor_count` ≥ 3 | Real team; coordination overhead already implicit — don't inflate further |
| `commit_count` < 10 with >5k LOC | Likely a one-shot import; LOC may overstate bespoke work |
| `project_duration_days` short vs LOC | Heavy AI/automation assist — flag for ROI step |

### AI-authored detector

```
loc_per_day = net_adds / max(project_duration_days, 1)
```

| `loc_per_day` | Interpretation | Effect on report |
|---|---|---|
| < 100 | Normal human pace | No flag |
| 100 – 500 | Productive / small team | No flag |
| 500 – 2000 | Likely AI-assisted | Flag: "human-cost is a counterfactual, not elapsed time" |
| 2000+ | Clearly AI-assisted / one-shot import | Flag strongly; Claude ROI leads the report |

**When AI-authored**, bottom-up / COCOMO / FP numbers are *hypothetical human rebuild costs*, not what the project took in calendar time. The report must say: *"This codebase was built in [X] calendar days with AI assistance. The $[Y] figure is what a human team *would* cost to rebuild it from scratch — the actual cost-to-build was a fraction."*

### Process-signal bounds check

```
process_hours ≈ commit_count × avg_commit_hours    # 0.5 (small) to 3.0 (large rewrites)
```

Use only as a bounds check: if your Step 4 total is <0.3× or >3× the process estimate, something is off (likely misclassification or excluded/generated code leaked in).

---

## Step 3: Categorize & calculate base hours (with ranges)

Read `references/category-rates.md` for the full rate table (15 categories, Low/Mid/High LOC-per-hour) and the formula mapping LOC → P10/P50/P90 hours.

Sum across categories → **Base Coding Hours (P10 / P50 / P90)**.

**Per-feature breakdown**: for any top-level directory with > 5% of counted LOC, also report a sub-estimate ("what did `src/checkout/` cost?"). See the reference for the shell one-liner and table format.

**Scoped mode** (`--since <commit>` or `--path <dir>`): restrict Steps 1-3 to that slice; keep every other step. See the reference.

When reporting, show which files/directories fell into each category so the reader can audit the classification.

---

## Step 4: Cross-checks (three independent sanity checks)

### 4a. COCOMO II

Read `references/cocomo-ii.md` — contains the `A × KSLOC^E × EAF` formula, the 5-bucket EAF lookup, and the divergence rules vs bottom-up.

**Divergence rule**: if bottom-up vs COCOMO diverges by >2×, **stop and investigate** before reporting. Likely causes: wrong category weighting, generated code leaked in, wrong E/EAF.

### 4b. Function Point backfiring

Read `references/function-points.md` — QSM language conversion table + hours-per-FP by domain. Gives a fourth independent number.

### 4c. LOCOMO (LLM-regeneration counterfactual)

Read `references/locomo.md` — answers "what would it cost an LLM to re-generate this code today?". The ratio `COCOMO_cost / LOCOMO_cost` is the human premium; flag it in Step 9.

Report COCOMO, bottom-up, and LOCOMO side-by-side in a single table. Never publish LOCOMO alone.

---

## Step 5: Overhead multipliers (compounding, no double-count)

Read `references/overhead-multipliers.md` for the exact formula. Key points:

- Multiplicative, not additive.
- If a quality signal already bumped per-LOC value in Step 1d, **use the low end** of the related overhead (tests, docs, CI) — don't double-count.
- Stacked overhead (before `quality_multiplier`) typically falls **1.8× – 2.6×** of base. Outside that range → investigate.

Apply to P10/P50/P90 each → **Total Engineering Hours (P10 / P50 / P90)**.

---

## Step 6: Market rates

Read `references/market-rates.md` for the WebSearch query templates and the fallback anchor table. Use WebSearch for current rates. Collect 3 – 5 data points across regions (global remote / US remote / SF/NYC / specialist).

Pick a **Recommended Rate** with one sentence of justification. If WebSearch is unavailable, use the anchor table and explicitly flag "rates from skill defaults, not live search".

---

## Step 7: Organizational overhead → calendar time

Read `references/team-cost.md` — covers coding-efficiency by company stage (solo / lean / growth / enterprise / bureaucracy) and the calendar-months formula. Report across all five company types.

---

## Step 8: Full team cost

Same reference (`references/team-cost.md`) — role ratios, rates, and stage multipliers (1.0× solo / 1.45× lean / 2.2× growth / 2.65× enterprise). Compute full-team cost at engineering P50 for each stage.

---

## Step 9: Claude ROI (session-aware, churn-aware, reviewer-aware, concurrency-aware)

The headline: *"What did each hour of Claude's actual clock time produce — and what did the user pay in time + money?"*

### 9a. Measure token usage + active hours + parallel windows

**Preferred — session logs (high confidence)**:

```bash
python3 .claude/skills/cost-estimate/scripts/claude_token_cost.py
```

Returns ground-truth tokens + equivalent API cost AND session-timing stats: `active_hours_capped6` (Claude compute throughput — additive across overlapping sessions), `operator_hours_union` (wall-clock time the user actually sat at the keyboard), `peak_concurrent_sessions`, and `avg_concurrency`. Flag `method: "session_logs"` and `api_cost_source: "session_logs"`.

**Fallback — git session clustering (medium confidence, ±2×)**:

```bash
python3 .claude/skills/cost-estimate/scripts/git_session_clustering.py
```

No concurrency signal available in this mode.

**Final fallback — LOC heuristic (low confidence)**: `net_claude_loc / 350 hrs`.

### 9b. Compute headline metrics

Read `references/claude-roi.md` for the full formulas. Two speed multipliers — report both:

- `speed_multiplier_compute = total_eng_hours_p50 / active_hours_capped6` — AI throughput
- `speed_multiplier_operator = total_eng_hours_p50 / operator_hours_union` — honest ROI metric (= compute multiplier × avg_concurrency)

**Reviewer-time rule** (non-optional): tune `reviewer_ratio` on peak concurrency — 0.5 for single-window, 0.2-0.3 for parallel (the operator IS the reviewer-in-loop), 0.1 for high-concurrency orchestration. Omitting reviewer time overstates ROI; using the wrong ratio under-counts it.

Two DIFFERENT cost numbers — never add them together:
- `equivalent_api_spend` = counterfactual per-token bill
- `actual_cash_paid` = Max ($200/mo × months) | Pro ($20/mo × months) | API (the bill itself)

### 9c. Speed-multiplier sanity check — evidence-based anchors

Compare the **per-developer-equivalent multiplier** (`speed_multiplier_operator / overhead_multiplier`) against published benchmarks — see `references/claude-roi.md` section 3 for anchors and the full gate:

- GitHub Copilot SPACE 2024: 1.55× (solo autocomplete)
- METR Feb 2026 transcript study (n=7): range **2.1 – 11.6×** at concurrency 1.05 – 2.32; top user 11.6× at 2.32 avg
- Anthropic C compiler (Carlini, solo + 16 async): existence proof, not a per-hour rate

Gate: `per_dev_equivalent > 25×` = implausible; `> 12×` = suspicious (above METR ceiling); else plausible. For async swarm mode (peak ≥ 10), report as "no_benchmark" — Carlini is the only public anchor and isn't a per-hour rate.

### 9d. Parallel Execution Profile paragraph — REQUIRED when `peak_concurrent >= 2`

Copy the template from `assets/report-template.md` (the *Parallel Execution Profile* block). Fill in peak, avg concurrency, operator/compute hours, operator-hour multiplier, per-developer-equivalent multiplier, and the contextual sentence placing the user relative to METR's observed band.

**Never invent tiers.** The only tiers in the report are the ones traceable to cited studies (METR, Copilot SPACE, Carlini). If the user's per-dev-equivalent exceeds METR's 11.6× ceiling, the paragraph must say so plainly and offer the two honest explanations (codebase shape inflates rebuild estimate; n=7 sample is small), not dress it up as "top-percentile expert".

### 9e. State limitations loudly

Always include: *"Claude active hours from [method]. Reviewer time assumed at [ratio]× operator hours (tuned for [peak] parallel windows). Operator-hour speed multiplier is the honest ROI number; compute-hour multiplier benchmarks AI throughput."*

---

## Step 10: Sensitivity & cross-validation

Read `references/cross-validation.md` for:

- **Sensitivity**: vary each input one bucket; report top-3 drivers by `p50_impact_usd`.
- **Harvard supply-side anchor** (Hoffmann-Nagle-Zhou 2024): expected `p50 / (LOC × $0.15) ≈ 3.5×`. Flag outliers.
- **Capers Jones 5-year TCO**: `build_cost × (1 + 0.20 × 5) = build_cost × 2.0`. Reframe: "build is ~40-50% of lifetime cost."
- **Three-way cross-check rules**: high confidence only if 3 signals agree within 30%; two-signal mode never reports "high".

---

## Step 11: Generate the report

Copy `assets/report-template.md` verbatim as the structure for your Markdown report. Fill in every `[N]` / `[X]` / `[date]` placeholder. Lead with TL;DR; put spot-checks and assumptions close to the end. **Preserve the credit footer** in the saved file — but strip it from the terminal print (see Step 12).

Keep to the two-sig-figs rule on dollar amounts. Show which files fell into each category so the reader can audit.

---

## Step 12: Write artifacts to a temp directory (never the repo)

**Never write output files into the user's working directory.** Someone could `git add .` and commit them by accident — reports contain sensitive numbers (rates, Claude costs, team composition) that don't belong in git history.

### Derive $OUTDIR

```bash
OUTDIR=$(python3 .claude/skills/cost-estimate/scripts/resolve_outdir.py)
echo "$OUTDIR"
```

Typical paths:
- Linux → `/tmp/cost-estimate/<project>/`
- macOS → `/var/folders/.../T/cost-estimate/<project>/`
- Windows → `%TEMP%\cost-estimate\<project>\`

### Write two files to $OUTDIR

- `$OUTDIR/cost-estimate-report.md` — the full Markdown report from Step 11 (credit footer included)
- `$OUTDIR/cost-estimate.json` — the machine-readable artifact; see `assets/artifact-schema.json` for the exact shape. `low_confidence_fields` is a list of JSON paths (e.g. `["claude_roi.reviewer_hours", "rates.recommended_usd_per_hour"]`) that downstream consumers should display with a warning icon.

**⚠ BOTH files go to `$OUTDIR`. Never write `./cost-estimate.json` or `./cost-estimate-report.md`.** Use the Write tool with the absolute path `$OUTDIR/...`. If the user explicitly asks for output in the current directory ("write it here"), honor the request but show the *"not written to the working directory"* note without it — the default is always the temp dir.

### Print to terminal

Print the full Markdown report to stdout so the user sees it without opening any file — **but strip the credit footer** (the "generated with the `/cost-estimate` skill, created by Julien Barbier…" block). The footer belongs only in the saved file and the JSON artifact, not in the terminal echo. After printing, end with a one-line pointer:

> *Report also saved to `$OUTDIR/cost-estimate-report.md` and `$OUTDIR/cost-estimate.json`. Not written to the current directory (safer — won't accidentally land in a commit).*

---

## Notes to self

- **Show your math.** Every number in the report must be traceable to a LOC count and a rate.
- **Never publish a single dollar figure without its range.**
- **Two-sig-figs rule**: round to two significant figures unless you can defend more.
- **Degrade gracefully.** Missing git? Note it, lower confidence, continue. Missing WebSearch? Use skill defaults, note it. Missing `scc`? Skip DRYness, note it.
- **Decompose macros.** For monorepos, estimate each service separately and sum.
- **Don't double-count.** Quality bonuses and overhead reductions live on the same axis — pick one or split them.
- **Reviewer-time is non-optional** in Step 9; omitting it lies about Claude ROI.
- **Frame AI-authored projects as counterfactuals**, not elapsed spend — the distinction matters to readers.
