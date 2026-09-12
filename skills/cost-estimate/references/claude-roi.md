# Claude ROI — session-aware, churn-aware, reviewer-aware, concurrency-aware (Step 9)

Headline: **"What did each hour of Claude's actual clock time produce — and what did the user pay in time + money?"**

## Contents
1. Measure Claude active hours + operator hours + parallel windows
2. Compute headline metrics
3. Speed-multiplier sanity check — evidence-based, not vibes
4. Parallel Execution Profile paragraph (goes in the report)
5. Loudly stated limitations

---

## 1. Measure Claude active hours + operator hours + parallel windows

### Method 1 (best): Claude Code session logs

Session transcripts live at `~/.claude/projects/<project-hash>/*.jsonl` where the hash is derived from the project path (`/` → `-`).

Run `scripts/claude_token_cost.py` — one script emits **all** of:

- **Token usage + API cost**: ground-truth `input_tokens`, `cache_creation_input_tokens`, `cache_read_input_tokens`, `output_tokens` per message × published per-model rates.
- **`active_hours_capped6`** — sum of `(last - first)` per session file, capped 6h/session. *Claude compute throughput* (adds up even when sessions overlap).
- **`active_hours_uncapped`** — same sum without the cap; used for sanity.
- **`operator_hours_union`** — wall-clock UNION of all session intervals. *Real human driver time* — hours the user actually sat at the keyboard.
- **`peak_concurrent_sessions`** — max simultaneous Claude Code windows.
- **`avg_concurrency`** = `active_hours_uncapped / operator_hours_union`.

Flag `method: "session_logs"` — high confidence.

### Method 2: Git churn + session clustering (fallback, medium confidence, ±2×)
Run `scripts/git_session_clustering.py`. No concurrency signal in this mode.

### Method 3: LOC heuristic (final fallback, low confidence)
`net_claude_loc / 350 hrs`.

---

## 2. Headline metrics

Two denominators, two different stories:

```
# Claude throughput — what the AI produced per compute-hour
speed_multiplier_compute  = total_eng_hours_p50 / active_hours_capped6

# Operator leverage — what one human produced per real keyboard-hour
speed_multiplier_operator = total_eng_hours_p50 / operator_hours_union

# These diverge when the user runs parallel windows:
# speed_multiplier_operator = speed_multiplier_compute × avg_concurrency
```

Report **both**. `speed_multiplier_operator` is the honest ROI number (the one the user's wallet feels); `speed_multiplier_compute` benchmarks AI throughput.

**Per-developer-equivalent multiplier** (for honest comparison with published benchmarks):

```
# The bottom-up P50 includes team overhead (~2.53× above base coding for debug/docs/review/test).
# Published benchmarks measure solo-developer speed, not team-rebuild cost. Divide it out:
per_dev_speed_multiplier = speed_multiplier_operator / overhead_multiplier
```

This is the apples-to-apples number for comparing against METR or Copilot. Report it alongside the headline multiplier.

```
# Reviewer time
reviewer_hours  = operator_hours_union × reviewer_ratio
# reviewer_ratio defaults:
#   single-window interactive: 0.5
#   parallel windows (peak_concurrent >= 2): 0.2 - 0.3
#   async swarm (Carlini-style, peak >= 10, mostly hands-off): 0.05 - 0.1
reviewer_cost   = reviewer_hours × recommended_rate

# Two DIFFERENT numbers — never add them together
equivalent_api_spend = sum(tokens × published_rates)      # counterfactual per-token bill
actual_cash_paid     = Max $200/mo | Pro $20/mo | API = the bill itself

claude_total_cost = actual_cash_paid + reviewer_cost
roi = (total_cost_p50 − claude_total_cost) / claude_total_cost
```

---

## 3. Speed-multiplier sanity check — evidence-based anchors

Two distinct workflows with different ceilings. Classify the user's mode first, **then** apply the right anchors.

### 3a. Interactive parallel (driver at keyboard, spot-reviewing multiple active windows)

This is what most Claude Code users do. The public data:

| Anchor | Speed multiplier | Concurrency | Source |
|---|---|---|---|
| GitHub Copilot SPACE study | 1.55× | 1 (inline autocomplete, keystroke review) | *Measuring GitHub Copilot's Impact on Productivity*, CACM 2024 |
| METR median Claude Code user | 3 – 5× | 1.2 – 1.4 avg | METR 2026 transcript analysis, n=7 |
| METR top Claude Code user | **11.6×** | **2.32 avg** (11.3 hrs/day) | Same study, Technical Staff A |
| METR full observed range | 2.1× – 11.6× | 1.05 – 2.32 avg | Seven Anthropic-adjacent engineers |

Ceiling for interactive parallel: **~12× per-developer-equivalent** — the highest directly-observed number in the public record, per the METR study cited above. Higher numbers usually mean the denominator is wrong (team overhead included, LOC-heavy boilerplate inflating base-coding estimate, sessions uncounted).

### 3b. Async orchestration (set up harness, walk away)

Rare, project-scale workflow. One published data point:

| Anchor | Scale | Source |
|---|---|---|
| Nicholas Carlini / Anthropic C compiler | 1 human, 16 parallel Claudes, ~2,000 sessions, 2 weeks, $20k API, **100k LOC** | *Building a C compiler with a team of parallel Claudes*, anthropic.com/engineering |

Carlini measured in **project-deliverables-per-scaffolding-week**, not per-hour-at-keyboard. His human time was mostly upfront harness design + periodic intervention; he "mostly walked away" between checkpoints. A speed multiplier in conventional units isn't published. Use this as an existence proof ("solo human + well-chosen task + async swarm can produce 100k LOC in 2 weeks"), not as a per-hour benchmark.

### 3c. Gate

```
# Classify mode
if peak_concurrent <= 1:                        mode = "single_window"
elif peak_concurrent <= 4 and avg < 3:          mode = "interactive_parallel"
elif peak_concurrent <= 10 and avg < 5:         mode = "advanced_interactive"
else:                                            mode = "async_swarm"

# For interactive modes, compare per_dev_speed_multiplier to METR's ceiling
if mode in ("single_window", "interactive_parallel", "advanced_interactive"):
    if per_dev_speed_multiplier > 25:    sanity_flag = "implausible"   # 2× above METR top
    elif per_dev_speed_multiplier > 12:  sanity_flag = "suspicious"     # above METR ceiling
    else:                                 sanity_flag = "plausible"

# For async swarm, no apples-to-apples benchmark exists in the public record
elif mode == "async_swarm":
    sanity_flag = "no_benchmark"
    # Report as "Carlini-style async orchestration — no direct public benchmark; compare
    # to his 100k LOC / 2 weeks / 1 human as an existence-proof anchor"
```

When `sanity_flag != "plausible"`, the report must explicitly name the metric to verify (operator_hours, team-overhead denominator, LOC inflation).

---

## 4. Parallel Execution Profile paragraph (goes in the report)

Fill this in whenever `peak_concurrent_sessions >= 2`. Show the user where the evidence places them — don't invent tiers.

> **Parallel Execution Profile.** This project was driven at **[peak]** Claude Code windows concurrently at peak (avg **[avg_concurrency]×** simultaneous), with **[operator_hours_union]** real keyboard hours producing **[active_hours_capped6]** hours of Claude compute work. Mode: **[interactive_parallel / advanced_interactive / async_swarm]**.
>
> **Evidence-based anchors (all measured 2024 – 2026):**
>
> - **GitHub Copilot inline autocomplete (SPACE 2024)**: 1.55× — solo developer, review every suggestion at the keystroke level.
> - **METR Claude Code transcript study (Feb 2026, n=7 Anthropic-adjacent engineers)**: median 3 – 5× at 1.2 – 1.4 avg concurrency; top user 11.6× at 2.32 avg concurrency (working 11.3 hr/day).
> - **Anthropic C-compiler experiment (Carlini, 2026)**: one human + 16 parallel Claudes + 2 weeks = 100k LOC compiler for $20k API — the published "async swarm" anchor. Not directly comparable in per-hour terms; reported as an existence-proof for solo-human + well-scoped parallel task.
>
> This user's **operator-hour multiplier is [X]×** against the full-team rebuild estimate (includes PM/design/QA overhead ~2.53×). The apples-to-apples **per-developer-equivalent multiplier is [X/2.53]×**, which is the number to compare to METR. At [avg_concurrency]× concurrency, METR's observed range is roughly [interpolated from the 1.05–2.32 band above]; this user's per-dev-equivalent sits **[inside / above / well above]** that range.
>
> Caveats: METR measured time-to-complete identical tasks; this skill measures hypothetical-rebuild-cost vs actual session time. The numerators are different, and LOC-dense codebases (scrapers, boilerplate, generated-style code) inflate the multiplier above what METR observes for complex novel work. Don't quote either multiplier as universal.

---

## 5. Limitations (state loudly in the report)

Always include:

> "Claude active hours from *[method]*. Reviewer time assumed at [ratio]× operator hours (tuned for [peak] parallel windows). Operator-hour multiplier is vs the full-team rebuild estimate; per-developer-equivalent is the apples-to-apples number for METR/Copilot comparison. METR's public range (Feb 2026, n=7) is 2.1 – 11.6× per developer at 1.05 – 2.32 avg concurrency."
