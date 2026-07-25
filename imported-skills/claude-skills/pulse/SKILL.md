---
name: pulse
description: "Multi-source recency research skill that takes the pulse of any topic across Reddit, Hacker News, the open web, and optionally X/Twitter within a configurable recent window (default 30 days). Forcing intake clarifies topic specificity, angle (trend/sentiment/problems/opportunities/comparison), time window, and platform scope before searching. Returns a synthesized briefing with citations, engagement metrics, and cross-platform pattern analysis. Use when the user requests multi-source recency intelligence on a topic (e.g., 'pulse on [topic]', 'what's happening with [topic]', 'what are people saying about [topic]', 'current conversation about [topic]', 'take the pulse of [topic]', 'trending: [topic]', 'find me info on [topic]'), and for competitor research, trend discovery, tool comparisons, and audience sentiment analysis."
license: MIT
metadata:
  source_spec: "megaprompts/01-pulse-megaprompt.md"
  build_pattern: "Path B (direct conversion)"
  research_pack_convention: "Agent Integrity Rules block preserved verbatim per PR #657 audit"
  version: 1.0.0
---

# Pulse — Multi-Source Recency Research

> **Portability:** Works in both Claude Code CLI and Claude.ai. The optional X/Twitter phase requires browser automation and is skipped automatically if unavailable.

A recency-oriented research skill that synthesizes what people are saying about a topic across Reddit, Hacker News, the open web, and (optionally) X/Twitter — within a configurable time window. Output is a single coherent briefing with citations, engagement signals, and cross-platform pattern analysis. The skill captures the **current conversation**, not the canonical reference.

## Invocation

**Explicit trigger phrases:**
- "pulse on [topic]"
- "what's happening with [topic]"
- "what are people saying about [topic]"
- "current conversation about [topic]"
- "take the pulse of [topic]"
- "trending: [topic]"
- "find me info on [topic]"

Also covers: competitor research with recency flavor, trend discovery, tool comparisons, audience sentiment analysis.

## Agent Integrity Rules (Research-Pack Convention)

The following rules apply throughout the run. They are inherited from the research-pack convention and locked down by PR #657's cross-skill consistency audit.

- **Execution discipline.** Phases 1–3 run in parallel (Reddit + HN + Web are independent). Within each phase, sequential calls only. **1 q/sec rate limit per platform.** Confirm response received before next call within the same phase.
- **Source discipline.** Cite only sources returned by **this session's tool calls.** Training knowledge is labeled `[Background — not from search]` and excluded from primary findings count.
- **Three-count tracking.** Queries sent / sources received (shown) / sources cited. Surfaced in the audit log inline in the synthesis section. Use `scripts/citation_tracker.py` for the deterministic count.
- **Retry policy.** On failure → wait 3s → retry once → log. After **3 consecutive failures across all sources:** stop, alert user, share what was collected. Never deliver an empty file.
- **Plan-tier detection.** Reddit + HN are unauthenticated public JSON APIs (rate-limited per IP, not per plan). Surface rate-limit signals from response headers when available; degrade gracefully otherwise.

See `references/research_pack_conventions.md` for the canon and `references/parallel_execution_discipline.md` for the rate-limit rationale.

## Phase 0: Grill-Me Intake (2–4 forcing questions, one at a time)

Dependency-ordered. Each question carries explicit "why I'm asking". Stop condition: max 4.

### Q1 (root) — Topic Specificity

> **What's the topic? State it in 1–2 sentences — be specific. "AI" or "tech" will get you a vague survey; "self-hosted LLM deployment for small teams" or "Claude Code adoption among enterprise engineering orgs" will get you a useful answer.**
>
> *Why I'm asking:* Specificity dictates search quality. Vague topics produce vague briefings. If your topic is broad, I'd rather narrow it now than spend a search budget on noise.

**Refuse mush.** If the user says "AI", push back once: "What about AI — adoption, safety, capability, regulation, or comparison? Pick an angle." If the user still won't narrow after one push-back, deliver with the explicit "vague topic — survey level, not depth" caveat.

### Q2 (depends on Q1) — Angle

> **What angle matters most? Pick one:**
>
> 1. **Trend** — what's accelerating or decelerating
> 2. **Sentiment** — what people feel about it
> 3. **Problems** — pain points and complaints
> 4. **Opportunities** — gaps and unmet needs
> 5. **Comparison** — how it stacks up against alternatives
>
> *Why I'm asking:* The angle dictates which sources weight more (Reddit for sentiment, HN for technical critique, Web for trend coverage) and how I rank the synthesis.

Forcing choice. **Recommended default:** trend, unless the topic obviously calls for a different angle.

### Q3 (always) — Time Window

> **Time window: 7 / 14 / 30 / 60 / 90 days? Default is 30.**
>
> *Why I'm asking:* 7 days catches breaking conversation; 90 days catches sustained narrative shift. Pick based on how recent the news matters.

Forcing choice with default.

### Q4 (depends on Q1) — Platform Scope

> **Any platform to skip? By default I'll cover Reddit + Hacker News + open web, plus X/Twitter if browser automation is available. Skip any you don't care about.**
>
> *Why I'm asking:* Skipping a platform saves search budget. Reddit dominates sentiment; HN dominates technical critique; Web dominates breadth; X dominates breaking conversation. Skip what doesn't fit your angle.

Asked only if Q1 + Q2 suggest some platforms are clearly off-target (e.g., consumer sentiment topic → HN less useful). Otherwise default to "all platforms".

**Stop condition:** After Q4 (or earlier with dependency skips), commit and start Phase 1. Max 4 questions, never bundle.

## Pre-flight

Before any phase fires:

1. **Compute the time window** with `scripts/time_window_calculator.py --window <Nd>`. Get back the Unix timestamp for `created_at_i>` (HN) and the `t=` parameter (`hour|day|week|month|year|all`) for Reddit.
2. **Generate the output slug** with `scripts/topic_slug_generator.py --topic "<topic>" --date $(date +%Y-%m-%d)`. Detect if `${RESEARCH_DIR}/pulse/<slug>-<date>.md` already exists; if yes, append `-v2` suffix or warn user.
3. **Start the three-count audit log** with `scripts/citation_tracker.py --action start --session pulse-<date>-<slug>`. This file at `~/.pulse_sessions/<session>.json` persists across the run.

## Phase 1: Reddit (parallel with HN + Web)

**API:** `reddit.com/search.json` (unauthenticated, public JSON).

**Queries (sequential within Reddit, 1 q/sec):**
1. `sort=top&t=<window>&q=<topic>` — top posts in window
2. `sort=new&t=<window>&q=<topic>` — new posts in window (catches breaking signal)
3. For each of the top 3–5 posts by score: fetch the comments JSON (`<post-url>.json?limit=top`) for the top 10–20 comments.

**Headers / rate limits.** Reddit rate-limits by IP, not plan. Throttle to 1 q/sec. If response has `X-Ratelimit-Remaining: 0` or returns 429, wait 3s, retry once. If still failing, fall back to subreddit-restricted search (`r/<topic-subreddit>/search.json`) or `?raw_json=1`.

**Record each query:** `citation_tracker.py --action record_sent --session NAME --query "..."`.
**Record received counts:** `citation_tracker.py --action record_received --session NAME --count N`.

## Phase 2: Hacker News (parallel with Reddit + Web)

**API:** Algolia HN search (`hn.algolia.com/api/v1/`).

**Queries (sequential within HN, 1 q/sec):**
1. `search?query=<topic>&numericFilters=created_at_i><timestamp>&tags=story` — stories in window
2. `search?query=<topic>&numericFilters=created_at_i><timestamp>&tags=comment` — comments in window (catches discussion signal)

**Failure handling.** If HN returns empty: broaden the query (remove uncommon nouns); if still empty, drop the timestamp filter as last resort and label results "outside window".

**HN bias note.** HN skews technical / builder. Surface this in synthesis: "HN's voice is implementation-oriented; consumer sentiment will be under-represented here."

## Phase 3: Web Search (parallel with Reddit + HN)

**Tools:** Available web search + fetch (e.g., `WebSearch` + `WebFetch`).

**Query strategy (sequential within Web, 1 q/sec):**
1. **Trusted publishers** — `"<topic>" site:nytimes.com OR site:wsj.com OR site:wired.com OR site:theverge.com OR site:techcrunch.com after:<date>`
2. **Recent reviews** — `"<topic>" review <year>` or `"<topic>" "honest review" after:<date>`
3. **Honest-opinion sources** — `"<topic>" problems OR complaints OR "worth it" after:<date>`

Fetch the top 3–5 URLs per query. Truncate at the body, skip cookie/nav markup.

**Citation discipline.** Every claim in the Web section must trace to a fetched URL. Do NOT cite from snippets alone; fetch first.

## Phase 4: X/Twitter (sequential, optional)

Run last. Reasons:
- Most likely to fail / require browser automation
- X content overlaps significantly with Reddit/HN — so it adds delta, not primary signal

**Interface (in priority order):**
1. **Grok** if available in the harness
2. **X API** if authenticated
3. **Browser automation** if the harness supports it (Claude Code CLI with `playwright` or similar)
4. **Skip with note** if none of the above available

**Documented behavior:**
> If Phase 4 is skipped: include the section header `## X/Twitter` with body `Skipped — [reason: no browser automation / no Grok / no X API]`. Do NOT pretend to have data.

## Synthesis (Cross-Platform Patterns)

After Phases 1–4 complete (or Phase 4 skipped), produce the synthesis:

1. **Consensus signals** — points where 3+ platforms agree (highest confidence). Tag each with cited source URLs.
2. **Controversy signals** — points where platforms disagree. Note who says what.
3. **Pain points** — recurring complaints across sources (esp. Reddit + Web).
4. **Excitement signals** — recurring enthusiasm (esp. HN + X if available).
5. **Emerging trends** — first-time mentions in newest posts but absent from older ones (compare `sort=new` vs `sort=top`).
6. **Gaps** — what's notably absent that you'd expect to find.

For each pattern, **cite the source URLs** that support it. Use `citation_tracker.py --action record_cited --session NAME --url "..."` per citation.

See `references/cross_platform_synthesis.md` for detection heuristics.

## Output

Save to file AND paste in chat:

**File:** `${RESEARCH_DIR}/pulse/<topic-slug>-<YYYY-MM-DD>.md` (path from `topic_slug_generator.py`).

**Format:**

```markdown
# [TOPIC] — Pulse (Last [N] Days)
*Generated: [DATE] | Angle: [Q2 choice]*

## TL;DR
[2-3 sentences max]

## Reddit
### Top Posts
- **[Title]** (r/sub) — [score, comments] — [summary] — [URL]
### What Reddit Is Saying
[Narrative paragraph]

## Hacker News
### Notable Stories
- **[Title]** — [points, comments] — [summary] — [URL]
### What HN Is Saying
[Narrative paragraph; note HN's technical/builder bias]

## Web
### Key Sources
- **[Title]** ([Publication]) — [takeaway] — [URL]
### What the Web Is Saying
[Narrative paragraph]

## X/Twitter (if available)
[Cleaned response, with handles/references preserved]
[Or: "Skipped — [reason]"]

## Cross-Platform Patterns
[Highest-confidence signals across sources]

## Key Takeaways
- [3-5 bullets]

## Content Angles (if applicable)
[2-3 specific angles supported by the data]

---
*Audit:* Queries sent: N (Reddit: a, HN: b, Web: c, X: d|skipped).
Sources received: M. Sources cited: K. Training knowledge: 0 ([Background] excluded from count).
```

## Error Handling

| Failure | Behavior |
|---|---|
| Topic is too vague (Q1) | Refuse to start. Re-ask Q1 once with examples. After 1 push-back, deliver with "vague topic" caveat. |
| Reddit blocks / rate-limits | Try `?raw_json=1` or fall back to subreddit-restricted search. Honor 3s-retry. |
| HN returns empty | Broaden query, drop timestamp filter as last resort, label results "outside window". |
| Web search returns nothing useful | Note in output; don't fabricate sources. |
| Browser automation unavailable | Skip Phase 4 with documented note. |
| WebFetch times out | Use what loaded, mark the source as "truncated". |
| 3 consecutive failures across sources | Stop. Return what was collected with explicit "stopped early" note. Do NOT deliver empty file. |
| All sources fail | Return error with diagnostic info. Do NOT deliver empty file. |

## Tooling

| Script | Role |
|---|---|
| `scripts/time_window_calculator.py` | Compute Unix timestamps + Reddit `t=` parameter from window string (`30d`, `7d`, etc.). Deterministic from `datetime.now()`. |
| `scripts/citation_tracker.py` | JSON-backed three-count audit log (sent / received / cited) at `~/.pulse_sessions/<session>.json`. |
| `scripts/topic_slug_generator.py` | Filesystem-safe slug + duplicate-date detection for output paths. |

## References

- `references/research_pack_conventions.md` — Agent Integrity Rules canon (7+ sources: Google SRE, Reddit API docs, Algolia HN docs, exponential-backoff literature, citation discipline)
- `references/cross_platform_synthesis.md` — consensus / controversy / pain detection across platforms (7+ sources)
- `references/parallel_execution_discipline.md` — 1 q/sec rationale + plan-tier signals (7+ sources)

## Anti-Patterns To Reject

- Starting any search before the user commits to topic specificity (Q1)
- Batching intake questions instead of one at a time
- Hardcoded URLs that won't survive API changes (note format, explain may evolve)
- Specific person / brand references in the skill body
- Tight coupling to one X/Twitter interface
- Missing fallback behavior on source failure
- "Just use [specific tool]" without explaining what the tool does
- Citing training knowledge in the cited count
- Fabricating sources to fill out a section

---

**Version:** 1.0.0
**Source spec:** [`megaprompts/01-pulse-megaprompt.md`](../../../../megaprompts/01-pulse-megaprompt.md)
**Build pattern:** Path B (direct conversion). Re-grill with `/cs:grill-with-docs` if drift between spec and implementation surfaces.
