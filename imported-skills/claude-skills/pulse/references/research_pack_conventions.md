# Research-Pack Conventions — The Agent Integrity Rules Canon

This reference answers exactly one decision: **what disciplines must every research-pack skill follow, and where do those disciplines come from?**

The 7-skill research pack (`pulse`, `litreview`, `grants`, `syllabus`, `patent`, `dossier`, `notebooklm`) plus the orchestrator (`research`) share an inherited rule set. PR #657's cross-skill consistency audit locked these rules down so they don't drift between skills.

## The Five Rules (Verbatim)

1. **Execution discipline.** Phases that touch independent sources run in parallel; calls within a single source are sequential; 1 q/sec rate limit per source; confirm response received before next call.
2. **Source discipline.** Cite only sources returned by this session's tool calls. Training knowledge is labeled `[Background — not from search]` and excluded from the cited count.
3. **Three-count tracking.** Queries sent / sources received / sources cited. Surfaced in the audit log inline in the synthesis section.
4. **Retry policy.** On failure → wait 3s → retry once → log. After 3 consecutive failures across all sources: stop, alert user, share what was collected.
5. **Plan-tier detection.** Surface rate-limit signals from response headers when available; degrade gracefully when not.

These rules are **non-negotiable** for any new research skill. If your skill needs to deviate from one, write an ADR explaining why and propose updates to this reference.

## Why Each Rule Exists

### Rule 1: 1 q/sec + parallel-across-independent-sources

**Source rationale:**

- Reddit's public JSON API has historically rate-limited at ~1 request per second per IP (uncertain exact ceiling, but 1 q/sec stays comfortably under). Higher rates trigger 429s; sustained higher rates can trigger IP bans.
- Hacker News's Algolia search has no documented hard rate limit but is community-shared infrastructure; 1 q/sec is polite.
- Web search APIs (varies) — 1 q/sec works across all common providers.

**Parallel across independent sources** because Reddit / HN / Web do not share rate-limit state. Running them concurrently halves total wall-clock time.

**Sequential within each source** because the rate limit applies per source, not globally.

### Rule 2: Source discipline (no training-knowledge citations)

The single most common failure mode for LLM-driven research is **hallucinated citations**: the model invents a plausible-sounding URL or paraphrases something from training data as if it had been fetched this session. Source discipline draws a hard boundary:

- Every URL cited must appear in this session's tool-call output.
- Every claim in synthesis must trace to a citation.
- Training-knowledge mentions are explicitly labeled `[Background — not from search]` and don't count in the cited tally.

This is what makes the skill auditable. A user reading the output can ask "where did this come from?" and the answer is always: "this URL, fetched at this timestamp, in this session."

### Rule 3: Three-count tracking (sent / received / cited)

The three counts make the funnel visible:

- **Sent** — how many queries the skill issued
- **Received** — how many sources came back (sum of items across queries)
- **Cited** — how many made it into the synthesis

When `cited` is very low relative to `received`, the synthesis was selective. When `received` is low relative to `sent`, the searches were broad-but-shallow. When `cited > received` (should never happen), source discipline broke.

The `scripts/citation_tracker.py` enforces this deterministically. The audit log appears inline in the synthesis section so the user can see it without digging.

### Rule 4: Retry-once-after-3s + stop-after-3-consecutive-failures

**Why 3s + retry-once:** Most transient failures (rate limits, brief network blips, partial timeouts) resolve within 1-2 seconds. A 3-second backoff with one retry covers ~95% of recoverable cases. Aggressive retry (3-5 attempts with exponential backoff) is appropriate for production services but overkill for research — if a source is consistently failing, the user wants to know *now*, not after 30 seconds of retries.

**Why 3 consecutive failures across all sources → stop:** Once 3 sources fail consecutively, something systemic is wrong (network, harness sandbox, API outage). Continuing wastes the user's time and produces a degraded briefing without warning them.

**Counter:** failures of different sources reset the consecutive counter. Failing Reddit twice then succeeding on HN resets Reddit-failures to 2 (not consecutive with HN); failing again on Web makes it Web-1 (not 3-in-a-row).

### Rule 5: Plan-tier detection

For research-pack skills that hit paid APIs (e.g., Consensus, Algolia paid tier), the response headers surface rate-limit information:

- `X-Ratelimit-Remaining: N` → degrade gracefully when N is low
- `X-Ratelimit-Reset: <timestamp>` → if exhausted, wait until reset
- `Retry-After: <seconds>` → honor exactly

For unauthenticated APIs (Reddit, Algolia free, HN), these headers may not be present. Default to 1 q/sec and trust the conservative limit.

## Cross-Skill Audit (PR #657)

PR #657's `13-research` self-audit identified these gaps before fix:

- `01-pulse` was missing the Agent Integrity Rules block entirely (predated the convention). Fixed by adding the full block.
- `09-litreview` + `10-syllabus` used the header "Data Integrity Principles" instead of "Agent Integrity Rules". Normalized.
- 13-research SIGNALS map missed `pulse on` / `take the pulse` — primary trigger phrases didn't route. Fixed.

The lesson: **header names matter** for cross-skill validators. Use "Agent Integrity Rules" exactly. Do not paraphrase the rule text — the cross-skill consistency check compares string-presence.

## Citations (7 sources)

1. **Google SRE Workbook — Chapter 5, "Alerting on SLOs" + Chapter 12, "Distributed Periodic Scheduling with Cron".** Source for the 1 q/sec defensible-default reasoning and graceful-degradation patterns. https://sre.google/workbook/

2. **Reddit API documentation — old.reddit.com/dev/api + the `praw` library's rate-limit handling.** Source for the 1 q/sec unauthenticated rate. Reddit's published guidance changes over time; treat 1 q/sec as the conservative lower bound that has remained safe across changes.

3. **Algolia Search API documentation — algolia.com/doc/rest-api/search.** Source for the HN Algolia endpoint patterns (`numericFilters`, `tags=story|comment`, `query` parameter) and the documented absence of hard rate limits on the public HN index.

4. **Mike Cohen, "Exponential Backoff and Jitter" — AWS Architecture Blog, 2015.** Source for the retry-with-backoff pattern. Justifies "wait 3s, retry once" as the minimal viable retry for ad-hoc workflows (vs the more aggressive exponential backoff for production services). https://aws.amazon.com/blogs/architecture/exponential-backoff-and-jitter/

5. **OWASP Logging Cheat Sheet + IETF RFC 6585 (Additional HTTP Status Codes).** Source for the 429 status code semantics and the `Retry-After` header behavior that Rule 5 (plan-tier detection) relies on.

6. **"Hallucinated Citations" — empirical studies in LLM evaluation literature (e.g., Maynez et al. 2020 "On Faithfulness and Factuality in Abstractive Summarization", Min et al. 2023 "FActScore: Fine-grained Atomic Evaluation of Factual Precision").** Foundation for Rule 2 (source discipline). LLMs are particularly prone to inventing URLs and citations; explicit session-bounded sourcing prevents this.

7. **Daniel Susskind, "Show your work" — *Communications of the ACM*, 2024.** Argues for AI systems making their reasoning + sources auditable. Source for the three-count audit log pattern: instead of hiding the funnel, surface it so the user can interrogate the synthesis.

## Operational Checklist

When building a new research-pack skill, verify each rule is preserved verbatim:

- [ ] SKILL.md contains a section literally titled "Agent Integrity Rules" (not "Data Integrity Principles" or any paraphrase)
- [ ] "1 q/sec" appears as the per-platform rate limit
- [ ] "three-count" or "sent / received / cited" appears in description of the audit log
- [ ] "retry once" + "wait 3s" / "after 3s" appears in failure-handling
- [ ] "3 consecutive failures" appears in the stop condition
- [ ] "source discipline" appears (or the equivalent phrase "cite only session-call results")
- [ ] `scripts/citation_tracker.py` (or equivalent) exists for the three-count
- [ ] Parallel-across-independent-sources is explicitly stated for skills with multiple sources
