---
name: research
description: Default entry point for any research request — a hybrid router that classifies the question deterministically and either delegates to a specialist research skill (pulse for trends/sentiment, grants for NIH funding, litreview for academic literature, syllabus for course reading, patent for prior-art + IP landscape, dossier for entity research) or runs its own plan-decompose-multi-source-search-synthesize-cite fallback workflow when no specialist matches. Always surfaces the routing decision so users can override. Use when the user makes any research request that doesn't obviously match a more-specific specialist skill (e.g., "research [topic]", "look into [topic]", "what do we know about [topic]", "investigate [topic]", "find me information on [topic]", "do some research on [topic]", "I need to understand [topic]"). Output is a markdown briefing (default) or .docx document (on request) with full citations and an audit log.
---

# Research — Hybrid Router + Fallback

**The runtime orchestrator for the research domain.** Architecture C: deterministic classification → specialist delegation OR own plan-decompose-search-synthesize-cite workflow.

## Portability

Requires `WebSearch` + `WebFetch` for the fallback workflow; specialist skills (`pulse`, `grants`, `litreview`, `syllabus`, `patent`, `dossier`) must be present for delegation to work. Node.js with `docx` package required if Q2 = document mode. Works in Claude Code CLI natively. In Claude.ai with web tools + Code Execution, the workflow is supported.

## Distinct From `engineering/autoresearch-agent`

These two skills share the word "research" but serve **completely different use cases**:

- **`research/research/`** (this skill) — research-query router + fallback workflow ("Research X")
- **`engineering/autoresearch-agent/`** — Karpathy's autonomous file-optimization experiment loop ("Make this code faster")

No overlap. They coexist.

## Hybrid Architecture (C)

Every invocation produces one of three outcomes:

1. **Delegation** — Classified as specialist-domain. Routes there. User sees the specialist's output.
2. **Fallback execution** — Classified as general research. Runs own plan → search → synthesize workflow.
3. **Clarification request** — Classification ambiguous OR a single bare-noun signal matched. Asks one forcing question (with a recommended answer) to disambiguate, then routes.

The skill **never silently runs its fallback** when a specialist would have done better. **Routing transparency** is what makes the hybrid architecture trustworthy.

## Specialist Registry

| Specialist | Routing signals | Domain |
|---|---|---|
| `pulse` | reddit / hn / x / buzz / sentiment / trending / "what's people saying" / "pulse on" / "take the pulse" / "current conversation" | Multi-source recency research |
| `grants` | NIH / grant / R01 / K-award / RePORTER / NOSI / "grants for" / FDA / "study section" / "principal investigator" | NIH grant-funding intelligence |
| `litreview` | literature review / PICO / SPIDER / systematic review / "review papers on" / meta-analysis | Academic literature orientation |
| `syllabus` | syllabus / course outline / curriculum / "reading list" / "for my class" / "for my students" | Course supplementary reading |
| `patent` | prior art / FTO / freedom to operate / patent / "patent landscape" / invention / novelty search / "ip landscape" | Patent prior-art + landscape |
| `dossier` | "dossier on" / "due diligence" / "background check" / "prep me for" / "competitor research" / "investor diligence" / "interview prep" / "background on" | Decision-grade entity research |

**Escalation → `deep-research`:** when a wrong answer is expensive (strategy, comparing N options, hypothesis validation, mapping a field) and rigor matters more than speed, escalate to the `deep-research` skill instead of the fast fallback workflow — it runs a triangulated, multi-round, adversarial investigation and persists an auditable, reusable research folder. This router is the fast path; `deep-research` is the heavyweight one.

## Agent Integrity Rules

This skill obeys the research-pack convention:

- **Execution discipline (fallback only)**: Sequential searches. 1 q/sec rate limit. Confirm response received before next call.
- **Source discipline**: Cite only sources returned by this session's tool calls. Training knowledge labeled `[Background — not from search]` and excluded from counts.
- **Three-count tracking (fallback only)**: Queries sent / sources received / sources cited.
- **Retry policy**: On failure → wait 3s → retry once → log. After 3 consecutive failures: stop, alert user.
- **Routing discipline**: Never delegate silently. Always state the decision + accept override.

## Phase 1: Grill-Me Intake (2–4 Questions)

Intake is intentionally minimal — the goal is to route fast, not to interrogate. One question per turn.

### Q1 (always) — Research question

> **What's the research question? State it in 1–2 sentences. Specific is better than broad — "AI for healthcare" gets you a vague survey; "How are health systems integrating LLM-based clinical decision support?" gets you a useful answer.**

**Refuse mush.** If user says "research AI", push back once: "What about AI specifically — adoption, safety, capability, funding, regulation, comparison? Pick an angle."

### Q2 (always) — Output preference

> **What output do you want? Pick one:**
> 1. Quick chat briefing (5-min read, markdown in chat)
> 2. Standalone document (.docx with citations, shareable)

Forcing choice. Document mode triggers deeper search budgets and full audit logs.

### Q3 (asked only when classification returns `ask` or `fallback` with no signals) — Domain disambiguation

> **Quick clarification — pick the closest match** *(recommended: {N} — your question matched a `{specialist}` signal)*:
> 1. Academic literature (papers, peer-reviewed)
> 2. Industry / trends (what's the buzz, news, sentiment)
> 3. Specific entity (a company, person, organization)
> 4. Technology / patents (prior art, IP landscape)
> 5. Grant funding (NIH, foundations)
> 6. Course material (syllabus or curriculum)
> 7. None of the above — run general research

When the classifier returned `ask` (single bare-noun signal), pre-mark the recommended option. **Skip if classification produced a silent route (≥2 signals OR one strong multi-word phrase).**

### Q4 (asked only if Q3 was needed AND user picked "none of the above") — General-research scope

> **For general research, what's your time horizon — quick scan (5 searches) or thorough (15 searches)?**

Skip if a specialist took over.

**Stop condition:** After Q4 (or earlier if dependency skips applied), commit and start Phase 2. **Most invocations exit intake after Q1 + Q2.**

## Phase 2: Deterministic Classification

This is **deterministic, not LLM-reasoned** — for speed, debuggability, and consistency.

```python
SIGNALS = {
  pulse:    ["reddit", "hn", "hacker news", "x.com", "twitter", "buzz",
             "sentiment", "trending", "what are people saying",
             "what's happening", "the conversation around",
             "pulse on", "take the pulse", "current conversation"],
  grants:   ["nih", "grant", "grants for", "r01", "r21", "k-award", "reporter",
             "nosi", "funding", "fda", "study section", "principal investigator"],
  litreview:["literature review", "lit review", "litreview", "pico", "spider",
             "systematic review", "review papers on", "research papers on",
             "papers about", "meta-analysis"],
  syllabus: ["syllabus", "course outline", "curriculum", "reading list",
             "for my class", "for my students", "course material"],
  patent:   ["prior art", "fto", "freedom to operate", "patent",
             "patent landscape", "invention", "novelty search",
             "patent search", "ip landscape"],
  dossier:  ["dossier on", "due diligence", "background check",
             "prep me for", "competitor research", "investor diligence",
             "interview prep", "research my competitor", "background on"]
}

# Signals are case-insensitive literal phrases (multi-word substring match).
# Bracketed placeholders (e.g., "research [company]") are intentionally NOT
# signals — they over-trigger on generic "research X" queries that should
# fall back to general research, not auto-route to dossier.
# STRONG signal = multi-word phrase (contains a space): pairs verb with noun
# ("dossier on", "prior art") and routes reliably.
# BARE-NOUN signal = single word ("funding", "fda", "patent", "grant"):
# too weak to silent-route on alone — it must trigger Q3 with a
# recommended answer instead.

For each specialist S:
  score[S] = count of SIGNALS[S] phrases matched in question (case-insensitive substring)

if max(score) >= 2:
  route_to = argmax(score)                  # high confidence — silent route
elif max(score) == 1 and only one specialist has score 1:
  if the matched phrase is multi-word (contains a space):
    route_to = that specialist              # strong phrase — silent route
  else:
    route_to = "ask"                        # bare noun — ask Q3, recommend that specialist
else:
  route_to = "fallback"                     # ambiguous or no match — ask Q3 / run fallback
```

**Implementation:** `scripts/classifier.py --question "..."` returns the routing decision + matched signals + per-specialist scores + (for `ask`) the recommended specialist. Use it; don't re-implement. The SIGNALS map and rules above are kept phrase-for-phrase in sync with the script — drift = bug.

## Phase 3a: Specialist Delegation (≥2 signals OR one strong multi-word phrase)

When delegating:

1. Pass the user's question **verbatim** plus the output preference (Q2)
2. **Let the specialist run its own grill-me intake** — do NOT pre-answer specialist questions
3. Return specialist output as the user-visible result
4. Tag the result with `[Delegated to: research → {specialist}]` in the chat output so the user knows what skill produced it
5. Tag the audit log via `scripts/routing_transparency_logger.py --action record_delegation`

## Phase 3b: Own Fallback Workflow

If routing produced no specialist match (and Q3 confirmed general research), run the 8-step fallback:

1. **Decompose** — break the question into 3–5 sub-questions (what / why / how / who / what's next). Show the decomposition before searching. `scripts/fallback_decomposer.py --question "..."` gives a deterministic starting point.
2. **Source selection** — per sub-question: recency → WebSearch+WebFetch (+Reddit/HN on signal); technical/docs → WebSearch+WebFetch; academic → Consensus MCP if connected, else WebSearch with `scholar.google.com` site filter; data/numbers → WebFetch primary documents; entity-level → offer `dossier` re-route.
3. **Search** — sequential per sub-question, 1 q/sec, 2–4 queries per source, broad-to-narrow.
4. **Read + extract** — WebFetch high-signal results; note every source URL.
5. **Synthesize** — 2–4 paragraphs per sub-question with inline citations; surface disagreement when sources disagree.
6. **Cross-cutting patterns** — 1–2 paragraphs across sub-questions: consensus, controversy, gaps.
7. **Output** — markdown brief by default; DOCX if user picked document mode.
8. **Audit log** — three counts (sent / received / cited) + per-source reliability tier (primary / secondary / tertiary).

## Routing Transparency Protocol (Mandatory)

After classification, the skill **always**:

1. **States the decision** in one sentence: "Routing to `litreview` because you mentioned PICO and meta-analysis (2 signals)."
2. **Offers override**: "If you want general research instead OR a different specialist, say so now."
3. **Proceeds with the recommended route if the user doesn't object** — no timers, no countdowns.
4. **If user overrides** → accept, re-route, log the override via `routing_transparency_logger.py --action record_override`.

**Never delegates silently.** This is the trust-building property that makes the hybrid pattern work.

## Output Format

**Markdown brief** (Q2 = quick chat briefing): title + `*Generated: [DATE] | Routed: [specialist | fallback]*`, then **TL;DR** (2-3 sentences) → **Findings** (one H3 per sub-question, inline citations) → **Cross-Cutting Patterns** → **Sources** (numbered, hyperlinked, reliability tier each) → **Audit** (three counts + failures).

**DOCX** (Q2 = standalone document): standard research-pack DOCX patterns — Arial 12pt, navy headings, blue table headers, hyperlinked sources, mandatory audit log section. Reference the `docx` skill for setup.

### Audit log block (fallback mode)

```
Queries sent: N | Sources received: M | Sources cited: K
Failures: F (3-consecutive-failures triggered: yes/no)
Per-source tier: [URL — primary | secondary | tertiary]
Routing decision: fallback (no specialist matched)
Sub-questions: [list]
```

All routing decisions + overrides also logged to `~/.research_sessions/<session>.json` via `routing_transparency_logger.py`.

## Failure Modes

| Failure | Behavior |
|---|---|
| Single bare-noun signal (e.g., "funding", "fda") | Ask Q3 with the matched specialist pre-marked as the recommended answer. Never silent-route. |
| Classification ambiguous (multiple 1-signal matches or none) | Ask Q3 (domain disambiguation). |
| Specialist delegation fails | Note in chat. Offer to retry or fall back to general research. |
| User overrides routing | Accept. Re-route. Log the override. |
| Fallback search returns thin results | Surface explicitly. Suggest the question may be too niche or too new. Do not fabricate. |
| 3 consecutive tool failures in fallback | Stop, alert user, share what was collected. |
| Question is non-research (e.g., "write me code") | Decline politely. Suggest the appropriate skill. |
| Sub-question can't be answered | Note as "limited public signal on this"; don't omit silently. |
| Output format mismatch | Honor Q2; if unavailable, fall back to markdown with note. |
| Specialist skill missing from environment | Skip it in classification scoring; route to fallback or next-best specialist. |

## Anti-Patterns Rejected

- LLM-reasoned classification (must be deterministic keyword + intent matching)
- Silent delegation (always surface routing decision)
- Refusing to route to a specialist when ≥2 signals match
- Silent-routing on a single bare-noun signal ("research FDA approval trends" must ask, not auto-route to grants)
- Wall-clock affordances ("auto-proceed after Ns") — the model cannot wait; proceed with the recommended route if the user doesn't object
- Pre-answering the specialist's grill-me intake (let it run its own)
- Fabricating sources in fallback when search is thin
- Skipping audit log in fallback mode
- Treating "dossier on [company]" as fallback when `dossier` is the right specialist (the verb-noun-paired phrase routes; the generic "research X" form does not)
- Auto-routing generic "research [topic]" queries to a specialist ("research Microsoft" alone is ambiguous — could be dossier or general; ask Q3 instead of guessing)

## Tooling

- **`scripts/classifier.py`** — Deterministic SIGNALS matching → routing decision (`specialist` / `ask` + recommended / `fallback`) + per-specialist score + matched phrases. `--question "..." --output json`.
- **`scripts/routing_transparency_logger.py`** — JSON-backed audit log at `~/.research_sessions/<session>.json`. Records every routing decision, override, and delegation handoff.
- **`scripts/fallback_decomposer.py`** — Heuristic question → 3–5 sub-questions (what / why / how / who / what's next).

### Reference Docs (each cites 7+ authoritative sources)

- **`references/hybrid_router_architecture.md`** — router-vs-run trade-offs + routing transparency principle
- **`references/deterministic_classification_canon.md`** — why keyword > LLM-reasoned for routing
- **`references/fallback_workflow_canon.md`** — plan-decompose-search-synthesize methodology

## Dependencies

- **`WebSearch`** + **`WebFetch`** — Required for fallback workflow
- **Specialist skills** — Required for delegation: `pulse`, `grants`, `litreview`, `syllabus`, `patent`, `dossier`. If a specialist is missing, the router skips it and routes to fallback instead.
- **Node.js `docx` library** — Required if user picks document output (Q2 = standalone)
- **Consensus MCP** — Optional; used in fallback if academic sub-questions surface

---

**Version:** 1.1.0
**Source spec:** [`megaprompts/13-research-megaprompt.md`](../../../../megaprompts/13-research-megaprompt.md)
**Build pattern:** Path B (direct conversion). v1.1.0: bare-noun signals now ask instead of silent-routing; 5s auto-proceed affordance removed; context-economy trim per the 2026-06 newgen audit.
