# Fallback Workflow Canon — Plan / Decompose / Search / Synthesize / Cite

This reference answers one decision: **when no specialist matches, what workflow does the orchestrator run instead?** The answer is an **8-step plan-decompose-multi-source-search-synthesize-cite** workflow grounded in the canonical research-pack conventions.

## The Eight Steps

The fallback workflow is documented in `SKILL.md`. This reference explains the **why** behind each step + the failure modes per step + the tooling that supports it.

### Step 1: Decompose

Break the research question into 3–5 sub-questions. Use the framework: **what / why / how / who / what's next**.

**Why decompose?** A 1-sentence research question rarely has a 1-source answer. Decomposition forces the orchestrator to enumerate the actual claim shape before searching, which makes search precise + makes synthesis structured.

**Failure mode:** decomposing into too many sub-questions (>5) wastes search budget on diminishing returns. Cap at 5.

**Tooling:** `scripts/fallback_decomposer.py` returns a deterministic starting point. Override + refine before searching.

### Step 2: Source Selection

For each sub-question, pick the right source class. Use the deterministic mapping in SKILL.md:

- Recency-sensitive → WebSearch + WebFetch (+ optional Reddit/HN signal)
- Technical specs → WebSearch + WebFetch
- Academic → Consensus MCP if available; else WebSearch + scholar.google.com filter
- Data / numbers → WebSearch for primary documents
- Entity-level → consider routing back to `dossier`

**Failure mode:** using a wrong-class source (e.g., WebSearch for academic when Consensus would have produced higher-quality results). The mapping is deterministic for a reason.

### Step 3: Search

Sequential per sub-question. **1 q/sec rate limit** (research-pack convention). Per source: 2–4 queries, broad-to-narrow.

**Why broad-to-narrow?** Broad queries map the landscape; narrow queries find the high-signal sources within it. Going narrow-only often misses the orienting overview.

**Failure mode:** parallel search bursts that trigger rate-limiting or get blocked. Sequential is the discipline.

### Step 4: Read + Extract

For each high-signal result: WebFetch the full content + extract the relevant section + note the URL.

**Why extract, not summarize?** Direct quotes + section references make citations verifiable. Summaries hide the source structure.

**Failure mode:** synthesizing from search snippets without WebFetch. Snippets are not sources.

### Step 5: Synthesize Per Sub-Question

For each sub-question: 2–4 paragraphs with inline citations. Surface disagreement when sources disagree.

**Why per-sub-question?** Sub-question structure carries through to the output. Reader can navigate to the part they care about.

**Failure mode:** synthesizing across sub-questions in one mega-paragraph. Loses the navigability + makes disagreements harder to surface.

### Step 6: Cross-Cutting Patterns

After per-sub-question synthesis: 1–2 paragraphs of patterns across all sub-questions — consensus, controversy, gaps.

**Why a separate section?** Pattern-level claims (e.g., "all sources agree on X but disagree on Y") are valuable for the reader's understanding but don't belong inside any single sub-question's synthesis.

**Failure mode:** skipping this step because "the sub-questions cover it". They don't — the cross-cutting view is its own contribution.

### Step 7: Output

Markdown brief by default. DOCX if Q2 = document mode. Honor user preference.

**Why honor preference?** Document mode triggers deeper search budgets + full audit logs. Brief mode is optimized for fast delivery. Different goals → different output shapes.

**Failure mode:** producing DOCX when user wanted brief (overkill) or producing brief when user wanted DOCX (loses citations).

### Step 8: Audit Log

Three-count summary (queries sent / sources received / sources cited) + per-source list with reliability tier.

**Why audit?** Research-pack convention. Lets the reader verify the orchestrator didn't fabricate sources or hide failures.

**Failure mode:** skipping the audit. Audit is what makes the fallback output trustworthy.

## The Three-Count Convention

The research-pack convention requires tracking three integers throughout the fallback workflow:

- **Sent**: queries actually issued (WebSearch + WebFetch + Consensus calls)
- **Received**: results returned from those calls (after filtering)
- **Cited**: sources actually cited in the final output

The relationship `sent >= received >= cited` is always true. When it isn't, something went wrong.

**Why three counts?** They make the orchestrator's search productivity visible. If sent=15, received=3, cited=1, the question was too niche or the search strategy was off. If sent=5, received=20, cited=15, the orchestrator found a rich vein. The reader can interpret the result quality based on the counts.

## Source Discipline

The orchestrator cites **only sources returned by this session's tool calls**. Training knowledge is labeled `[Background — not from search]` and excluded from the three-count.

**Why?** Citations must be verifiable. A "cited" source that wasn't actually retrieved is a fabrication, regardless of how well it matches the orchestrator's training data.

**Failure mode:** inferring a citation from background knowledge + presenting it as if retrieved. This is the highest-severity research-pack violation.

## Retry + Failure Policy

- **On single failure**: wait 3s → retry once → log.
- **After 3 consecutive failures**: stop, alert user, share what was collected.

**Why 3s + single retry?** Most failures are transient (rate limit, network blip). 3s + retry catches them. After 3 in a row, something structural is wrong (API outage, blocked endpoint, query-format issue); halt + escalate.

**Failure mode:** infinite retry loops that consume the session budget. The 3-consecutive-failure stop is the safety valve.

## Reliability Tier Classification

Per source, classify as:

- **Primary** — original source (peer-reviewed paper, government document, company filing, original announcement)
- **Secondary** — derivative reporting (news article summarizing a paper, blog post analyzing a filing)
- **Tertiary** — aggregator or wiki (Wikipedia, news aggregator, opinion piece)

**Why surface tiers?** Reader needs to know which claims rest on primary evidence vs derivative reporting. A consensus claim backed by 5 secondary sources is weaker than the same claim backed by 1 primary source.

**Failure mode:** misclassifying tier to make the audit look better. Honest tiering > polished audit.

## Disagreement Surfacing

When two sources disagree on a sub-question's answer:

- **Name both positions** in the synthesis
- **Cite both sources**
- **State which seems stronger** + why (primary vs secondary, recency, methodology)
- **Don't pick a winner without reasoning**

**Why?** Hiding disagreement misleads the reader. Surfacing it lets them apply their own judgment.

**Failure mode:** averaging two disagreeing sources into a mushy middle that neither source actually supports. This is the synthesis equivalent of fabrication.

## When To Stop Searching (Fallback Mode)

The fallback workflow is **not infinite**. Q4 sets the budget (5 searches for quick scan, 15 for thorough). Stop when:

- Budget exhausted
- All sub-questions have ≥1 high-signal source
- 3-consecutive-failure threshold hit
- User says "stop" or "that's enough"
- Diminishing returns (last 3 searches produced no new high-signal sources)

**Why budget the search?** Open-ended search is the failure mode that turns "research X" into a 30-minute exploration. Budget forces commitment + delivery.

## What Goes Wrong With Fallback

### Fabricated sources

The orchestrator infers a citation from background knowledge. Highest-severity violation. **Prevention:** strict source discipline + three-count tracking makes this auditable.

### Thin results presented as comprehensive

Search returned 2 sources. Orchestrator presents conclusions as if backed by 10. **Prevention:** surface the audit counts. Reader sees `cited: 2` + adjusts confidence.

### Skipping cross-cutting patterns

Per-sub-question synthesis without cross-cutting view. Reader misses the pattern-level insight. **Prevention:** Step 6 is mandatory.

### Skipping audit

Output without the audit section. **Prevention:** Audit is part of the output format, not optional.

### Wrong output format

User asked for brief, got DOCX. Or vice versa. **Prevention:** Q2 captures preference + Step 7 honors it.

### Synthesis without decomposition

Orchestrator searches first, organizes later. Output is unstructured. **Prevention:** Step 1 (decompose) before Step 3 (search) is non-negotiable.

## When To Choose Fallback Over Specialist

The classifier handles this deterministically. But conceptually, fallback is right when:

- No specialist's signal vocabulary fits the question
- User explicitly picked "none of the above" in Q3
- User overrode the routing decision to fallback
- A specialist failed + user opted to retry as fallback

Fallback is **wrong** when:

- A specialist clearly matched (≥2 signals) but the orchestrator ran fallback anyway
- The question is structurally a specialist's domain but used non-canonical phrasing (this is the Q3 case — disambiguate, then route)

## Operational Checklist (Per Fallback Run)

- [ ] Q1 specific enough to decompose (push back if vague)
- [ ] Decomposition produced 3-5 sub-questions
- [ ] Source class chosen per sub-question
- [ ] Sequential 1 q/sec search discipline
- [ ] WebFetch on every cited result
- [ ] Per-sub-question synthesis with citations
- [ ] Cross-cutting patterns section
- [ ] Output format honors Q2
- [ ] Three-count tracked
- [ ] Reliability tier per source
- [ ] Audit log included
- [ ] No fabricated citations

## Citations (7 sources)

1. **Cooper, Hedges, Valentine — "The Handbook of Research Synthesis and Meta-Analysis" (2009, 3rd ed.).** Source for the canonical research-synthesis workflow: question → decomposition → systematic search → extraction → synthesis → reporting. The fallback workflow is a lightweight adaptation of this for AI-orchestrated general research.

2. **Cochrane Collaboration — Handbook for Systematic Reviews of Interventions (current ed.).** Source for the rigor of source classification (primary vs secondary vs tertiary), explicit search protocols, and audit requirements. The three-count + per-source-tier conventions trace to Cochrane practice.

3. **PRISMA 2020 Statement — Page et al., BMJ 2021.** Source for the canonical reporting checklist for research synthesis: searches conducted + sources screened + sources included + sources excluded with reasons. The audit log in fallback mode parallels PRISMA's flow diagram.

4. **Karpathy, Andrej — "On chunking and search in LLMs" (talks 2024-2025).** Source for the principle that decomposition before retrieval beats single-shot retrieval. Sub-questions drive precise queries; whole-question retrieval is too broad. https://karpathy.ai/

5. **Anthropic — Multi-Agent Research System (2024-2025).** Source for the orchestrator-runs-fallback-with-audit pattern. Anthropic's research orchestrator includes explicit audit + source-tier surfacing as trust mechanisms. https://www.anthropic.com/research

6. **Tufte, Edward — "The Visual Display of Quantitative Information" (1983).** Source (by analogy) for the principle of surfacing data integrity to the reader rather than hiding methodology. The three-count + audit log are the textual analogue of Tufte's data-ink ratio: report what you did so the reader can interpret what you found.

7. **NIST — Special Publication 800-53 (Audit Logging guidance).** Source for the operational discipline of immutable, structured audit logs. The `routing_transparency_logger.py` JSON-backed log + the fallback audit section both implement this discipline at different scales.
