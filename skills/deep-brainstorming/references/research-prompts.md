# Research Prompt Templates

Reference file for deep-brainstorming skill. Load when structuring research rounds.

## Agent Discipline (inject into ALL researcher prompts)

Every researcher prompt MUST include these instructions:

```
SYNTHESIZE FIRST — write your findings report before doing more searches.
You can always search more after writing what you know. Do not spend more
than 60% of your effort on searching — the remaining 40% must go to synthesis.

For library documentation, prefer structured doc sources (e.g., Context7 MCP, official API docs)
over web search where available. They return focused content at lower token cost.
```

**Max 5 questions per agent.** If you have more questions, split across parallel agents.

## Round 1: Broad Discovery

One agent per domain. Each agent gets the same vision doc but a different functional area.

### Prompt Template (Round 1)

```
You are researching [DOMAIN AREA] solutions for a project.

SYNTHESIZE FIRST — write your findings report before doing more searches.
You can always search more after writing what you know.

For library API docs, prefer structured documentation sources (official docs, doc tools)
over web search. Use web search for benchmarks, comparisons, and non-library topics.

## Requirements
[Paste sanitized vision document here]

## Your Task (max 5 questions — focus on these)
Research the best approaches for the [DOMAIN AREA] requirements above.

1. Identify the top 3-5 approaches (include both open-source and commercial options)
2. For each approach, provide:
   - What it does and how it addresses the requirements
   - Verified benchmark data (cite the original source, not a blog post)
   - Known limitations for this specific use case
   - Production readiness (who uses it at scale?)
3. Rank approaches by quality-of-fit for THESE specific requirements
4. Note any requirements that NO current tool fully addresses

Verify all claims via web search. Do not rely on training data for version numbers,
benchmarks, or feature availability. If you cannot verify a claim, mark it as UNVERIFIED.

Do NOT recommend tools because they are popular. Recommend them because they are
the best fit for these specific requirements.
```

### Domain Split Examples

| Project Type | Domains to Split |
|-------------|-----------------|
| Web application | Backend framework, Frontend framework, Database, Auth, Deployment |
| Data pipeline | Ingestion, Processing, Storage, Query layer, Orchestration |
| ML/AI product | Model serving, Training infra, Data pipeline, Monitoring, API layer |
| Mobile app | Native vs cross-platform, Backend, Realtime sync, Storage, Push notifications |
| RAG system | Embedding model, Vector DB, Retrieval strategy, LLM, Document processing |

## Round 2: Fresh Verification

Critical: Round 2 prompts must NOT reference Round 1 findings. Ask the same functional questions with different framing.

### Prompt Template (Round 2)

```
You are independently evaluating approaches for [DOMAIN AREA].

SYNTHESIZE FIRST — write your findings report before doing more searches.
You can always search more after writing what you know.

For library API docs, prefer structured documentation sources (official docs, doc tools)
over web search. Use web search for benchmarks, comparisons, and non-library topics.

## Requirements
[Paste same sanitized vision document]

## Your Task (max 5 questions — focus on these)
Without assuming any prior research has been done:

1. What are the strongest solutions for [DOMAIN AREA] given these requirements?
2. For each solution:
   - Current version and release date (verify via official source)
   - Performance characteristics verified from independent benchmarks (not vendor)
   - Integration complexity with [related domains from vision]
   - Licensing and pricing (verify current, not cached)
3. What would you recommend if cost were no object? What about for a constrained budget?
4. What's the biggest risk with the most popular option in this space?

Verify via web search. Mark anything you cannot independently confirm as UNVERIFIED.
```

### Comparing Round 1 and Round 2

After both rounds complete:

| Signal | Interpretation | Action |
|--------|---------------|--------|
| Same recommendation, same evidence | Genuine convergence — likely a strong choice | Verify the shared evidence independently |
| Same recommendation, different evidence | May be correct but verify — could be popularity bias | Deep-dive on whether the evidence actually supports the recommendation |
| Different recommendations | Research divergence — investigate further | Round 3 targeted at the disagreement |
| Same recommendation, one round has no evidence | Likely popularity/marketing bias in the weak round | Trust the round with verifiable evidence |

## Round 3+: Targeted Investigation (Thorough Only)

Only needed when Rounds 1 and 2 diverge significantly.

### Prompt Template (Round 3)

```
Two independent research rounds produced different recommendations for [DOMAIN AREA]:
- Round A recommends: [OPTION A] because [EVIDENCE A]
- Round B recommends: [OPTION B] because [EVIDENCE B]

SYNTHESIZE FIRST — write your analysis before doing more searches.

Your job is to determine which recommendation is better supported:

1. Verify each piece of evidence independently
2. Find cases where [OPTION A] outperforms [OPTION B] and vice versa
3. Identify the specific conditions under which each option is superior
4. Recommend which option is better FOR THESE SPECIFIC REQUIREMENTS, with evidence

Do not default to the more popular option. The popular option needs to EARN the
recommendation with better evidence, not better marketing.
```

## Consensus Guard Prompt

Use when all agents in a round converge on the same tool.

```
All research agents recommended [TOOL X] for [DOMAIN].

Your job is adversarial: find the strongest case AGAINST [TOOL X] and FOR an alternative.

1. What are [TOOL X]'s biggest weaknesses for these specific requirements?
2. What's the strongest alternative, and under what conditions would it win?
3. Are there use cases similar to ours where [TOOL X] failed or was replaced?
4. Is the recommendation based on benchmarks or on blog post volume?

If after this investigation [TOOL X] is genuinely best, say so with evidence.
But your default assumption should be skepticism, not confirmation.
```

## Claim Verification Prompt

Use for independent verification of specific claims.

```
Verify the following claim:
"[EXACT CLAIM TEXT]"

SYNTHESIZE FIRST — write what you find before doing more searches.

1. Find the original source (not a secondary reference)
2. What does the source actually say? (Direct quote if possible)
3. Is this from an independent source or the vendor?
4. Has this been replicated or confirmed by others?
5. What's the date of this information? Is it current?

Report: VERIFIED (2+ independent sources), SINGLE-SOURCE, VENDOR-ONLY, or UNVERIFIED.
```

## Negative Claim Verification

Use when an agent reports "X doesn't exist" or "X is not available." NEVER accept from a single agent.

**Do NOT dispatch another agent.** Verify locally:

```bash
# Model existence
pip index versions <package-name>
# or: HuggingFace API query

# Package existence
pip index versions <package-name>
# or: PyPI web search

# Import path verification
python -c "from X import Y"

# Version check
pip show <package-name>
```

**Evidence:** In real use, agents prematurely dismissed existing models and library versions as "not available." Local verification (HuggingFace API, official docs) reversed both. This pattern recurs — agents confidently report non-existence for things that exist.

Only accept negative claims after local verification produces the same conclusion.
