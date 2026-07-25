# Deterministic Classification — Why Keyword Beats LLM-Reasoned For Routing

This reference answers one decision: **should the routing classifier use deterministic keyword matching or LLM reasoning over the query?** The answer is **deterministic keyword matching** for query-routing purposes, with LLM reasoning reserved for cases where keyword matching has genuinely exhausted the signal space.

## The Trade-Off Spectrum

| Approach | Latency | Cost | Determinism | Debuggability | Coverage of fuzzy intent |
|---|---|---|---|---|---|
| **Keyword + intent signals** (this skill) | <1ms | $0 | 100% | High (signals named explicitly) | Low |
| **Embedding similarity to specialist descriptions** | ~10-100ms | Cents/100K queries | High (deterministic given embeddings) | Medium (need to inspect cosine scores) | Medium |
| **LLM reasoning over query + specialist list** | ~500ms-2s | ~$0.001-0.01/query | Low (same query → varied outputs) | Low (prompt-dependent) | High |

The trade-off: as you move down the table, coverage of fuzzy intent improves, but latency, cost, and unpredictability all worsen. The right choice depends on how predictable + auditable the routing needs to be.

## For Query Routing, Determinism Wins

Routing is **fundamentally a control-flow decision**: it determines which subsystem runs next. Like any control-flow decision in software, predictability + auditability are first-order properties.

Compare to other deterministic control-flow systems:

- **Compilers** use deterministic lexer + parser, not LLMs.
- **Routers** (network sense) use deterministic CIDR matching, not LLMs.
- **CI/CD systems** use deterministic file-pattern triggers, not LLMs.
- **Linters + formatters** use deterministic AST-walking, not LLMs.

These are all systems where users need to predict + debug behavior. LLM-reasoned routing in any of them would be a regression. Same applies to skill routing.

## The Bracketed-Placeholder Anti-Pattern

A common mistake when building keyword classifiers: using bracketed placeholders as signals.

**Wrong:**
```python
SIGNALS = {
  dossier: ["dossier on [company]", "background check on [person]", "research [entity]"]
}
```

**Why wrong:** the "research [entity]" pattern collapses to "research" as a substring match, which matches every research request ever. The signal over-triggers + breaks the classifier.

**Right:**
```python
SIGNALS = {
  dossier: ["dossier on", "background check", "background on", "competitor research"]
}
```

**Why right:** verb-noun pairs ("dossier on", "background on", "competitor research") are specific to dossier intent. Generic "research X" stays in fallback territory until paired with a specialist-specific noun.

This is the post-PR-#657-audit lesson encoded as a hard rule.

## What Counts As A "Signal"

A signal is a **case-insensitive literal phrase (multi-word substring)** that, when present in the user's question, indicates a specialist domain. Good signals are:

- **Specific enough** that they don't appear in unrelated queries (good: "literature review", bad: "research")
- **Common enough** that users actually say them (good: "due diligence", bad: "actuarial diligence assessment framework")
- **Diverse enough** to cover surface variations (good: "lit review" + "literature review" + "litreview"; bad: only one form)
- **Verb-noun-paired** when the noun alone is ambiguous (good: "dossier on" + "background on"; bad: just "company name")

## Confidence Thresholds

The skill commits to a specialist at **≥2 signals** for two reasons:

1. **2 signals reliably indicate intent.** "PICO + meta-analysis" doesn't show up in unrelated queries.
2. **1 signal isn't strong enough.** "PICO" alone might be a clinical question, a syllabus question, or a litreview question. The second signal distinguishes.

The single-weak-match exception (1 signal + only one specialist with any score) handles the case where the user used a highly specific phrase that no other specialist's signals overlap with. "What's the FTO landscape" → only patent has any score → route to patent even though it's just 1 signal.

The "ask Q3 disambiguation" exception handles the case where multiple specialists each have score 1, OR no specialist has any score. Both indicate genuine ambiguity that the classifier can't resolve.

## What Goes Wrong With LLM-Reasoned Classification

### Non-determinism

Same query, different responses across invocations. User says "what are people saying about X" — sometimes routes to pulse, sometimes to dossier, sometimes to fallback. User can't develop intuition for the system.

### Cost

500ms-2s per classification × hundreds of routing decisions/day adds up. Deterministic classifier is sub-millisecond + free.

### Debuggability

When LLM routes "weirdly," there's no signal to inspect. With deterministic classification, the user sees "matched signals: PICO, meta-analysis" and understands why.

### Prompt drift

LLM classifier behavior changes when the underlying model version changes. Deterministic classifier behavior is locked to the signals list. Auditable + reproducible.

## What Goes Wrong With Pure Keyword Classification

### Fuzzy intent

User says "I want to understand what the academic community thinks about CRISPR safety." No keyword matches litreview signals (no "PICO", no "systematic review", no "literature review"). Classifier punts to fallback even though litreview was the right answer.

**Mitigation:** Q3 disambiguation handles this. User picks "academic literature" → routes to litreview. The architecture's clarification path covers the fuzzy-intent case.

### Surface-form proliferation

Users say "lit review", "literature review", "litreview", "review the literature on", "review papers on", "look at the papers about", "what does the research say about" — that's 7 surface forms for the same intent. Signals list grows.

**Mitigation:** Cover the top-N surface forms (3-5 per specialist). Let Q3 handle the long tail.

### Polysemy

"Patent" could mean a legal patent (route to patent specialist) OR a medical term ("the symptoms are patent" = obvious). Keyword matching can't distinguish.

**Mitigation:** Multi-signal requirement reduces false positives. "Patent + prior art" is unambiguously patent intent.

## The Right Hybrid: Deterministic First, Clarify When Stuck

The architecture combines:

1. **Deterministic classification** for the high-confidence path (cheap + fast + predictable)
2. **Q3 disambiguation** for the genuinely-ambiguous path (LLM-free; user picks from 7 options)
3. **Fallback workflow** for the no-specialist path

This is strictly better than pure-LLM classification (cheaper, faster, more predictable) and strictly better than pure-keyword classification (handles fuzzy intent via Q3).

## Operational Discipline

When adding a new signal to the SIGNALS map:

- [ ] Verify the signal doesn't appear in queries that should route elsewhere (false positive check)
- [ ] Verify the signal does appear in queries that should route to this specialist (false negative check)
- [ ] Check for case-insensitivity (the matcher is case-insensitive, but be explicit)
- [ ] Avoid bracketed placeholders
- [ ] Use verb-noun pairs when the noun alone is ambiguous
- [ ] Document why this signal was added (which queries it covers)

When removing a signal:

- [ ] Check what queries previously routed via this signal
- [ ] Confirm they still route correctly (via another signal OR via Q3)
- [ ] Update the documentation

## Tooling

`scripts/classifier.py` implements the deterministic SIGNALS-matching algorithm. Use it; don't re-implement. It returns:

- `route_to`: specialist name OR "fallback"
- `confidence`: "high (N signals)" OR "weak (1 signal, single specialist)" OR "ambiguous"
- `matched_signals`: dict of specialist → list of matched phrases
- `scores`: dict of specialist → integer score

The CLI: `classifier.py --question "..." --output json`.

## Citations (7 sources)

1. **Aho, Sethi, Ullman — "Compilers: Principles, Techniques, and Tools" (Dragon Book, 1986).** Source for the deterministic lexer + parser as the canonical control-flow classifier in software. Compilers don't use LLMs for tokenization; routing shouldn't either.

2. **Cisco IOS — Access Control List (ACL) implementation guides.** Source for the deterministic CIDR-matching pattern in network routing. Predictability + auditability are first-order requirements; same applies to skill routing.

3. **Google Search Engineering blog — Query Classification (2020+).** Source for the production-grade query-classification pattern. Google uses deterministic signal matching as the first layer + LLM reasoning only for residual queries that signals miss. Same architecture as this skill (Q3 as the LLM-equivalent escape hatch).

4. **Mikolov et al. — "Distributed Representations of Words and Phrases" (Word2Vec, 2013).** Source for the embedding-similarity baseline. Embeddings are an intermediate point between keywords + LLM reasoning; this skill chooses keywords for cost + determinism reasons but acknowledges embedding-similarity as a valid alternative.

5. **Karpathy, Andrej — "Software 2.0" (blog post, 2017).** Source for the framing that not everything should be ML. Deterministic systems (compilers, routers, type checkers) remain superior for control-flow decisions even in the LLM era. https://karpathy.github.io/2017/11/11/software-2-0/

6. **Anthropic — Tool Use + Function Calling documentation.** Source for the production pattern of LLM-routes-to-deterministic-tool: the LLM decides intent at the top level, then deterministic tools handle the actual work. Same shape as this skill (intake → deterministic classifier → specialist tool). https://docs.anthropic.com/

7. **NIST — "Information Retrieval Evaluation" (TREC reports).** Source for the canonical evaluation methodology for classifiers: precision + recall measured against held-out queries. Keyword classifiers reliably outperform LLM-reasoned classifiers on precision for domain-specific routing tasks. https://trec.nist.gov/
