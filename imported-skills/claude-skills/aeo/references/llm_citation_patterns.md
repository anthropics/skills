# LLM Citation Patterns — How ChatGPT, Perplexity, Claude, Gemini, and Mistral Choose Sources

This reference answers one decision: **for a given query, how does each major LLM decide which sources to cite — and what does this imply for AEO strategy?**

## The Five Players (as of 2026)

| LLM | Citation Style | Retrieval Backend | Citation Density |
|---|---|---|---|
| **Perplexity** | Citation-first (inline footnotes) | Custom search + Brave + Bing | 5-15 per response |
| **ChatGPT (search mode)** | Citation-trailing (after-paragraph) | Bing API + internal | 3-8 per response |
| **Claude (browse mode)** | Citation-trailing | Brave + direct fetch | 3-10 per response |
| **Gemini (with grounding)** | Citation-trailing | Google search | 2-6 per response |
| **Mistral (with search)** | Citation-trailing | Brave + custom | 2-5 per response |

Perplexity is the **most aggressive citation-first** LLM and has been the standard-bearer for AEO discipline. Other LLMs follow with varying citation aggressiveness depending on the mode (default chat vs. search-augmented).

## Per-LLM Citation Behavior

### Perplexity

**Design intent:** "Answer engine" — citations are the product, not an afterthought.

**Selection heuristics observed:**

1. Recency-weighted for time-sensitive queries (news, prices, breaking events)
2. Authority-weighted for evergreen queries (definitions, methodology, comparisons)
3. Diversity-weighted: tends to cite 3-7 sources from different domains
4. Structured-data-weighted: prefers sources with clear schema.org markup

**Implications:** Schema.org structured data is the highest-leverage AEO investment for Perplexity citation.

### ChatGPT (search mode)

**Design intent:** Conversational with grounding when explicit search is invoked.

**Selection heuristics:**

1. Retrieval pipeline favors Bing's top-10 results
2. Citation pruning step: keeps sources that contributed unique facts to the response
3. Author-credential boost: sources with bylined experts cited more often
4. Long-form preference: 1500+ word articles more likely to be cited than short pages

**Implications:** Write longer, more comprehensive pieces; ensure SEO foundation (because Bing retrieval is the gating function).

### Claude (browse mode)

**Design intent:** Honest about limitations; cites primary sources preferentially.

**Selection heuristics:**

1. Brave Search retrieval (no Google/Bing dependency)
2. Quality classifier weights primary sources heavily over aggregators
3. Cites less promiscuously than Perplexity — quality over quantity
4. Strong preference for dated content (knows training cutoff, prefers post-cutoff sources)

**Implications:** Primary-source positioning + dated examples + corrections policy are critical for Claude citation.

### Gemini (with grounding)

**Design intent:** Google-native; inherits Google ranking signals directly.

**Selection heuristics:**

1. Google Search index as primary retrieval
2. Inherits Google's E-E-A-T rubric
3. AI Overview integration: cites top featured snippets + Wikipedia + .gov/.edu heavily
4. Sometimes cites Reddit/forums for first-person discussion topics

**Implications:** Win at SEO and you win at Gemini citations. Schema.org for FAQPage + HowTo gives extra Google AI Overview boost.

### Mistral (with search)

**Design intent:** EU-focused; favors recent + European sources for region-relevant queries.

**Selection heuristics:**

1. Brave Search retrieval (similar to Claude)
2. Regional weighting: .eu/.de/.fr domains preferred for EU-context queries
3. Multilingual citation: more likely to cite non-English sources than US-centric LLMs

**Implications:** If targeting EU audiences, ensure European authority signals (.eu domain, GDPR/DSGVO mentions, EU regulator references).

## Citation Correlation Across LLMs

Industry data (Search Engine Land 2024-2026 longitudinal studies) shows ~73% citation overlap across the 5 major LLMs on the same query. The shared signals:

- Schema.org structured data presence
- E-E-A-T composite score (proxied by author bylines + credentials + corrections policy)
- HTTPS + accessibility + page speed
- Source authority (backlink graph)
- Citation density within the content itself

Optimizing for one major LLM typically helps all. The exception: Perplexity's structured-data weighting is so strong that Perplexity-specific gains (schema markup) often outpace gains elsewhere.

## What Triggers Citation (Empirical)

**High-citation triggers:**

1. **Verifiable facts with sources** — "47% of Fortune 500 use X [source]"
2. **Comparison tables** — "Tool A vs Tool B vs Tool C"
3. **Definitions** — clearly delineated "X is..."
4. **Step-by-step processes** — HowTo schema + ordered lists
5. **Recent stats with dates** — "as of Q1 2026..."

**Low-citation triggers (avoid):**

1. **Pure opinion without evidence** — LLMs prefer attributed facts
2. **Unverifiable claims** — "many people believe..." without count or source
3. **Promotional/marketing language** — "the best", "industry-leading" without metrics
4. **Generic boilerplate** — duplicate content patterns penalized
5. **Listicles without substance** — "10 ways to..." that aren't actually 10 distinct ways

## Time-Sensitivity of Citation

Citation distribution varies wildly by query type:

| Query type | Recency weight | E-E-A-T weight | Schema weight |
|---|---|---|---|
| Definition ("what is X") | Low | High | Medium |
| News ("latest in X") | Critical | Medium | Low |
| Comparison ("X vs Y") | Medium | High | Critical |
| HowTo ("how to do X") | Medium | High | Critical |
| Stats ("how many...") | High | High | Medium |
| Opinion ("should I...") | Low | Critical | Low |

This matters: don't waste effort on schema markup for opinion content. Don't waste effort on credentials for news content. Match optimization to query type.

## Operational Discipline

When optimizing for cross-LLM citation:

- [ ] Make E-E-A-T signals consistent (author byline + credentials in all the right places)
- [ ] Add schema.org markup (Article + FAQPage + HowTo where applicable)
- [ ] Include 5+ verifiable factual claims with primary-source citations
- [ ] Date your content and update timestamps when content changes
- [ ] Add a corrections policy link in the footer
- [ ] For high-citation queries, include a comparison table where natural
- [ ] Track which LLMs cite which queries via `citation_tracker.py` over 4+ weeks

When competing for a specific LLM:

- **Perplexity**: maximize schema + structured data + diverse external links
- **ChatGPT**: maximize length + comprehensiveness + traditional SEO
- **Claude**: maximize primary-source positioning + corrections discipline
- **Gemini**: maximize traditional SEO + Google-native signals
- **Mistral**: regional authority for EU-context queries

## Citations (7 sources)

1. **Perplexity AI — Public documentation on retrieval architecture (2023-2025).** Source for Perplexity's citation-first design and its weighting heuristics. Establishes the structured-data-prefer signal as a primary leverage point. https://www.perplexity.ai/

2. **OpenAI — ChatGPT search documentation (developer + product blog 2024-2026).** Source for ChatGPT's Bing-based retrieval pipeline + citation pruning behavior in search mode. https://platform.openai.com/docs/

3. **Anthropic — Claude browse mode + tool use documentation (2024-2026).** Source for Claude's Brave-based retrieval and primary-source preference. https://docs.anthropic.com/

4. **Google AI — Gemini grounding + AI Overviews architecture (developer blog 2024-2026).** Source for Gemini's Google-Search-native retrieval and its inheritance of Google's ranking signals. https://ai.google.dev/

5. **Mistral AI — Search integration documentation (2024-2026).** Source for Mistral's Brave-based retrieval + regional weighting characteristics. https://docs.mistral.ai/

6. **Search Engine Land — "How LLMs cite sources" longitudinal coverage (2024-2026).** Source for the cross-LLM citation correlation data (~73% overlap on same queries) and the empirical citation triggers analysis. https://searchengineland.com/

7. **BrightEdge — "Generative engine optimization" (industry research 2024-2026).** Source for the empirical citation pattern analysis across thousands of queries. Establishes the time-sensitivity matrix (which signals matter for which query types).

8. **SEMrush + Ahrefs — AEO research reports (2024-2026).** Source for industry-wide citation tracking + the per-LLM citation share studies. Both publish quarterly reports tracking which domains get cited most across major LLMs.
