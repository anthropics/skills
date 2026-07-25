# E-E-A-T Methodology for Answer Engine Optimization

This reference answers one decision: **what signals do LLMs use to decide whether a piece of content is citable as an authoritative source?** The answer is the **E-E-A-T framework** — Experience, Expertise, Authoritativeness, Trustworthiness — adapted for AI-citation contexts.

## Origin: Google → LLMs

E-A-T originated as Google's Quality Rater Guidelines criterion in 2014. In December 2022, Google added the second "E" (Experience) to acknowledge first-hand demonstrable knowledge. With the rise of LLM-powered AI Overviews and citation-driven search, E-E-A-T has effectively become **the** ranking signal — both for SEO and AEO.

LLM citation algorithms inherit heavily from search retrieval: the same Google indexing infrastructure that powers AI Overviews uses E-E-A-T as a primary signal. RAG-based assistants (ChatGPT browse, Perplexity, You.com) also weight E-E-A-T signals because their retrieval layers train on Google's signals and on similar quality-rated corpora.

## The Four Dimensions

### Experience

**Definition:** Demonstrated first-hand experience with the subject matter.

**LLM-detectable signals:**

- First-person verbs ("we ran", "we tested", "I implemented")
- Dated examples ("in 2026, our team observed...")
- Specific case studies with metrics
- Photos, videos, screenshots from actual implementation
- Process narratives ("step 3 took us 6 hours longer than expected because...")

**Industry weight:**
- Healthcare: ⚠️ critical (must be from licensed practitioner)
- Finance: ⚠️ critical (must be from credentialed advisor)
- SaaS: medium (case studies + product manager bylines)
- Travel/lifestyle: high (the entire point)

### Expertise

**Definition:** Verifiable subject-matter credentials of the author or contributor.

**LLM-detectable signals:**

- Author bio with credentials (PhD, MD, CFA, CPA, JD, etc.)
- Author page / portfolio of related work
- Citations to peer-reviewed sources
- Technical depth (specific frameworks, technical terms used correctly)
- Editorial review credit ("medically reviewed by", "fact-checked by")

**Industry weight:**
- Healthcare, finance, legal: ⚠️ critical
- B2B SaaS: high (technical depth visible to LLM)
- Consumer content: medium (varies by category)

### Authoritativeness

**Definition:** External recognition of the content / author / publisher as a trusted source.

**LLM-detectable signals:**

- Backlinks from authority domains (Wikipedia, .edu, .gov, established publications)
- Author cited by other authoritative sources
- Schema.org structured data (Article + Author + Publisher)
- Featured snippets, citations in news articles
- Brand mentions across the open web

**Industry weight:**
- Universal: high
- News + politics + medicine: critical (anti-misinformation)

### Trustworthiness

**Definition:** Indicators that the content + publisher operate transparently and reliably.

**LLM-detectable signals:**

- HTTPS (table stakes)
- Contact information clearly visible
- Editorial policy + corrections process
- Privacy policy, terms of service
- Transparent ownership / "About us"
- Industry disclaimers (financial: "not investment advice"; medical: "consult a professional")
- Update timestamps on time-sensitive content

**Industry weight:**
- Healthcare, finance, legal: ⚠️ critical (disclaimers, qualifications)
- E-commerce: high (returns, contact, reviews)
- Universal: high

## How LLM Citation Differs From Google Ranking

| Aspect | Google Ranking | LLM Citation |
|---|---|---|
| **Goal** | Get clicks | Get cited as authoritative source |
| **E-E-A-T weight** | Important | Primary signal |
| **Backlinks** | Critical | Important but not dominant |
| **Keywords** | Critical | Minimal (LLMs extract topic semantically) |
| **Structured data** | Helpful | Critical (LLMs prefer structured facts) |
| **Recency** | Variable | Important for citations of new info |
| **Citation density** | Optional | Critical (more verifiable claims → more citable) |

The key insight: **LLMs are not searching keywords**. They are extracting facts and selecting the most authoritative-looking source to attribute. Optimization for LLM citation is therefore E-E-A-T-first, keyword-secondary.

## Industry-Specific E-E-A-T Thresholds

Different industries have different YMYL ("Your Money or Your Life") implications. Healthcare and finance content with low E-E-A-T can cause real-world harm — Google rates this content most strictly, and LLMs inherit that rigor.

| Industry | Min Composite | Rationale |
|---|---|---|
| Healthcare | 85 | Direct health implications |
| Finance | 85 | Real financial decisions |
| Legal | 85 | Legal jeopardy if misapplied |
| Education | 75 | Learning outcomes depend on accuracy |
| B2B SaaS | 70 | Business decisions, lower personal risk |
| Marketing/Media | 70 | Editorial reputation |
| E-commerce | 65 | Product reviews, lower individual risk |

Content for high-YMYL topics that scores below the threshold is unlikely to be cited regardless of other AEO signals.

## Operational Discipline

When auditing for E-E-A-T:

- [ ] Run `aeo_audit.py --input <file> --industry <industry>` for deterministic baseline
- [ ] Verify author byline includes credentials (or "by Editorial Team" → flag)
- [ ] Confirm schema.org markup for Article + Author + Publisher
- [ ] Check primary-source citations for any factual claim
- [ ] Confirm HTTPS, contact, corrections, disclosure footer
- [ ] For YMYL topics: confirm industry-specific disclaimer present
- [ ] For dated content: verify last-updated timestamp visible

When fixing low E-E-A-T:

- Lowest-scoring dimension first (auditor prioritizes top fixes)
- Don't add fake signals (LLMs detect inconsistency between claim and signal)
- Real first-person evidence beats synthesized authority
- Schema.org markup only for verifiable claims (mark up an FAQ answer → that answer must actually be in the page)

## Anti-Patterns

### Fabricated credentials

Adding "PhD" to a byline without actual degree. LLMs cross-reference authors against external mentions (LinkedIn, Wikipedia, academic databases). Fabrication produces inconsistency that downranks the source.

### Schema spam

Marking up content that doesn't match the schema. False FAQPage schema (the marked-up questions don't appear in the page text) gets filtered.

### Authority laundering

Linking out to authority domains in the hope the link confers authority. LLMs measure inbound authority, not outbound.

### Pure AI-generated content with no human review

Generic LLM-generated content is detectable through low semantic distinctiveness. The signal: average vocabulary distance to other LLM outputs. RAG retrieval algorithms specifically deprioritize this content because it doesn't add value relative to the LLM's own knowledge.

### Optimizing one LLM at expense of others

Citation distributions are highly correlated across LLMs because they share training corpora. Optimize for the shared E-E-A-T signals, not per-LLM hacks.

## Citations (7 sources)

1. **Google Search Central — Quality Rater Guidelines (December 2022, current ed.).** Source for the E-E-A-T framework as Google's official authority signal. The December 2022 update added "Experience" alongside the original E-A-T. https://developers.google.com/search/docs/fundamentals/creating-helpful-content

2. **Marie Haynes — "E-E-A-T and YMYL" (multi-year longitudinal analysis, 2022-2026).** Source for industry-specific E-E-A-T thresholds + YMYL framing. Haynes's case studies establish the empirical correlation between E-E-A-T signals and ranking + citation outcomes across healthcare, finance, legal.

3. **Lily Ray — "AEO is the new SEO" (Amsive blog + industry talks, 2024-2026).** Source for the AEO-vs-SEO distinction + the citation-density discipline. Ray's analyses of which sources Perplexity and ChatGPT cite established that structural factors (lists, tables, schema) outweigh keyword density.

4. **Schema.org — Article + FAQPage + HowTo + Person + Organization specifications.** Source for the structured data conventions that LLMs treat as direct facts. Specifically, Article.author + Person.alumniOf + Organization.sameAs provide the cross-reference fabric that lets LLMs verify expertise claims. https://schema.org/

5. **Perplexity AI — Citation behavior + RAG architecture (technical blog 2023-2025).** Source for how a citation-first LLM weighs source authority. Perplexity publicly documents that it weights source authority (E-E-A-T proxy) higher than recency for most queries, except for explicitly time-sensitive topics.

6. **Anthropic — Claude's web browsing + citation patterns (technical documentation 2024-2026).** Source for Claude's citation discipline when browsing the live web. Anthropic documents that Claude prefers to cite primary sources, dated content, and identifies and deprioritizes low-authority aggregators. https://docs.anthropic.com/

7. **OpenAI — ChatGPT search + retrieval documentation (developer blog 2024-2026).** Source for ChatGPT's grounded retrieval behavior. ChatGPT's search-augmented responses use a quality classifier inheriting from search-engine retrieval signals — overlapping substantially with Google's E-E-A-T rubric. https://platform.openai.com/docs/

8. **Search Engine Land — "How LLMs choose sources to cite" (industry coverage 2024-2026).** Source for the cross-LLM correlation in citation choices. The trade publication's longitudinal coverage establishes that ChatGPT, Perplexity, Claude, and Gemini cite overlapping source sets ~73% of the time on the same query — implying shared underlying signals (E-E-A-T). https://searchengineland.com/
