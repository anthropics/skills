---
name: aeo
description: "Answer Engine Optimization (AEO) skill — optimize content to be cited by AI language models (ChatGPT, Perplexity, Claude, Gemini, Mistral) as authoritative sources. Distinct from SEO — AEO optimizes for citation in LLM-generated responses, not search rankings. Use when planning content for AI-first search audiences, auditing existing content for E-E-A-T signals, tracking which pages get cited by which LLMs, or building a citation-friendly content strategy. Triggers — 'AEO audit', 'optimize for ChatGPT', 'get cited by Perplexity', 'LLM citation strategy', 'answer engine optimization', 'content for AI search', 'E-E-A-T audit'. Output is a markdown audit report (default) or JSON for pipeline integration. Stdlib-only Python tools."
---

# Answer Engine Optimization (AEO)

**Get your content cited by ChatGPT, Perplexity, Claude, Gemini, and Mistral as the authoritative source.**

AEO is the practice of optimizing content for **citation** in LLM-generated responses — distinct from SEO, which optimizes for search rankings. This skill audits, optimizes, and tracks AEO performance.

## Distinct From SEO

| | SEO | AEO |
|---|---|---|
| **Optimizes for** | Click-through rankings | Being cited as authoritative source |
| **Audience** | Humans browsing search results | LLMs answering questions |
| **Success metric** | Position 1-10, organic traffic | Citation count across LLMs |
| **Key signals** | Backlinks, keywords, page speed | E-E-A-T, structured data, factual density |
| **Update cadence** | Weeks-to-months | Days-to-weeks (LLM training cycles) |

Both can coexist — the same content can rank #1 on Google AND get cited by Perplexity. But the techniques differ: SEO rewards keyword density + backlinks; AEO rewards primary-source signals + structured facts.

## When To Use

- Planning a new content piece for an AI-first audience
- Auditing existing content for E-E-A-T gaps before AI Overview rollout
- Tracking which pages get cited by which LLM (citation ledger)
- Researching what queries LLMs cite sources for (vs. what they answer from training)
- Benchmarking against competitors' citation rates
- Building a long-term AEO strategy aligned with traditional SEO

## When NOT To Use

- Pure click-through SEO without LLM-citation intent — use `marketing-skill/skills/seo-audit` instead
- Brand-voice content with no factual claims — citations require facts to cite
- Content for a topic where LLMs already have strong training signal (e.g., elementary math) — citation upside is minimal
- Time-sensitive content (breaking news) — LLM training lag means citations come months later

## Core Capabilities

### 1. Content audit + E-E-A-T scoring

The auditor (`aeo_audit.py`) scores content across 4 dimensions:

- **Experience**: First-person evidence, dated examples, case studies, "We ran X in 2026" claims
- **Expertise**: Author bio, credentials, citations to peer-reviewed sources, technical depth
- **Authoritativeness**: External backlinks from authority domains, schema.org markup, structured data
- **Trustworthiness**: HTTPS, contact info, transparent corrections, factual density (number of verifiable claims per 1000 words)

Composite score 0-100 with per-dimension breakdown. Output: markdown report with specific fix recommendations.

### 2. Content optimization

The optimizer (`aeo_optimizer.py`) generates AEO-improved variants:

- **Structure rewrite** — H2/H3 hierarchy optimized for LLM parsing
- **Citation density boost** — adds `[1]`-style references with sources
- **Schema injection** — generates JSON-LD for FAQ, HowTo, Article schemas
- **Fact-first lede** — moves verifiable claims into the first 200 words

Three modes: `conservative` (touch <10% of words), `balanced` (touch <30%), `aggressive` (rewrite for maximum AEO).

### 3. Citation tracking

The tracker (`citation_tracker.py`) maintains a local ledger of citations:

- Manual entry: paste a citation found in ChatGPT/Perplexity/Claude/Gemini output
- Track which URL, which LLM, which query, what date
- Compute per-page citation count, citation velocity, LLM coverage
- Export to CSV for reporting

Stores in `~/.aeo-data/citations.json` (local, no telemetry).

## References

- `references/aeo_eeat_canon.md` — E-E-A-T methodology, industry thresholds, anti-patterns
- `references/llm_citation_patterns.md` — per-LLM citation selection heuristics (Perplexity, ChatGPT, Claude, Gemini, Mistral)
- `references/aeo_vs_seo.md` — when to invest in AEO vs SEO vs both
- `references/bot_access_and_monitoring.md` — AI crawler robots.txt matrix (the prerequisite check: a blocked bot zeroes that platform), Google Search Console AI Overviews monitoring, manual testing protocols, citation-drop diagnostic (merged from the former `ai-seo` skill)
- `references/extractable_content_patterns.md` — 7 copy-ready block templates (definition, steps, table, FAQ, attributed stat, expert quote, summary box) that answer engines reliably extract (merged from the former `ai-seo` skill)

## Workflow

```
0. Pre-flight: bot access
   Check robots.txt against the crawler matrix in references/bot_access_and_monitoring.md
   → a blocked GPTBot/PerplexityBot/ClaudeBot/Google-Extended is the first fix, always

1. Audit existing content
   $ python3 scripts/aeo_audit.py --url https://example.com/blog/post
   → markdown report with composite score + 4-dimension breakdown

2. Apply optimization recommendations
   $ python3 scripts/aeo_optimizer.py --input post.md --mode balanced --output post-aeo.md
   → optimized variant with citations + schema + structural fixes

3. Publish + monitor
   $ python3 scripts/citation_tracker.py --action add --url https://example.com/blog/post \
       --llm perplexity --query "what is AEO" --date 2026-05-17
   → adds entry to local citations.json ledger

4. Report
   $ python3 scripts/citation_tracker.py --action report --url https://example.com/blog/post
   → per-page citation stats: count, LLMs, queries, velocity
```

## Configuration

The skill is industry-aware via per-run `--industry` flag. Supported: `saas`, `healthcare`, `finance`, `legal`, `ecommerce`, `b2b`, `media`, `education`.

Industry affects:
- **Authority signal requirements** — healthcare/finance need stricter source citations
- **Fact-checking rigor** — legal/healthcare flag unverifiable claims as critical
- **Citation style** — academic vs. trade-journal vs. blog conventions

Example:
```bash
python3 scripts/aeo_audit.py --url <url> --industry healthcare
# → stricter E-E-A-T thresholds; flags any health claim without primary citation
```

## Output Format

### Markdown audit report (default)

```markdown
# AEO Audit Report — [Page Title]

**URL:** https://example.com/blog/post
**Date:** 2026-05-17
**Industry:** saas
**Composite Score:** 72/100 (B+)

## Dimension Breakdown

| Dimension | Score | Verdict |
|---|---|---|
| Experience | 80/100 | Strong — first-person case study present |
| Expertise | 65/100 | Author bio missing credentials |
| Authoritativeness | 75/100 | 4 backlinks from authority domains |
| Trustworthiness | 68/100 | No corrections policy linked |

## Top 3 Fixes

1. Add author bio with credentials (Expertise +15)
2. Link to corrections policy from footer (Trustworthiness +12)
3. Inject FAQ schema for the 5 questions implicit in H2s (Authoritativeness +8)

## All Recommendations
[...]

## Audit Trail
[3-count of analysis steps, sources cited, time taken]
```

### JSON for pipelines

```bash
python3 scripts/aeo_audit.py --url <url> --output json
```

Returns full structured data for integration with content management workflows.

## Industry-Specific E-E-A-T Thresholds

| Industry | Min Composite | Critical Signals |
|---|---|---|
| Healthcare | 85 | Medical reviewer byline, peer-reviewed citations, FDA disclosure |
| Finance | 85 | Author CFA/CPA credentials, "not investment advice" disclaimer, dated examples |
| Legal | 85 | Jurisdiction disclosed, attorney bio, "not legal advice" disclaimer |
| SaaS | 70 | Product manager byline, case study with metrics, ROI calculator |
| E-commerce | 65 | Product reviews aggregated, return policy, schema.org Product |
| B2B | 70 | Industry analyst quotes, customer logos, ROI data |
| Media | 70 | Editorial policy, fact-check link, original reporting |
| Education | 75 | Instructor bio, learning outcomes, accreditation if applicable |

## Anti-Patterns Rejected

- **Keyword stuffing for AI** — LLMs already extract topic from semantics; keyword density doesn't boost citation likelihood
- **Pure AI-generated content with no human review** — generic LLM output gets de-prioritized by RAG retrieval algorithms looking for distinctive signal
- **Citation farms / link wheels** — modern LLM RAG penalizes low-authority linked networks
- **Schema spam** — false or unverifiable schema.org claims get filtered; only mark up real, verifiable claims
- **Optimizing for one LLM at expense of others** — citation distributions are highly correlated across major LLMs because they share training data sources; optimize for the shared signals (E-E-A-T) not per-LLM hacks
- **Ignoring SEO entirely** — AEO citations often originate from sources that already rank well organically; AEO and SEO are complements, not substitutes

## Dependencies

- **stdlib-only** for all 3 scripts — no `pip install` required
- **Optional**: `requests` + `beautifulsoup4` if `--url` mode used (otherwise pass markdown via `--input` for file-based audits)
- **Optional**: any LLM API key for `query_research` mode (currently scaffold-only — full LLM-driven query research is roadmap)

## Storage

All data is local-first:
- `~/.aeo-data/citations.json` — citation ledger
- `~/.aeo-data/patterns.json` — success patterns library
- `~/.aeo-data/audits/<hash>.md` — saved audit reports

No telemetry. No cloud sync. Export to CSV anytime via `citation_tracker.py --action export`.

## Trigger Phrases

- "AEO audit", "AEO check"
- "optimize for ChatGPT / Perplexity / Claude / Gemini"
- "get cited by [LLM]"
- "LLM citation strategy"
- "answer engine optimization"
- "content for AI search"
- "E-E-A-T audit"
- "track AI citations"
- "schema for AI"

## Related Skills

- `marketing-skill/skills/seo-audit` — traditional click-through SEO
- `marketing-skill/skills/programmatic-seo` — template-driven SEO at scale
- `marketing-skill/skills/content-strategy` — broader content planning
- `marketing-skill/skills/copywriting` — voice + tone
- `marketing-skill/skills/schema-markup` — structured data implementation

---

**Version:** 2.7.3
**Source:** Ported from [`alirezarezvani/aeo-box`](https://github.com/alirezarezvani/aeo-box) (`answer-engine-optimization/` skill, 2,464 LOC across 9 modules). This port distills the 9-module Python toolkit into 3 stdlib CLI tools per the claude-skills convention; preserves the E-E-A-T scoring methodology, citation-tracking schema, and industry-aware thresholds verbatim.
**License:** MIT (matches upstream + this repo).
