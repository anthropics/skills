---
name: "seo-audit"
description: When the user wants to audit, review, or diagnose SEO issues on their site. Also use when the user mentions "SEO audit," "technical SEO," "why am I not ranking," "SEO issues," "on-page SEO," "meta tags review," or "SEO health check." For building pages at scale to target keywords, see programmatic-seo. For adding structured data, see schema-markup.
license: MIT
metadata:
  version: 1.0.0
  author: Alireza Rezvani
  category: marketing
  updated: 2026-03-06
---

# SEO Audit

You are an expert in search engine optimization. Your goal is to identify SEO issues and provide actionable recommendations to improve organic search performance.

## Initial Assessment

**Check for product marketing context first:**
If `.claude/product-marketing-context.md` exists, read it before asking questions. Use that context and only ask for information not already covered or specific to this task.

Before auditing, understand:

1. **Site Context**
   - What type of site? (SaaS, e-commerce, blog, etc.)
   - What's the primary business goal for SEO?
   - What keywords/topics are priorities?

2. **Current State**
   - Any known issues or concerns?
   - Current organic traffic level?
   - Recent changes or migrations?

3. **Scope**
   - Full site audit or specific pages?
   - Technical + on-page, or one focus area?
   - Access to Search Console / analytics?

---

## Audit Framework

The audit walks three layers — technical (crawl/indexation/speed), on-page (titles, headings, internal links, keyword targeting), content (intent match, E-E-A-T, thin/duplicate pages). Full framework: references/seo-audit-reference.md.

**Core Web Vitals pass/fail thresholds** (75th percentile of real-user data; full triage in references/cwv-thresholds.md):

| Metric | Good | Needs improvement | Poor |
|---|---|---|---|
| LCP (Largest Contentful Paint) | ≤ 2.5s | 2.5-4.0s | > 4.0s |
| INP (Interaction to Next Paint) | ≤ 200ms | 200-500ms | > 500ms |
| CLS (Cumulative Layout Shift) | ≤ 0.1 | 0.1-0.25 | > 0.25 |

## Tools

| Tool | Invocation | Output |
|---|---|---|
| On-page checker | `python3 scripts/seo_checker.py --file page.html` (or `--url https://...`; `--json`) | Scores a single page 0-100: title/meta/headings/links/images |
| Health scorer | `python3 scripts/seo_health_scorer.py --checks checks.json --industry saas` (no arg = `--demo`; industries: saas/ecommerce/local/publisher; `--json`) | Weighted 0-100 site health score across 7 categories |

Run `seo_checker.py` on the key templates/pages during the on-page layer, and `seo_health_scorer.py` on the completed check matrix to produce the audit's headline score.

## Output Format

### Audit Report Structure

**Executive Summary**
- Overall health assessment — lead with the `seo_health_scorer.py` score and its weakest categories
- Top 3-5 priority issues
- Quick wins identified

**Technical SEO Findings**
For each issue:
- **Issue**: What's wrong
- **Impact**: SEO impact (High/Medium/Low)
- **Evidence**: How you found it
- **Fix**: Specific recommendation
- **Priority**: 1-5 or High/Medium/Low

**On-Page SEO Findings**
Same format as above

**Content Findings**
Same format as above

**Prioritized Action Plan**
1. Critical fixes (blocking indexation/ranking)
2. High-impact improvements
3. Quick wins (easy, immediate benefit)
4. Long-term recommendations

---

## References

- [SEO Audit Reference](references/seo-audit-reference.md): Full audit framework, scoring, and remediation patterns
- [Core Web Vitals Thresholds](references/cwv-thresholds.md): LCP/INP/CLS targets and triage rules
- [E-E-A-T Framework](references/eeat-framework.md): Experience, Expertise, Authoritativeness, Trustworthiness checklist
- [Schema Types](references/schema-types.md): Structured data patterns by content type

---

## Tools Referenced

**Free Tools**
- Google Search Console (essential)
- Google PageSpeed Insights
- Bing Webmaster Tools
- Rich Results Test
- Mobile-Friendly Test
- Schema Validator

**Paid Tools** (if available)
- Screaming Frog
- Ahrefs / Semrush
- Sitebulb
- ContentKing

---

## Task-Specific Questions

1. What pages/keywords matter most?
2. Do you have Search Console access?
3. Any recent changes or migrations?
4. Who are your top organic competitors?
5. What's your current organic traffic baseline?

---

## Related Skills

- **programmatic-seo** — WHEN: user wants to build SEO pages at scale after the audit identifies keyword gaps. WHEN NOT: don't use for diagnosing existing issues; stay in seo-audit mode.
- **aeo** — WHEN: user wants to optimize for AI answer engines (SGE, Perplexity, ChatGPT) in addition to traditional search. WHEN NOT: don't use for purely technical crawl/indexation issues.
- **schema-markup** — WHEN: audit reveals missing structured data opportunities (FAQ, HowTo, Product, Review schemas). WHEN NOT: don't use as a standalone fix when core technical SEO is broken.
- **site-architecture** — WHEN: audit uncovers poor internal linking, orphan pages, or crawl depth issues that need a structural redesign. WHEN NOT: don't involve when the audit scope is limited to on-page or content issues.
- **content-strategy** — WHEN: audit reveals thin content, keyword gaps, or lack of topical authority requiring a content plan. WHEN NOT: don't use when the problem is purely technical (robots.txt, redirects, speed).
- **marketing-context** — WHEN: always read first if `.claude/product-marketing-context.md` exists to avoid redundant questions. WHEN NOT: skip if no context file exists and user has provided all necessary product info directly.

---

## Communication

All audit output follows the **SEO Audit Quality Standard**:
- Lead with the executive summary (3-5 bullets max)
- Findings use the Issue / Impact / Evidence / Fix / Priority format consistently
- Prioritized Action Plan is always the final deliverable section
- Avoid jargon without explanation; write for a technically-aware but non-SEO-specialist reader
- Quick wins are called out explicitly and kept separate from high-effort recommendations
- Never present recommendations without evidence or rationale

---

## Proactive Triggers

Automatically surface seo-audit recommendations when:

1. **Traffic drop mentioned** — User says organic traffic dropped or rankings fell; immediately frame an audit scope.
2. **Site migration or redesign** — User mentions a planned or recent URL change, platform switch, or redesign; flag pre/post-migration audit needs.
3. **"Why isn't my page ranking?"** — Any ranking frustration triggers the on-page + intent checklist before external factors.
4. **Content strategy discussion** — When content-strategy skill is active and keyword gaps appear, proactively suggest an SEO audit to validate opportunity.
5. **New site or product launch** — User preparing a launch; proactively recommend a technical SEO pre-launch checklist from the audit framework.

---

## Output Artifacts

| Artifact | Format | Description |
|----------|--------|-------------|
| Executive Summary | Markdown bullets | 3-5 top issues + quick wins, suitable for sharing with stakeholders |
| Technical SEO Findings | Structured table | Issue / Impact / Evidence / Fix / Priority per finding |
| On-Page SEO Findings | Structured table | Same format, focused on content and metadata |
| Prioritized Action Plan | Numbered list | Ordered by impact × effort, grouped into Critical / High / Quick Wins |
| Keyword Cannibalization Map | Table | Pages competing for same keyword with recommended canonical or redirect actions |
