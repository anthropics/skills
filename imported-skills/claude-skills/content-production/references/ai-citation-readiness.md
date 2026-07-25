# AI Citation Readiness

How to optimize content so AI platforms (Perplexity, ChatGPT, Google AI Overviews, Claude) cite your pages in their answers. This is the emerging "second SEO" — ranking in AI-generated answers, not just Google blue links.

## Why this matters

AI answer engines extract passages from web content and present them as citations. Content that's structured for extraction gets cited more often. This is independent of traditional SEO — a page can rank #1 on Google but never get cited by AI because it's not formatted for extraction.

## The 5 AI citation signals

### 1. Answer-first paragraphs

The first 40-60 words after each H2 must directly answer the section's implied question. AI platforms extract these opening passages as citation candidates.

**Bad (builds up to the answer):**
```
There are many factors to consider when choosing a framework. 
Performance, ecosystem, and learning curve all play a role. 
After evaluating several options, React remains the best choice
for most teams in 2026.
```

**Good (answer first):**
```
React is the best frontend framework for most teams in 2026. 
It has the largest ecosystem (4.2M weekly npm downloads), 
the most hiring demand, and the best balance of performance 
and developer experience.
```

### 2. Passage-level citability

Structure content in self-contained 120-180 word chunks that make sense when extracted in isolation. Each chunk should:
- State a clear claim
- Provide supporting evidence
- Cite a source
- Work as a standalone answer

### 3. Entity clarity

Use full entity names on first reference, then consistent abbreviations. AI models need unambiguous entity references to match queries.

**Bad:** "The framework's new feature improves DX significantly."
**Good:** "React 19's Server Components improve developer experience (DX) by reducing client-side JavaScript by 40%."

### 4. Q&A formatting

Include explicit question-and-answer patterns. These directly match how users query AI platforms.

```markdown
## How much does React hosting cost?

React hosting ranges from $0 (Vercel/Netlify free tier) to $20-50/month
for production apps with custom domains and CI/CD. Static sites built
with React are effectively free to host.
```

### 5. Freshness signals

AI platforms prefer recently updated content. Include:
- `dateModified` in JSON-LD or frontmatter
- "Last updated: [date]" visible on page
- Update frequency: evergreen content should be refreshed every 6-12 months

## Scoring for content_quality_gates.py

```
AI Citation Readiness checks:
  Answer-first paragraphs at H2     → pass/fail (check first 60 words)
  Passage length 120-180 words      → pass/warn/fail
  Entity clarity (no ambiguous "it") → pass/warn (heuristic)
  Q&A section present               → pass/fail
  Freshness signal present           → pass/fail
```

## What NOT to do

- Don't stuff FAQ schema on every page — use it only when genuine Q&A exists
- Don't write for extraction at the expense of human readability
- Don't fabricate statistics to make passages more "citable"
- Don't keyword-stuff entity names — use them naturally
