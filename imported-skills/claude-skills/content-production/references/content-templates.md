# Content Templates — Auto-Selection Guide

12 content templates with selection logic. The LLM should detect topic intent and recommend the right template before writing.

## Selection matrix

| User intent | Template | Target length | Best for |
|---|---|---|---|
| "How do I..." | How-to guide | 1,500-3,000 words | Step-by-step processes |
| "Best X for Y" / "Top N" | Listicle | 2,000-4,000 words | Comparison/curation |
| "X increased revenue by Y%" | Case study | 1,500-2,500 words | Social proof, sales enablement |
| "X vs Y" | Comparison | 2,000-3,500 words | Decision-stage buyers |
| "Complete guide to X" | Pillar page | 3,000-5,000 words | Topical authority hub |
| "Is X worth it?" | Product review | 1,500-2,500 words | Affiliate, purchase intent |
| "The future of X" | Thought leadership | 1,200-2,000 words | Brand authority |
| "Experts say about X" | Roundup | 2,000-3,500 words | Link building, authority |
| "How to build X step by step" | Tutorial | 2,000-4,000 words | Technical audiences |
| "What happened with X" | News analysis | 800-1,500 words | Timeliness, trending topics |
| "[Data] shows that..." | Data research | 1,500-3,000 words | Original research, link magnets |
| "What is X?" | FAQ / knowledge base | 1,000-2,000 words | Informational, featured snippets |

## Template structures

### How-to guide
```
H1: How to [Action] [Object] (in [Timeframe])
H2: What You'll Need / Prerequisites
H2: Step 1: [First action]
H2: Step 2: [Second action]
...
H2: Common Mistakes to Avoid
H2: FAQ
```

### Listicle
```
H1: [N] Best [Category] for [Audience] in [Year]
H2: Quick Comparison Table
H2: 1. [Item] — Best for [Use Case]
  H3: Key Features | H3: Pricing | H3: Who It's For
H2: 2. [Item] — Best for [Use Case]
...
H2: How We Evaluated
H2: FAQ
```

### Case study
```
H1: How [Company] [Achieved Result] with [Method/Product]
H2: The Challenge
H2: The Approach
H2: The Results (with metrics)
H2: Key Takeaways
H2: What's Next
```

### Comparison
```
H1: [X] vs [Y]: Which Is Better for [Use Case]?
H2: Quick Verdict (answer-first)
H2: Comparison Table
H2: [X] — Strengths and Weaknesses
H2: [Y] — Strengths and Weaknesses
H2: When to Choose [X]
H2: When to Choose [Y]
H2: FAQ
```

### Pillar page
```
H1: The Complete Guide to [Topic] ([Year])
H2: What Is [Topic]?
H2: Why [Topic] Matters
H2: [Subtopic 1] (links to cluster article)
H2: [Subtopic 2]
...
H2: Getting Started
H2: FAQ
H2: Further Reading (internal links to cluster)
```

## Auto-selection logic

```
IF user says "how to" or "step by step" → How-to guide
IF user says "best" or "top" + number → Listicle
IF user provides metrics/results data → Case study
IF user says "vs" or "compare" → Comparison
IF user says "complete guide" or "everything about" → Pillar page
IF user says "review" or "worth it" → Product review
IF user asks "what is" or implies definition → FAQ / knowledge base
IF user provides original data → Data research
IF user mentions recent event → News analysis
ELSE → ask user to clarify intent, suggest 2-3 options
```

## Quality checklist (applies to all templates)

- [ ] Answer-first paragraph at every H2
- [ ] Title 50-60 characters
- [ ] Meta description 150-160 characters
- [ ] No heading skips (H1→H2→H3 only)
- [ ] All statistics sourced
- [ ] All images have alt text
- [ ] Internal links ≥ 3
- [ ] External links ≥ 2 (to authoritative sources)
- [ ] CTA present (but not self-promotional beyond 1 mention)
