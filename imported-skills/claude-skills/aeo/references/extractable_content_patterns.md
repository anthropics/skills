# Extractable Content Patterns for AI Citability

Ready-to-use block templates for the content patterns answer engines reliably extract and cite. Folded in from the former `ai-seo` skill (merged into `aeo` 2026-06). Use these when `aeo_audit.py` flags low structure scores, and apply them via `aeo_optimizer.py` rewrite modes.

---

## Why Patterns Matter

AI systems don't read pages the way humans do. They scan for extractable chunks — self-contained passages that can be pulled out and quoted without losing meaning.

The patterns below are structured to be self-contained by design. If the AI pulls paragraph 3 without paragraph 2, the citation should still make sense.

---

## Pattern 1: Definition Block

**Used for:** "What is X" queries — the most common AI Overview trigger.

**Requirements:**
- First sentence: direct definition
- Second sentence: why it matters or how it works
- Third sentence (optional): example or context
- Placed in first 300 words of the page

**Template:**
```markdown
**[Term]** is [precise definition — what it is, what it does, who uses it]. 
[One sentence on why it matters or what problem it solves]. 
[Optional: one sentence example — "For example, a SaaS company might use X to..."].
```

**Example:**
```markdown
**Churn rate** is the percentage of customers who cancel or stop using a service within a given period, typically measured monthly or annually. It directly impacts recurring revenue — a 5% monthly churn means losing over half your customer base each year. For subscription SaaS, a healthy monthly churn rate is typically below 2%.
```

**Tips:**
- Bold the term on its first use
- Don't start with "In the world of..." or "When it comes to..."
- The definition should work even if the reader knows nothing about the topic

---

## Pattern 2: Numbered Steps (How-To)

**Used for:** "How to X" and "How do I X" queries.

**Requirements:**
- Numbered list (not bulleted)
- Each step starts with an action verb
- Each step is self-contained (can be cited alone)
- 5-10 steps maximum
- Pair with HowTo schema markup

**Template:**
```markdown
## How to [Task]

1. **[Verb phrase]** — [1-2 sentence explanation of this specific step]
2. **[Verb phrase]** — [1-2 sentence explanation]
3. **[Verb phrase]** — [1-2 sentence explanation]
4. **[Verb phrase]** — [1-2 sentence explanation]
5. **[Verb phrase]** — [1-2 sentence explanation]
```

**Example:**
```markdown
## How to Reduce SaaS Churn

1. **Define your activation event** — Identify the specific action that signals a user has experienced core product value. For Slack, it's 2,000 messages sent. For Dropbox, it's saving the first file.
2. **Instrument the activation funnel** — Add event tracking from signup to activation. Find the step where most users drop off — that's your highest-leverage point.
3. **Build a customer health score** — Combine login frequency, feature adoption, and support ticket volume into a single score. Customers below 40 get proactive outreach.
4. **Segment churn by cohort** — Not all churn looks the same. Compare churn rates by acquisition channel, onboarding path, and company size to find patterns.
5. **Interview churned customers** — The customers who left quietly are more valuable than the ones who complained. Call 10 churned accounts per month and ask what they were trying to accomplish.
```

**Schema markup (JSON-LD):**
```json
{
  "@context": "https://schema.org",
  "@type": "HowTo",
  "name": "How to [Task]",
  "step": [
    {"@type": "HowToStep", "name": "Step 1 name", "text": "Step 1 explanation"},
    {"@type": "HowToStep", "name": "Step 2 name", "text": "Step 2 explanation"}
  ]
}
```

---

## Pattern 3: Comparison Table

**Used for:** "X vs Y" and "best X for Y" queries.

**Requirements:**
- Header row with category names
- First column: feature or criterion
- Remaining columns: the things being compared
- Keep it focused — 5-10 rows maximum
- Don't try to cover everything; cover what matters most

**Template:**
```markdown
| Feature | [Option A] | [Option B] | [Option C] |
|---|---|---|---|
| [Criterion 1] | [Value] | [Value] | [Value] |
| [Criterion 2] | [Value] | [Value] | [Value] |
| [Criterion 3] | [Value] | [Value] | [Value] |
| Best for | [Audience A] | [Audience B] | [Audience C] |
| Pricing | [Range] | [Range] | [Range] |
```

**Tips:**
- Put the most important criteria first
- Use simple values — "Yes / No / Partial" beats long prose in cells
- Include a "Best for" row — AI systems use this for recommendation queries
- Add a sentence below the table summarizing the verdict: "X is best for teams that need A; Y is better when B matters more."

---

## Pattern 4: FAQ Block

**Used for:** Question-style queries, People Also Ask queries, voice search.

**Requirements:**
- Question phrased exactly as someone would ask it (natural language)
- Answer is complete in 2-4 sentences (no "read more in section 3")
- 5-10 FAQs per block
- Pair with FAQPage schema markup

**Template:**
```markdown
## Frequently Asked Questions

**What is [X]?**
[2-4 sentence complete answer]

**How does [X] work?**
[2-4 sentence complete answer]

**What's the difference between [X] and [Y]?**
[2-4 sentence complete answer]

**How much does [X] cost?**
[2-4 sentence complete answer]

**Is [X] right for [audience]?**
[2-4 sentence complete answer]
```

**Schema markup (JSON-LD):**
```json
{
  "@context": "https://schema.org",
  "@type": "FAQPage",
  "mainEntity": [
    {
      "@type": "Question",
      "name": "What is [X]?",
      "acceptedAnswer": {
        "@type": "Answer",
        "text": "Complete answer text here"
      }
    }
  ]
}
```

**Tips:**
- Write questions the way users actually type or speak them — use Google's "People Also Ask" as a source
- Answers should be complete without needing context from anywhere else on the page
- Don't start answers with "Great question" or "That's a common question" — just answer

---

## Pattern 5: Statistic with Attribution

**Used for:** Data queries, "how many" queries, research-backed claims.

**Requirements:**
- Named source (not "a study" — the actual organization name)
- Year of the data
- Specific number (not "many" or "most")
- Context (what the number means)

**Template:**
```markdown
According to [Organization Name]'s [Report Name] ([Year]), [specific statistic with units]. [One sentence on what this means or why it matters].
```

**Example:**
```markdown
According to the Baymard Institute's 2024 UX benchmarking study, 69.8% of online shopping carts are abandoned before purchase. For a $1M/month ecommerce store, recovering just 5% of abandoned carts represents $35,000 in monthly revenue.
```

**Tips:**
- Link to the original source (AI systems and readers both benefit)
- If data is from your own research, say so: "In our 2025 survey of 500 SaaS founders..."
- Proprietary data is the highest-value citation target — AI systems actively seek original research

---

## Pattern 6: Expert Quote Block

**Used for:** Authority building, "what do experts say" queries.

**Requirements:**
- Full name of the person quoted
- Their title and organization
- A quote that's substantive (not a generic endorsement)
- Brief context sentence before the quote

**Template:**
```markdown
[Context sentence explaining why this person's view matters.]

"[Direct quote — specific, substantive, something only they would say]," says [Full Name], [Title] at [Organization].
```

**Example:**
```markdown
Patrick Campbell, founder of ProfitWell (acquired by Paddle), studied pricing data from over 30,000 SaaS companies before reaching a counterintuitive conclusion about churn.

"Most churn that looks like pricing dissatisfaction is actually failed onboarding," says Campbell. "The customer never saw the value that justified the price. That's a different problem than being too expensive."
```

**Tips:**
- Don't use generic quotes ("innovation is key to success") — they add nothing
- Quotes should contain a specific claim, data point, or perspective
- If quoting your own team: "[Name], [Title] at [Company Name]" is still valid
- Live quotes (from interviews or primary research) outperform secondary quotes from other articles

---

## Pattern 7: Quick-Scan Summary Box

**Used for:** Queries where users want the TL;DR before committing to the full article.

**Requirements:**
- Placed near the top of the article (after the intro)
- 3-7 key takeaways
- Each bullet stands alone — no context required
- Labeled clearly ("Key Takeaways" or "Quick Summary")

**Template:**
```markdown
**Key Takeaways**
- [Specific, complete takeaway — could be read as a tweet]
- [Specific, complete takeaway]
- [Specific, complete takeaway]
- [Specific, complete takeaway]
- [Specific, complete takeaway]
```

**Tips:**
- This is often the block AI systems extract for "summary" type queries
- Make each bullet specific: "Monthly churn below 2% is considered healthy for most SaaS" beats "Churn should be low"
- Don't repeat the article intro verbatim — these should be the most actionable insights

---

## Combining Patterns

The most citable pages combine multiple patterns throughout the piece:

**Recommended page structure for maximum AI extractability:**
1. Definition block (first 300 words)
2. Quick summary box (right after intro)
3. Body sections with numbered steps or subsections
4. Data points with full attribution throughout
5. Comparison table (if competitive topic)
6. FAQ block (before conclusion)
7. Expert quote (to add authority)

A page with all 7 patterns has significantly more extractable surface area than a page with prose only. The AI has more options to pull from and a higher probability of finding something that perfectly matches the query.

---

## Citations (6 sources)

1. Google Search Central — Featured snippets and structured data guidelines (developers.google.com/search)
2. Schema.org — FAQPage and HowTo type definitions (schema.org)
3. Backlinko (Brian Dean) — "Definitive Guide to Featured Snippets" extraction-format research
4. Baymard Institute — UX benchmarking methodology cited in the statistic-attribution example (baymard.com)
5. Nielsen Norman Group — "How People Read Online" scanning research underpinning self-contained blocks (nngroup.com)
6. Aggarwal et al. — "GEO: Generative Engine Optimization" (KDD 2024), empirical evidence that citations, statistics, and quotations increase LLM source visibility
