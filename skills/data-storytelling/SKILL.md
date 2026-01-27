---
name: data-storytelling
description: Transform raw data into compelling narratives with insights and visualizations. Use when users need to communicate data findings to stakeholders, create executive summaries from analytics, build data-driven presentations, or explain trends and patterns. Triggers on requests like "explain this data", "summarize these metrics", "create a data presentation", "what does this data tell us", or "make a dashboard narrative".
---

# Data Storytelling

Bridge the gap between raw data and meaningful communication by crafting narratives that drive understanding and action.

## Storytelling Framework

### 1. Context → Insight → Action

Every data story follows this arc:

```
CONTEXT: What's the situation? Why does this matter now?
    ↓
INSIGHT: What did the data reveal? What's surprising or important?
    ↓
ACTION: What should we do about it? What's the recommendation?
```

### 2. Story Structure Template

```markdown
## The Headline
[One sentence that captures the key insight]

## The Setup
[Why we looked at this data, what question we're answering]

## The Journey
[What the data shows, building from simple to complex]

## The Revelation
[The key insight, the "aha" moment]

## The Path Forward
[Recommendations and next steps]
```

## Audience Adaptation

### Executive Summary (C-Suite)
- Lead with the insight, not the methodology
- Focus on business impact and dollars
- One key metric, one key action
- Keep to one page or 3 minutes

```markdown
**Bottom Line**: [Revenue/growth/risk impact in one sentence]

**Key Finding**: [The insight]

**Recommended Action**: [What to do]

**Supporting Data**: [2-3 bullet points max]
```

### Operational Report (Managers)
- Include trends and comparisons
- Show what's within tolerance vs. needs attention
- Provide enough detail for decisions

### Technical Deep-Dive (Analysts)
- Full methodology explanation
- Statistical significance noted
- Raw data access provided

## Visualization Selection

### Match Chart to Message

| What You're Showing | Best Visualization |
|---------------------|-------------------|
| Change over time | Line chart |
| Comparison between categories | Bar chart |
| Part-to-whole relationship | Pie/donut (≤5 segments), stacked bar |
| Correlation between variables | Scatter plot |
| Distribution | Histogram, box plot |
| Geographic patterns | Map |
| Single metric status | Big number, gauge |

### Visual Hierarchy

```
1. TITLE: What is this showing? (not "Revenue Chart")
   → "Revenue grew 23% after campaign launch"

2. FOCUS: Draw eye to the key insight
   → Color, size, annotation

3. CONTEXT: Reference points
   → Benchmarks, targets, prior period

4. DETAIL: Supporting information
   → Legend, axis labels, source
```

## Insight Extraction Process

### Step 1: Describe What You See

```
- Total: [value]
- Range: [min] to [max]
- Average/Median: [value]
- Trend direction: [up/down/flat]
- Notable outliers: [items]
```

### Step 2: Compare to Find Meaning

| Comparison Type | Question Answered |
|-----------------|-------------------|
| vs. Prior Period | Is this better or worse? |
| vs. Target/Goal | Are we on track? |
| vs. Benchmark | How do we compare to others? |
| vs. Segments | Where are the differences? |

### Step 3: Ask "So What?"

Transform observation into insight:

```
OBSERVATION: Sales dropped 15% in Q3
    ↓ So what?
INSIGHT: Our largest customer segment reduced spending
    ↓ So what?
IMPLICATION: We need to address churn risk or find new segments
    ↓ So what?
RECOMMENDATION: Launch retention program for enterprise accounts
```

## Narrative Patterns

### The Trend Story

```markdown
**Where we were**: [Historical baseline]
**What changed**: [The inflection point or trend]
**Where we're headed**: [Projection if trend continues]
**What to do**: [Action to maintain or reverse]
```

### The Comparison Story

```markdown
**The difference**: [Key gap between A and B]
**Why it matters**: [Impact of that difference]
**The cause**: [What explains the difference]
**The learning**: [What we should do differently]
```

### The Anomaly Story

```markdown
**The surprise**: [What deviated from expectations]
**The investigation**: [What we found when we dug in]
**The explanation**: [Root cause]
**The response**: [Whether to act or adjust expectations]
```

### The Correlation Story

```markdown
**The pattern**: [When X happens, Y tends to happen]
**The evidence**: [Data showing the relationship]
**The caveat**: [Correlation vs. causation acknowledgment]
**The hypothesis**: [Proposed causal mechanism to test]
```

## Dashboard Narrative Flow

### Layout Principles

```
┌─────────────────────────────────────────────┐
│  HEADLINE METRIC                            │  ← Most important number
│  +12% vs target                             │
├─────────────────┬───────────────────────────┤
│                 │                           │
│  TREND          │  BREAKDOWN                │  ← Context and detail
│  (line chart)   │  (bar chart)              │
│                 │                           │
├─────────────────┴───────────────────────────┤
│  SUPPORTING DETAILS                         │  ← Tables, secondary metrics
│  (as needed)                                │
└─────────────────────────────────────────────┘
```

### Annotation Best Practices

Add annotations to highlight:
- Goal lines and targets
- Events that explain changes
- Anomalies requiring attention
- Thresholds (good/warning/critical)

## Output Templates

### One-Page Data Brief

```markdown
# [Topic]: [Key Finding in Active Voice]

## At a Glance
| Metric | Current | vs. Prior | Status |
|--------|---------|-----------|--------|
| [KPI]  | [value] | [change]  | [↑/↓]  |

## Key Insight
[2-3 sentences explaining the most important finding]

## What's Driving This
1. [Factor 1]
2. [Factor 2]

## Recommended Action
[Specific, actionable recommendation]

## Methodology Note
[One line on data source and time period]
```

### Talking Points Format

```markdown
# [Topic] - Talking Points

**Lead with**: "[Quote-ready key finding]"

**If asked about trend**:
[Context and explanation]

**If asked about comparison to X**:
[Relevant benchmark data]

**If asked about next steps**:
[Recommended actions]

**Caveat to mention**:
[Any important limitations]
```

## Quality Checklist

- [ ] Insight stated in headline (not just topic)
- [ ] Data source and time period clear
- [ ] Visualizations have descriptive titles
- [ ] Comparison context provided
- [ ] "So what" answered explicitly
- [ ] Recommendation is specific and actionable
- [ ] Appropriate for audience expertise level
- [ ] Caveats and limitations noted
