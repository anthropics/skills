---
name: dead-app-hunt
description: "Research abandoned and neglected apps in any sector, mine their 1-star reviews, and output a ranked opportunity list with MVP specs. Use when the user wants to find product opportunities, analyze competitor weaknesses, or discover underserved markets by studying failed or abandoned applications."
license: MIT
metadata:
  author: moski-labs
  version: "1.0"
---

# Dead App Hunt

**"Don't invent. Re-invent."**

Find neglected or abandoned apps in a given sector and turn their failures into a product roadmap.

## Input

The user provides a **sector or category** (e.g. "fitness tracking", "invoice management", "language learning").

If no sector is provided, ask the user: "What sector or app category should I hunt in?"

## Process

### Step 1: The Hunt

Search for apps in the given sector that meet these criteria:
- **Niche utilities** (not big-name apps)
- **Last updated > 1 year ago** (abandoned or neglected)
- **Still have active users** (proven demand)

Use web search to find:
1. App Store and Google Play listings in the category
2. "Best [sector] apps" listicles that mention smaller tools
3. Product Hunt launches in the category that have gone quiet
4. Reddit threads where users complain about existing tools

### Step 2: The Audit

For each dead/neglected app found (aim for 5-10), research:
- **1-star reviews**: What are users complaining about? Common patterns?
- **Feature gaps**: What do users wish it had?
- **UI/UX complaints**: "Too complicated", "crashes", "ugly interface"
- **Pricing complaints**: "Too expensive for what it does"

These complaints ARE the product roadmap.

### Step 3: Insight Extraction

Cross-reference the complaints to find patterns:
- Which problems appear across MULTIPLE apps? (high-signal)
- Which problems are solvable with modern AI/tech? (feasible)
- Which problems have paying users behind them? (monetisable)

## Output

Write a file called `dead-app-hunt-[sector].md` in the current directory with this structure:

```markdown
# Dead App Hunt: [Sector]

## Executive Summary
[2-3 sentences: the biggest opportunity found]

## Dead/Neglected Apps Found

### 1. [App Name]
- **Last Updated**: [date]
- **Platform**: iOS / Android / Web
- **Rating**: X.X stars (N reviews)
- **Top Complaints**:
  - [complaint 1]
  - [complaint 2]
  - [complaint 3]
- **Opportunity**: [what you'd build differently]

### 2. [App Name]
[repeat...]

## Pattern Analysis

| Complaint Pattern | Frequency | Feasibility | Revenue Signal |
|---|---|---|---|
| [pattern] | X apps | High/Med/Low | High/Med/Low |

## Top 3 Opportunities (Ranked)

### #1: [Opportunity Name]
- **Problem**: [the core user pain]
- **Evidence**: [which apps/reviews prove this]
- **Suggested 3-Feature MVP**:
  1. [Feature 1 — solves the #1 complaint]
  2. [Feature 2 — solves the #2 complaint]
  3. [Feature 3 — the differentiator]
- **Monetisation angle**: [how this makes money]

### #2: [Opportunity Name]
[repeat...]

### #3: [Opportunity Name]
[repeat...]

## Next Step
Validate the top opportunity against macro trends and produce a full MVP spec.
```

## Rules
- Be specific. Use real app names, real review quotes where possible.
- Rank by **signal strength** (frequency of complaint x feasibility x revenue potential).
- Always output actionable opportunities, not just analysis.
