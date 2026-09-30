---
name: consulting-opportunity
description: Analyze a company's careers page for consulting opportunities. Scrapes job postings, identifies automation signals, and generates scoped engagement proposals.
argument-hint: [careers-url]
disable-model-invocation: true
allowed-tools: Bash, WebSearch, WebFetch, Read, Write, Glob, Grep
license: Complete terms in LICENSE.txt
---

# Analyze Company for Consulting Opportunities

You are analyzing a company's careers page to identify consulting opportunities for building agents and automation. Job postings are companies broadcasting their pain points — roles heavy on coordination, data entry, reporting, and manual workflows signal where agent-based automation could replace or augment hiring.

The user has provided a careers URL: `$ARGUMENTS`

## Workflow

### Step 1: Research the Company (DO THIS FIRST)

Use WebSearch to find:
- What the company does, who they serve
- Size, funding stage, growth trajectory
- **Key financials:** Customer count, ARR/revenue figures, growth rates (MoM/YoY), funding rounds and amounts, key investors
- Recent news (acquisitions, expansions, new products)
- Business model and key operational challenges

Include specific numbers in the Company Context section — customer count, ARR, growth rates, team size, number of open roles. These figures are critical for assessing fit and framing opportunities.

### Step 2: Scrape the Careers Page

First, ensure Playwright is installed:
```bash
cd $SKILL_DIR/scripts && npm install && npx playwright install chromium 2>/dev/null || true
```

Then scrape the careers page:
```bash
node $SKILL_DIR/scripts/scrape.js "$ARGUMENTS"
```

This returns JSON with job listings. If the scraper doesn't find jobs automatically, use WebFetch to get the page content and parse it manually.

For each job listing found, scrape the full job description:
```bash
node $SKILL_DIR/scripts/scrape.js --description "JOB_URL_HERE"
```

### Step 3: Smart Deduplication

Before analyzing, deduplicate similar roles:
1. Strip location suffixes (UK, France, EMEA, etc.)
2. Strip seniority prefixes for grouping (Sr., Junior, Lead)
3. Group by normalized title
4. Keep one representative posting per group
5. Note the count of similar roles (indicates team scale)

Cap at 30 unique roles to analyze.

### Step 4: Analyze for Automation Signals

Read the `$SKILL_DIR/signals.md` file for the full signal detection reference.

For each job description, look for:
- **High-signal language:** "manage", "coordinate", "oversee" + process/workflow; "ensure", "maintain", "track" + data/records; "spreadsheet", "reporting", "reconciliation"
- **High-signal role types:** Operations, Coordinator, Analyst with "reporting" emphasis, Implementation/Onboarding, Support with technical investigation
- **Structural signals:** Multiple similar roles (scale problem), 24/7 coverage, cross-functional coordination, compliance/audit

Identify 2-3 distinct opportunity areas. Each should be specific enough to pitch as a scoped engagement.

### Step 5: Generate the Report

Read the template at `$SKILL_DIR/templates/company-report.md` and use it to structure the output.

Create the output directory and write the report:
```bash
mkdir -p data/companies
```

Write to `data/companies/{company-slug}.md`

For each opportunity, frame it as a **quick-win engagement** (2-4 weeks):
- **"The one thing it solves"** — a single, specific pain point
- **What we'd build** — concrete agent/automation, not a vague platform
- **Why now** — reference specific language from job postings
- **Honest caveat** — be specific about what could make this not work: existing tools that solve this (name them), whether the team could build it themselves, market alternatives, timing risks. Don't just flag risk — explain why it might not land.
- **Entry point** — who to pitch to
- **Scope** — 2-4 week engagement with week-by-week breakdown
- **Dependencies** — what access/APIs/data we'd need

Include an **Overall Assessment** section with honest fit rating (Strong/Medium/Weak) and reasoning. For weak fits, include a **"When this might become a fit"** section with a specific re-check timeline (e.g., "worth re-checking in 6-12 months when they scale to X people and start hiring operations roles").

### Step 6: Request Feedback

After presenting the report, ask:
1. Which opportunities resonate? Which don't?
2. What's missing that you expected to see?
3. Is the framing right for how you'd pitch this?

If feedback is provided, save it to `data/feedback/{company-slug}_feedback.md` using the template at `$SKILL_DIR/templates/feedback.md`.

## Positioning Context

We're looking for projects involving:
- **Primary:** Building agents to automate workflows (using Claude, etc.)
- **Secondary:** General consulting on automation, process improvement

Frame opportunities around what we can actually deliver as 2-4 week engagements, not generic "you should automate this."
