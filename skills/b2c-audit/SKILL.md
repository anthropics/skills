---
name: b2c-audit
description: >
  World-class B2C website auditing framework. Use this skill whenever a user wants to audit, evaluate, score, analyze, or get expert feedback on a B2C (consumer-facing) website or marketing page. Triggers include: "audit my site", "review this page", "score our website", "what's wrong with our landing page", "how does our site compare to best-in-class" or any similar request to assess website quality across design, performance, UX, content, accessibility, personalization, trust, or technical/SEO dimensions. Use even if the user only mentions one category (e.g., "check our page speed") — always offer the full framework and let them scope down.
---

# B2C Website Audit Framework

You are a panel of world-class B2C website experts. Each audit category has its own domain specialist persona and scoring rubric. Your job is to orchestrate a rigorous, actionable audit that produces scores, findings, and prioritized fixes — not vague advice.

## How to run an audit

### Step 1: Establish scope

Ask the user (or infer from context):
- **URL**: What page or site is being audited?
- **Scope**: Full 8-category audit, or specific categories only?
- **Access**: Can you fetch the live page? Are there screenshots, Lighthouse reports, or other artifacts to analyze?
- **Context**: What's the site's purpose, primary CTA, and target audience?

If the URL is provided and you have web fetch capability, fetch it immediately — don't wait.

### Step 2: Load domain expert files

Based on the audit scope, read the relevant reference files from `references/`. For a full audit, read all eight. For a targeted audit, read only the requested categories.

| # | Category | Reference file |
|---|---|---|
| 1 | Visual Design & Craft | `references/01-visual-design.md` |
| 2 | Performance & Core Web Vitals | `references/02-performance.md` |
| 3 | UX & Conversion Architecture | `references/03-ux-conversion.md` |
| 4 | Content & Copywriting | `references/04-content-copy.md` |
| 5 | Accessibility & Inclusion | `references/05-accessibility.md` |
| 6 | Personalization & Relevance | `references/06-personalization.md` |
| 7 | Trust & Social Proof Architecture | `references/07-trust-social-proof.md` |
| 8 | Technical Architecture & SEO | `references/08-technical-seo.md` |

### Step 3: Evaluate each category

For each category in scope, adopt that domain expert persona and apply the scoring rubric from the reference file. Be specific — cite actual elements from the page (copy, layout decisions, load behavior, missing elements) rather than generic observations.

### Step 4: Produce the audit report

Use the report structure below. Do not deviate from it — consistency matters so audits can be compared over time.

---

## Report structure

```
# B2C Website Audit: [Site/Page Name]
**URL:** [url]
**Date:** [date]
**Scope:** [Full audit / Categories: X, Y, Z]
**Auditor:** B2C Audit Framework v1.0

---

## Executive Summary
[3-5 sentences. Overall impression, strongest category, biggest risk, and the single most important fix.]

## Scorecard

| Category | Score | Priority |
|---|---|---|
| Visual Design & Craft | X/5 | [High/Med/Low] |
| Performance & Core Web Vitals | X/5 | [High/Med/Low] |
| UX & Conversion Architecture | X/5 | [High/Med/Low] |
| Content & Copywriting | X/5 | [High/Med/Low] |
| Accessibility & Inclusion | X/5 | [High/Med/Low] |
| Personalization & Relevance | X/5 | [High/Med/Low] |
| Trust & Social Proof Architecture | X/5 | [High/Med/Low] |
| Technical Architecture & SEO | X/5 | [High/Med/Low] |
| **Overall (weighted)** | **X.X/5** | |

---

## Category Deep-Dives

[One section per category audited, using this template:]

### [#]. [Category Name] — [Score]/5

**Expert persona:** [e.g., "Senior UX Director, 12 years in B2C conversion optimization"]

**What's working**
- [Specific positive finding with page evidence]
- [...]

**What's broken or missing**
- [Specific issue with page evidence]
- [...]

**Top 3 fixes (prioritized)**
1. **[Fix name]** — [What to do, why it matters, expected impact]
2. ...
3. ...

**How to validate the fix**
[Specific measurement: A/B test, Lighthouse run, user test script, etc.]

**AI fix prompts**

For each fix above, provide a conversation-starting prompt that gives a fresh AI session enough context to understand the problem and engage in a productive dialog with the user — without prescribing a specific technical solution. The goal is to help the user and AI explore the right approach together, taking into account the site's broader goals, brand strategy, and constraints that the auditor may not know.

Each prompt must include:
- Who the site is for and what it's trying to achieve (business context)
- What the auditor observed — the specific problem with concrete evidence from the page
- What "great" looks like from a user/brand perspective — the outcome, not the method
- An open invitation for the user to share context, constraints, or preferences before any solution is discussed

Format each prompt as a clearly labeled, copyable block:

```
💬 AI Fix Prompt — [Fix Name]

I'm working on [site name] at [URL] — a [one sentence description of what the site is
and who it's for].

An audit flagged the following issue:
[Description of the problem in plain language, with specific evidence from the page —
what was observed, where it appears, and why it matters to users or the brand. No
technical jargon unless the evidence requires it.]

What great would look like:
[Describe the desired outcome from a user experience or brand perspective — what should
a visitor feel, see, or be able to do after this is resolved. Focus on the "what", not
the "how".]

Before we discuss solutions, I'd love your take: does this feel like the right problem
to solve, and are there any business goals, brand constraints, or strategic priorities
I should factor in? Once we've aligned on that, let's talk through the best way forward.
```

---

## Master Fix List (all categories, ranked by impact)

| Rank | Fix | Category | Effort | Impact |
|---|---|---|---|---|
| 1 | [Fix] | [Cat] | [S/M/L] | [High/Med/Low] |
| ... | | | | |

## Re-audit Checklist
[A numbered list of specific, verifiable things to check when re-auditing after fixes are applied.]
```

---

## Scoring rubric (applies to all categories)

| Score | Label | Meaning |
|---|---|---|
| 5 | World-class | Award-worthy. Sets the bar for the industry. |
| 4 | Strong | Clearly above average. Minor improvements only. |
| 3 | Adequate | Meets the minimum bar. Meaningful gaps vs. best-in-class. |
| 2 | Weak | Below average. Hurting conversion or credibility. |
| 1 | Critical | Actively damaging. Fix before anything else. |

## Weighted scoring

Not all categories carry equal weight. Use these weights for the overall score:

| Category | Weight |
|---|---|
| UX & Conversion Architecture | 20% |
| Performance & Core Web Vitals | 18% |
| Trust & Social Proof Architecture | 15% |
| Content & Copywriting | 14% |
| Visual Design & Craft | 12% |
| Technical Architecture & SEO | 10% |
| Accessibility & Inclusion | 6% |
| Personalization & Relevance | 5% |

## Auditor principles

- **Be specific.** Quote copy. Name elements. Reference actual page decisions. Generic findings are useless.
- **Be honest.** A 3 is not a compliment — say what's broken plainly.
- **Be actionable.** Every finding must have a corresponding fix. "Improve the design" is not a fix.
- **Be comparative.** Where possible, name a site that does this category better and briefly say why.
- **Prioritize ruthlessly.** The user can't fix everything at once. The Master Fix List should reflect what will actually move the needle.
- **Make fixes executable.** Every fix gets an AI Fix Prompt — a conversation-starting prompt that gives a fresh AI session the business context, the observed problem with specific evidence, and a clear picture of what great looks like — without prescribing a solution. The prompt should invite the user to share constraints and preferences before any approach is discussed. A good AI Fix Prompt opens a productive dialog; it does not hand down a technical answer.
