# Example: Idea Validation Report — InterviewOps

> This is a reference example showing the expected output format and depth.
> Use this to calibrate your own reports.

---

# Idea Validation Report: InterviewOps
**Date:** 2025-05-01
**Validator:** Claude Idea Validator Skill

## Executive Summary
InterviewOps targets a high-acuity pain (job seekers failing interviews for preventable reasons) with a differentiated AI-agentic approach that goes beyond generic prep tools. The go/no-go verdict is **CONDITIONAL GO**: the core technical pipeline is feasible, but monetization and trust in AI-generated prep plans remain unvalidated. The highest-risk assumption — that candidates trust AI enough to practice with it over a human coach — must be tested before scaling.

---

## Phase 1 — Problem & User Clarity

**Pain Trigger:** A software developer receives an interview invite from a target company. They have 5–7 days. They don't know the company's engineering culture, tech stack quirks, or what past interviewees faced.

**Current Workaround:** Google the company + "interview experience", scroll Glassdoor reviews, look up LeetCode company tags, ask friends.

**Workaround Failure:** Fragmented, inconsistent, outdated, and doesn't connect to their specific resume or the JD they applied for.

**Cost of Problem:** An unprepared candidate wastes 7 days of prep on generic material, fails a dream-company interview, and loses a $20k–$100k salary opportunity.

### Failure Modes
1. **Distribution risk** — job seekers don't know where to find niche tools; discoverability is brutal without SEO or community traction.
2. **Trust risk** — AI-generated prep plans may feel generic; candidates default to human coaches for high-stakes interviews.
3. **Timing risk** — interview windows are short (5–7 days); if the tool takes >30 min to set up, they'll skip it.
4. **Data staleness risk** — scraped interview data goes stale fast; Glassdoor reviews from 2022 don't reflect current engineering bars.
5. **Retention risk** — this is an event-driven tool; users churn between job searches, making recurring revenue hard.

### Persona A — The Buyer
- **Role:** Mid-level software engineer, 3–6 YoE, actively job hunting
- **Pain trigger:** Got a Google interview after 2 years of trying; terrified of wasting it
- **Would pay:** $30–$50 for a single company prep report; $19/mo for active job search period
- **Churn trigger:** Gets the job (positive churn); tool gives generic answers they could Google

### Persona B — The Skeptic
- **Role:** Senior engineer, confident in interviews, skeptical of AI tools
- **Won't pay because:** "I can find this on Glassdoor myself" + low trust in AI accuracy for company-specific culture

### Fake 1-Star Review
```
★☆☆☆☆ "Felt like ChatGPT with a Glassdoor skin"
I paid $29 for a Google prep report. The "company pain points" were just
generic complaints I'd already seen on Reddit. The practice questions
were LeetCode mediums I'd done 3 years ago. Nothing felt specific to
the current engineering bar. Went with a human coach for my actual prep.
— Priya K., Staff Engineer
```

**Problem Scores:** Acuity: 5/5 | Frequency: 3/5 (event-driven) | Willingness to Pay: 4/5

---

## Phase 2 — Market & Competition

| Competitor | Pricing | Key Strength | Key Weakness | Target User |
|---|---|---|---|---|
| Interviews.chat | $29/mo | AI mock interviews | Generic, not company-specific | All job seekers |
| Final Round AI | $96/mo | Real-time interview assist | Ethically grey, bans risk | Aggressive candidates |
| Glassdoor | Free / $10/mo | Real user reviews | Fragmented, no synthesis | All |
| Grokking the Interview | $39/mo | Structured patterns | No company-specific context | Engineers |
| Exponent | $12/mo | PM/SWE human coaching | Expensive at scale | Senior candidates |

**Gap:** Nobody connects company-specific intelligence (culture, pain points, actual questions) to a candidate's specific resume + JD and generates a personalized prep plan. That's the gap InterviewOps fills.

**Differentiation:** `Unique Angle: Company-specific + resume-matched + JD-aligned prep plan in one automated pipeline`
`Defensibility: MEDIUM — the data pipeline is moatable but the AI layer is commoditizing`

**Market Signal:** Exponent, Final Round AI all have paying customers. Glassdoor Premium exists. Coaching market ($2B+) is proven. Green flags.

**ICP:** Software engineers + PMs, 2–8 YoE, actively interviewing at top-50 tech companies.
1% of 500k active job seekers at $25/report = **$125k/month ceiling at MVP pricing**. Viable.

---

## Phase 3 — Prototype Feasibility

**Core Assumption:** Users trust a company-specific prep plan generated from scraped data + their resume enough to follow it over generic resources.

**Test Method:** Build a Wizard of Oz prototype — manually run the pipeline for 10 job seekers, deliver the report via PDF or Notion. See if they say "this is worth $X."

```
Prototype Type: Level 3 (Wizard of Oz)
Build Time: ~1 day of manual work per report
Platform: Claude chat + Notion template + PDF export
CTA: "Get your custom [Company] interview prep report — $0 for first 10 beta users"
Traffic Source: Blind, Reddit r/cscareerquestions, Twitter/X #jobsearch
Pass Condition: 7/10 beta users say "I would have paid $20+ for this"
```

**What NOT to build yet:** Auth, billing, user accounts, company database UI, admin dashboard, mobile app.

---

## Phase 4 — Technical Risk Assessment

| Risk | Category | Severity | Likelihood | Mitigation |
|---|---|---|---|---|
| Glassdoor/LinkedIn scraping ToS violations | Data/Legal | HIGH | HIGH | Use Firecrawl + rotate sources; long-term build partnerships or use official APIs |
| AI output quality variance (hallucinated "company facts") | AI/ML | HIGH | MEDIUM | Implement source citation in every claim; human review flag for low-confidence data |
| Data staleness — interview reviews age quickly | Data | MEDIUM | HIGH | Timestamp all data; flag reviews >6 months old; allow user submission to augment |
| Cost at scale — multi-agent pipeline is expensive | Scale | MEDIUM | MEDIUM | Cache company research aggressively; separate scrape cadence from user-triggered runs |
| Resume parsing accuracy for non-standard formats | Integration | LOW | MEDIUM | Use existing libs (resume-parser, Affinda API) rather than building custom |

```
Spike Target: The scraping pipeline — specifically, can you reliably extract structured
              interview questions + sentiment from Glassdoor/Blind without getting blocked?
Why This One: If the data quality is poor or scraping is blocked, the whole value prop collapses.
Time Estimate: ~2 days
Success Criteria: 50+ structured interview data points extracted for 3 companies with >80% relevance
Failure Signal: Block rate >30% within 24h, or data quality too noisy to be useful
```

**Stack (for your profile):**
- **Backend:** Node/Fastify or Python/FastAPI (FastAPI preferred for agent orchestration)
- **AI Layer:** Anthropic API (Claude Sonnet 4.x) — direct API, not LangChain at MVP
- **Scraping:** Firecrawl + Playwright fallback; BrightData for production
- **Data:** Postgres + pgvector for resume/JD embeddings; Redis for job queue
- **Hosting:** Railway for MVP

**Agentic Assessment:** You built a multi-agent system — that was the right destination. But at MVP, you could have validated with **sequential API calls**: scrape → extract → match → generate. Full agent orchestration is worth it after you validate data quality and output trust.

---

## Phase 5 — Go / No-Go Decision Memo

| Dimension | Score | Weight | Weighted |
|---|---|---|---|
| Problem Acuity | 5/5 | 25% | 1.25 |
| Market Demand Signal | 4/5 | 25% | 1.00 |
| Competitive Differentiation | 4/5 | 20% | 0.80 |
| Technical Feasibility | 3/5 | 15% | 0.45 |
| Prototype Testability | 4/5 | 15% | 0.60 |
| **Total** | | | **4.10/5.0** |

```
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
VERDICT: CONDITIONAL GO
CONFIDENCE: 7/10
WEIGHTED SCORE: 4.1/5.0
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

**Biggest Unvalidated Assumption:**
"Candidates trust AI-synthesized company intelligence enough to follow the prep plan instead of defaulting to a human coach or Googling it themselves."

**The Condition:** Run the Wizard of Oz for 10 beta users. If 7/10 say they would have paid $20+, the trust bar is cleared. Proceed to technical build.

**If condition is met:** Build the scraping spike first. Don't touch auth or billing until 50 users have used a free report and 10 have asked to pay.

**If condition fails:** The trust gap is real. Pivot to a **human-in-the-loop** model — AI drafts the plan, a human coach reviews and personalizes it. Lower margin, but the trust problem is solved.

---

## Appendix — Validation Checklist

### ✅ Validated
- [x] Problem exists and is high-acuity
- [x] Competitors identified — gap confirmed
- [x] Differentiation articulated (company-specific + resume-matched)
- [x] Tech stack de-risked (feasible with known tools)
- [x] Market signal exists (adjacent tools have paying customers)

### ⚠️ Still Open
- [ ] User trust in AI-generated prep plans (the condition)
- [ ] Pricing sensitivity ($19/mo vs $29/report vs free+upsell)
- [ ] Data quality from scraping pipeline (spike required)
- [ ] Retention model — how to monetize between job searches

### 🚫 Out of Scope Until First Revenue
- [ ] Enterprise / recruiting team use case
- [ ] Mobile app
- [ ] Real-time interview coaching (Final Round AI territory)
- [ ] Browser extension
