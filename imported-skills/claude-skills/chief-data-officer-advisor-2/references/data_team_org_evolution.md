# Data Team Org Evolution — The Decision: "What data role do we hire next, and when do we centralize vs embed?"

This reference answers exactly one decision: **for our stage and business decisions we can't currently make, what is the next role to add — and at what point do we centralize vs embed?**

## The Wrong Question

> "Should we hire a data scientist?"

This is the wrong question. Most data scientists hired by Series A startups are unable to deliver value because:
- The data isn't clean enough for modeling
- There's no infrastructure to deploy a model
- The "model" the founder imagines is actually a SQL query

## The Right Question

> "What's the next decision we can't make because we lack data, and what role unblocks that?"

This shifts hiring from role-taxonomy to decision-unblocking. The data org grows in response to specific decision gaps.

## The Five Stages

### Stage 1: Pre-seed / Seed
**Team size:** 1-15 people. **Data team:** 0.

**Reality:** Founder is the analyst. SQL + spreadsheets are sufficient.

**Don't hire:** Data engineer, data scientist, head of data. They will have nothing to do because the questions aren't crisp enough yet.

**Tooling:** Postgres / production DB direct read access. Metabase Free or Looker Studio. Google Sheets.

**When to move to stage 2:** Founder is spending >20% of their week on data work AND it's preventing them from doing CEO work.

### Stage 2: Series A
**Team size:** 15-50 people. **Data team:** 1-3.

**First hire: Analyst (NOT data engineer, NOT data scientist).**

Why: at this stage, 80% of the value is in clean reports, dashboards, and quick ad-hoc analyses. An analyst delivers all of this. A data engineer wants to build infrastructure that's premature; a data scientist wants to build models that don't have ROI yet.

Profile: 2-4 years experience, strong SQL, BI tool fluency, comfortable with ambiguity, can talk to non-data people.

**Second hire: Analytics engineer (dbt practitioner).**

Why: after the first analyst, the most acute pain is "dashboards are out of sync because everyone defines 'active customer' differently." Analytics engineer brings discipline (dbt models, semantic layer) and turns the analyst's work into reusable infrastructure.

Profile: SQL fluency + software engineering practices (PRs, tests, version control), dbt experience preferred but not required.

**Don't hire yet:** Data engineer, data scientist, head of data, data PM.

**When to move to stage 3:** 3+ functional teams are requesting bespoke analyses weekly, AND your first ML use case has a clear ROI.

### Stage 3: Series B
**Team size:** 50-200. **Data team:** 4-8.

**Third hire: Data engineer.**

Why: ingest pipelines are now business-critical. Salesforce → warehouse, Stripe → warehouse, product events → warehouse. Reliability matters. The analytics engineer cannot maintain this AND ship dbt models.

Profile: Python + SQL + understanding of streaming vs batch tradeoffs, experience with Fivetran/Airbyte or similar.

**Fourth hire: Senior analyst (embedded in GTM, often Sales/Marketing).**

Why: GTM is where data ROI is most measurable. An analyst embedded in the sales org (or reporting dotted-line to CRO) closes the gap between data team and revenue org.

**Fifth hire (conditional): Data PM.**

When: 3+ functional teams need data and the data team has ≥4 people. The data PM owns the roadmap, intake, and SLA negotiations. Without this, the team flips into reactive mode and never builds platform.

**Conditional: Data scientist / ML engineer.**

Hire only when:
- You have at least 1 model in production OR a strong hypothesis with ROI math
- Data engineer is in place (so data scientist isn't blocked on infrastructure)
- Eng leadership signs on for productionizing models (not just notebooks)

**When to move to stage 4:** Central data team is the bottleneck for >50% of GTM data requests, OR you're hiring data people every quarter and they all report to one manager.

### Stage 4: Growth (Series C / pre-IPO)
**Team size:** 200-1000. **Data team:** 8-30.

**Sixth hire: Manager of Analytics (people manager).**

Why: at 5-8 reports, the original analytics lead can no longer code AND manage. Split into managers + senior ICs.

**Seventh hire: ML engineer (production-grade).**

When: 1+ model in production, 2-3 more planned. ML engineer owns deployment, monitoring, retraining infrastructure. Different person from data scientist (who owns model invention).

**Eighth hire: Head of Data.**

Triggers:
- Data team is 10+ people
- Data team has its own strategy independent of company strategy (problematic if no one owns the reconciliation)
- Founder/CTO is no longer the right escalation for data decisions
- Compliance / governance becomes board-level concern

The Head of Data owns data strategy, hires/fires, and is the cross-functional executive for all data + AI.

**Centralize vs Embed decision:**

By Series C, the centralize-vs-embed tension is acute. Two patterns work:

**Hub-and-spoke (most common, recommended):**
- Central data platform team owns infrastructure, governance, semantic layer
- Embedded analysts in 3-5 major functional teams (Sales, Marketing, Product, CS, Finance)
- Embedded analysts have solid-line to function leader, dotted-line to Head of Data
- Tools, standards, dbt models are central; questions and SLAs are local

**Federated (data mesh — only if culture supports):**
- Each domain team owns their data products end-to-end
- Central platform team provides infrastructure substrate, not data products
- Requires high data culture maturity; failure mode is mesh-without-culture

Hub-and-spoke handles 95% of Series C companies. Mesh fits when you're 1000+ people with strong domain ownership culture (Netflix, Zalando, JP Morgan scale).

**When to move to stage 5:** Series D / late-stage growth, 50+ data team members, multiple domains with their own data leadership.

### Stage 5: Late-stage (Series D+, post-IPO)
**Team size:** 1000+. **Data team:** 30-200+.

**CDO promotion / hire.**

Triggers:
- Data is in the company's strategic narrative (board deck, investor calls)
- Data has its own P&L (productized data, monetization)
- Multiple regulatory regimes apply (GDPR + CCPA + HIPAA + EU AI Act)
- Head of Data is escalating data-strategy questions to CTO and it's not landing right

Profile:
- Has run a data org at $100M+ ARR scale
- Comfortable with board reporting
- Strategic, not just technical
- Strong on data governance + AI policy (post-2024 AI Act and similar requirements)

**Federated CDO model (late-stage):**

At thousands-of-people scale, the CDO often runs:
- Central platform team (engineering)
- Central governance team (privacy, compliance, AI policy)
- Federated data leaders embedded per business unit
- Data product leaders for any productized data

## Specific Roles Defined

Because founders confuse these:

| Role | Owns | Does NOT own |
|---|---|---|
| Analyst | Ad-hoc analyses, dashboards, business questions | Pipeline reliability, model deployment |
| Analytics engineer | dbt models, semantic layer, data quality tests | Ingest pipelines, ML, infrastructure |
| Data engineer | Ingest pipelines (Fivetran/Airbyte/custom), warehouse infra, streaming | Modeling logic, dashboards, ML models |
| Data scientist | Model invention, experimentation, statistical analysis | Production deployment, monitoring |
| ML engineer | Production model deployment, monitoring, retraining infra | Model invention |
| Data PM | Data team roadmap, intake, prioritization, stakeholder mgmt | IC delivery work |
| Data PM (productized data) | Data products sold to customers | Internal-only data work |
| Head of Data | Data strategy, hiring, budget, exec representation | Day-to-day IC work |
| CDO | Data + AI strategy at board level, governance, P&L (where applicable) | Day-to-day execution |

## The Centralize-vs-Embed Trigger

The decision is not "centralize or embed" — it's "when do you transition from one to the other?"

**Centralized (everyone reports to one data leader):** works up to ~5 data people serving ≤5 functional teams.

**Hub-and-spoke (central platform + embedded analysts):** works from 5-30 data people serving 5-15 functional teams.

**Federated (each domain owns):** works at 30+ data people across 15+ functional teams WITH strong data culture.

**The trigger to move from centralized to hub-and-spoke:** when 3+ functional teams complain that the central team doesn't understand their domain, AND when the central team's intake queue exceeds 4 weeks of lead time.

**The trigger to move from hub-and-spoke to federated (data mesh):** when domain teams have data leaders, are already running their own data SLAs, and would rather not depend on central platform for product launches. This is rare and usually arrives at thousands-of-people scale.

## Anti-Patterns

- **Hiring a data scientist as first data hire.** They will spend 6 months unable to deliver because data isn't clean.
- **Hiring a "head of data" at Series A.** Nothing for them to manage.
- **Hiring multiple analysts before adding analytics engineer.** Dashboards multiply; consistency vanishes.
- **Building a data platform with no users.** Internal platform team with no customers is shelfware.
- **Hiring an ML engineer before a data engineer.** ML engineer cannot deploy models if data pipelines are broken.
- **Promoting an analyst to "Head of Data" without people-management experience.** Most analysts are great ICs; people management is a different skill.

## When This Reference Doesn't Help

- **Comp benchmarking.** See `c-level-advisor/skills/chro-advisor/scripts/comp_benchmarker.py`.
- **Leveling ladders.** See `c-level-advisor/skills/chro-advisor/references/leveling_ladders.md`.
- **Specific JD templates.** Not covered here; many open-source examples exist.
- **Performance management.** Standard people management; not data-specific.

This reference is about the data team's evolution as a function of company-stage decisions, not about HR mechanics.

---

**Source observations (non-exhaustive):**
- Tristan Handy (dbt Labs) — "The Modern Data Stack: Past, Present, Future"
- Maxime Beauchemin — "The Rise of the Data Engineer" (2017), "The Downfall of the Data Engineer" (2017)
- Erik Bernhardsson — "The Modern Data Experience" (2022)
- Lauren Balik — "Modern Data Stack writings"
- Direct observations from 50+ B2B SaaS data org evolutions, 2020-2026
