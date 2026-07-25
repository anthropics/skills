# Scaling Playbook: What Breaks at Each Growth Stage

> Compiled from patterns across 100+ high-growth companies. Not theory — this is what actually breaks and what to do about it.

---

## How to Use This Playbook

Each stage section covers:
1. **What breaks** — the specific failure modes that kill companies at this stage
2. **Hiring** — who to bring in and when
3. **Process** — what to formalize vs. keep loose
4. **Tools** — infrastructure that unlocks the next stage
5. **Communication** — how information flow changes
6. **Culture** — what to protect and what to let go

**Benchmarks are medians** — your mileage varies by sector, geography, and business model.

---

## Stage 0: Pre-Seed / Seed ($0–$2M ARR, 1–15 people)

### Key Benchmarks
| Metric | Benchmark |
|--------|-----------|
| Revenue per employee | $0–$100K (still finding PMF) |
| Manager:IC ratio | N/A (no managers) |
| Burn multiple | 2–5x (acceptable) |
| Runway | 12–18 months minimum |
| Time-to-hire | 2–4 weeks |

### What Breaks

**Premature process.** The #1 mistake at seed stage is adding process before you have a repeatable model. Sprint ceremonies, OKR frameworks, and performance reviews are all theater when you haven't found PMF. Every hour spent in process is an hour not spent learning.

**Wrong first hires.** Hiring "senior" people who've only worked in structured environments. You need people who can operate in chaos, not people who expect process to already exist.

**Founder communication bottleneck.** Founders try to be in every decision. Fine at 5 people, fatal at 12. No written decisions means knowledge lives in founders' heads — unscalable.

**Technical debt accepted as strategy.** "We'll fix it later" said about core data models, auth systems, or billing. Later comes at Series A and it costs 3x more to fix.

### Hiring
- **Don't hire for scale you don't have.** Hire for the next 12 months.
- **First 10 hires set culture permanently.** Get them wrong and you'll spend years correcting.
- **Hire athletes, not specialists.** Generalists who can do multiple jobs outperform specialists at this stage.
- **Avoid VP titles early.** Inflated titles block future hires and create expectations you can't meet.
- **Founder-referral bias is real.** Your network is homogeneous. Force diversity early.

**Who to hire first (in rough order):**
1. Engineers who can ship product (2–3 generalists)
2. First sales/GTM if B2B (founder-led sales first, then one closer)
3. Designer/product (often a hybrid)
4. Customer success (often a founder at first)

### Process
**Formalize nothing before PMF.** Literally. Run on Slack, shared docs, and founder judgment.

**After PMF signals appear, formalize only:**
- How you handle customer escalations
- How you deploy code (even basic CI/CD)
- How you onboard new hires (a 1-page checklist is enough)

**Decision rule:** If a founder has to answer the same question three times, write it down. Once.

### Tools
| Function | Seed-Stage Tool |
|----------|----------------|
| Communication | Slack + Google Workspace |
| Project tracking | Linear or Notion (pick one, stay consistent) |
| CRM | HubSpot free or Notion |
| Engineering | GitHub + basic CI (GitHub Actions) |
| Finance | Brex/Mercury + QuickBooks |
| HR | Rippling or Gusto (basic) |
| Analytics | Mixpanel or PostHog (free tier) |

**Rule:** One tool per function. No tool sprawl. Every extra tool is a coordination tax.

### Communication
- **Weekly all-hands** (30 min max). What shipped, what's stuck, what's next.
- **No status meetings.** Anyone can see status in Linear/Notion.
- **Founder write-ups.** Every major decision gets a 1-paragraph Slack post explaining *why*.
- **Group chat discipline.** One channel per project/customer. Inbox zero mentality.

### Culture
**What to build deliberately:**
- High ownership: everyone acts like they own the company, because they do
- Direct feedback: brutal honesty delivered with care
- Bias to ship: done > perfect
- Customer obsession: founders talk to customers weekly

**What to watch for:**
- "Hero culture" where one person saves everything — unsustainable
- Over-indexing on culture fit (code for homogeneity)
- Avoidance of conflict — mistaking silence for agreement

---

## Stage 1: Series A ($2–$10M ARR, 15–50 people)

### Key Benchmarks
| Metric | Benchmark |
|--------|-----------|
| Revenue per employee | $100–$200K |
| Manager:IC ratio | 1:6–1:8 |
| Burn multiple | 1.5–2.5x |
| Sales efficiency (CAC payback) | <18 months |
| Churn (B2B SaaS) | <10% net annual |
| Engineering velocity | Feature shipped every 1–2 weeks |
| Time-to-hire | 4–6 weeks |
| Offer acceptance rate | >80% |

### What Breaks

**Founder-as-manager bottleneck.** At 20+ people, founders can't manage everyone. The first layer of management needs to appear — and it's usually picked wrong (best IC ≠ best manager).

**Tribal knowledge explosion.** "Ask Sarah" stops working when Sarah has 15 things open. Documentation becomes critical — not for bureaucracy, but because institutional knowledge is now a flight risk.

**Sales process fragmentation.** Without a defined sales process, every rep closes differently. You can't train, debug, or scale what you can't see.

**Scope creep in product.** With Series A money comes investor pressure to expand scope. Teams try to build three things at once and ship nothing well.

**Compensation chaos.** Early employees got equity-heavy deals. New hires get market cash. Someone compares, someone gets upset. No comp philosophy = constant re-negotiation.

**Recruiting becomes a job in itself.** Founders can't hire 30 people themselves. First dedicated recruiter needed by 25 people.

### Hiring

**Who to hire at Series A:**
- **Head of Engineering** (if founder is CTO): needs to be an operator, not just an architect
- **First Sales Manager** (when you have 3+ reps): don't promote the best seller
- **HR/People Ops** (generalist, by 30 people): comp, compliance, recruiting coordination
- **Finance** (fractional CFO or strong controller): Series A board needs real numbers
- **Customer Success Lead**: retention is everything at this stage

**Hiring mistakes to avoid:**
- Hiring "big company" execs who need large teams and established process
- Assuming your Series A lead can recruit (they can intro, not close)
- Taking too long — top candidates have 2–3 offers. Move in <2 weeks from first call to offer.

**Leveling:** Build a simple career ladder *before* the compensation complaints start. 3–4 levels per function is enough.

### Process

**What to formalize at Series A:**
1. **Sprint planning** (2-week sprints, public roadmap)
2. **Sales process** (defined stages with entry/exit criteria)
3. **Onboarding** (30/60/90 day plan for each function)
4. **1:1 cadence** (weekly for direct reports, bi-weekly for skip-levels)
5. **Incident response** (P0/P1/P2 definition, on-call rotation)
6. **Quarterly planning** (OKRs or goals framework — keep it lightweight)

**What to keep loose:**
- Internal project process (let teams self-organize)
- Meeting formats (let teams evolve their own rituals)
- Tool selection within approved stack

**Documentation standard:** Write decisions down in a shared wiki. "Decision log" with date, decision, context, owner, and outcome. Takes 5 minutes, saves hours.

### Tools
| Function | Series A Tool |
|----------|--------------|
| Project/Product | Linear + Notion |
| CRM | HubSpot or Salesforce (Starter) |
| Engineering | GitHub + CI/CD pipeline + Sentry |
| HR/People | Rippling or Lattice (performance) |
| Finance | NetSuite or QBO + Brex |
| Analytics | Mixpanel/Amplitude + Looker (or Metabase) |
| Customer Success | Intercom + HubSpot or Zendesk |
| Docs | Notion or Confluence |

### Communication

**Introduce structured communication layers:**

1. **Company all-hands** (monthly, 60 min): CEO share, metrics review, team spotlights, Q&A
2. **Leadership sync** (weekly, 60 min): cross-functional issues, blockers, priorities
3. **Team standups** (async or 15 min daily): what's in progress, what's blocked
4. **1:1s** (weekly): direct report health, career, performance
5. **Written updates** (weekly to investors + board): CEO memo format

**Information hierarchy:** Everyone in the company should know: (1) company goals this quarter, (2) their team's goals, (3) what they personally own. If they don't, your communication structure is broken.

### Culture

**Deliberate culture work starts here.** You're too big for culture to be accidental.

- **Write down values.** Real values with examples of what they look like in action. Not "integrity" — "we tell investors bad news before we tell them good news."
- **Performance management.** First PIPs (Performance Improvement Plans) happen at this stage. Handle them well — the team is watching.
- **Equity culture.** Make sure people understand what their equity is worth in different outcomes. Lack of transparency breeds resentment.
- **First layoff plan.** Even if you never use it, know the criteria. Reactive layoffs destroy trust; plan-based ones (even painful) preserve it.

---

## Stage 2: Series B ($10–$30M ARR, 50–150 people)

### Key Benchmarks
| Metric | Benchmark |
|--------|-----------|
| Revenue per employee | $150–$300K |
| Manager:IC ratio | 1:5–1:7 |
| Burn multiple | 1.0–1.5x |
| CAC payback | <12 months |
| NRR (net revenue retention) | >110% |
| Engineering: Product ratio | ~3:1 |
| Sales: CS ratio | ~3:1 |
| Time-to-hire (senior) | 6–10 weeks |
| Annual attrition | <15% voluntary |

### What Breaks

**Middle management void.** You now have managers managing managers. The "player-coach" model breaks — people can't be ICs and managers simultaneously at this scale. Force the choice.

**Planning misalignment.** Sales promises what product hasn't built. Product builds what customers didn't ask for. Engineering ships what QA didn't test. Fixing this requires cross-functional planning ceremonies.

**Data fragmentation.** Five different versions of "how are we doing." Sales sees Salesforce. Product sees Amplitude. Finance sees spreadsheets. Nobody agrees. You need a single source of truth.

**Process debt.** The Series A processes are starting to creak. Onboarding that worked for 5 hires/quarter doesn't work for 20. Customer escalation paths built for 50 customers fail at 500.

**Cultural fragmentation.** Engineering culture ≠ Sales culture ≠ Support culture. Sub-cultures form. The shared identity you had at 30 people requires active work to maintain at 100.

**The "brilliant jerk" problem.** High performers with bad behavior were tolerated early. Now they're managers with bad behavior, and it's systemic. Act decisively or lose your best people.

### Hiring

**Who to hire at Series B:**
- **COO or VP Operations**: founder is overwhelmed, someone needs to run the machine
- **VP Sales**: first Sales Manager won't scale to 20-rep org
- **VP Marketing**: demand gen and brand need dedicated ownership
- **Dedicated Recruiting**: 2–3 recruiters minimum; you're hiring 30–50 people/year
- **Data/Analytics**: dedicated analyst or data engineer to consolidate reporting
- **Legal counsel**: fractional or in-house; contracts and compliance are getting complex

**The "big company exec" trap.** Series B is when companies hire their first VP from FAANG or a large SaaS company. 60% of these fail within 18 months. They're used to: large teams, established brand, existing process, political navigation. They struggle with: scrappy execution, no support staff, ambiguous direction. Vet explicitly for startup experience.

**Span of control.** At this stage, hold managers to 5–8 direct reports. More than 8 = no time for actual management. Less than 3 = management overhead isn't justified.

### Process

**What to formalize at Series B:**
1. **Quarterly Business Reviews (QBRs)** — every function presents metrics, wins, gaps
2. **Annual planning** — budget, headcount plan, strategic priorities
3. **Cross-functional roadmap alignment** — product/sales/marketing in sync quarterly
4. **Promotion criteria** — written, public, applied consistently
5. **Interview scorecards** — structured interviews with defined rubrics
6. **Change management** — how major process changes get communicated and adopted
7. **Vendor management** — evaluation criteria, approval process, contract management

**SOPs for critical processes:**
- Customer onboarding (if >50 customers)
- Sales handoff from SDR to AE to CS
- Engineering release process
- Incident response playbook
- Contractor/vendor procurement

### Tools
| Function | Series B Tool |
|----------|--------------|
| Project/Product | Jira or Linear (with roadmapping) |
| CRM | Salesforce (full) |
| ERP/Finance | NetSuite |
| HR | Workday or BambooHR + Lattice |
| Analytics | Looker or Tableau + data warehouse |
| Customer Success | Gainsight or ChurnZero |
| Engineering | GitHub Enterprise + full CI/CD + observability |
| Security | 1Password Teams + SSO (Okta) + endpoint management |

### Communication

**At 50+ people, informal communication breaks down.** Information no longer flows naturally — it has to be architected.

**Communication stack:**
- **Monthly all-hands** (90 min): metrics deep-dive, strategy update, team Q&A
- **Weekly leadership team** (90 min): cross-functional priorities, decisions, escalations
- **Bi-weekly skip-levels** (30 min): every manager holds these with their manager's reports
- **Quarterly town halls** (2 hrs): broader context, financial update, roadmap preview
- **Written company update** (bi-weekly): CEO to all-hands via Slack/email

**The information gradient problem.** People at the top know too much. People at the bottom know too little. Fix this with a deliberate "broadcast" culture — any decision affecting more than 5 people gets written up and shared.

### Culture

**Retention becomes an existential issue.** At Series B, you have 50–150 people who've been with you through something hard. They're valuable. And they have options.

- **Career ladders** are non-negotiable by this stage. People leave when they can't see a future.
- **Manager quality** determines retention. Invest in manager training. Run manager effectiveness surveys.
- **Compensation benchmarking** quarterly. If you're more than 10% below market, you're losing people silently.
- **Culture carriers.** Identify the 10–15 people who embody your culture and make them formally responsible for transmitting it. Give them a platform.

---

## Stage 3: Series C ($30–$75M ARR, 150–500 people)

### Key Benchmarks
| Metric | Benchmark |
|--------|-----------|
| Revenue per employee | $200–$400K |
| Manager:IC ratio | 1:5–1:6 |
| Burn multiple | 0.75–1.25x |
| NRR | >115% |
| CAC payback | <9 months |
| Sales cycle (Enterprise) | 60–120 days |
| Engineering team % | 30–40% of headcount |
| Annual attrition target | <12% voluntary |
| Time-to-hire (senior) | 8–12 weeks |

### What Breaks

**Strategy execution gap.** Leadership agrees on strategy. Middle management interprets it differently. ICs execute on their interpretation. By the time work ships, it barely resembles the original strategy. Fix: strategy must cascade in writing with explicit outcomes.

**Process bureaucracy.** The processes you built at Series B start generating bureaucracy. Approval chains lengthen. Simple decisions require three meetings. The antidote is explicit process owners empowered to eliminate friction.

**Org design complexity.** Do you have functional teams (all engineers in one org) or product teams (engineers embedded in product squads)? The answer affects everything: career paths, knowledge sharing, delivery speed. Most companies get this wrong twice before getting it right.

**Geographic complexity.** First international office or remote-heavy team introduces timezone, communication, and culture challenges that don't exist when everyone is in one room.

**Leadership team dysfunction.** Seven VPs who were all individual contributors two years ago are now running $10M+ organizations. Some have grown into it. Some haven't. This is the stage where hard leadership team changes happen.

### Hiring

**Series C hiring is about depth, not breadth.** You have functional coverage — now hire people who go deep within functions.

- **Functional leaders' deputies**: VP Engineering needs a Director of Platform Engineering, Director of Product Engineering, etc.
- **Internal promotions**: 40–60% of leadership roles should be filled internally by now. If you're hiring externally for everything, you've failed at development.
- **Specialists**: Security, data science, UX research, RevOps — functions that were "shared" become dedicated.
- **General Counsel**: Legal volume justifies full-time counsel.

**Headcount planning discipline.** Every hire should have a business case. "The team is busy" is not a business case. "This role will unlock $X in revenue or save Y hours/week" is a business case.

### Process

**Process consolidation.** Audit every process. Kill anything that doesn't have a clear owner and clear outcome. The average Series C company has 40% more process than it needs.

**Key processes to have locked at Series C:**
1. **Annual planning cycle** (strategy → goals → headcount → budget)
2. **Quarterly operating review** (progress against plan, forecast, adjustments)
3. **Product development lifecycle** (discovery → design → build → launch → measure)
4. **Revenue operations** (forecasting, pipeline management, territory planning)
5. **People operations** (performance cycles, promotion cadence, compensation philosophy)
6. **Risk management** (operational, security, compliance, legal)

**Delegation architecture.** At 200+ people, the COO cannot know about every decision. Build explicit decision rights: what decisions require CEO/COO approval vs. VP vs. Director vs. IC.

### Tools

**Consolidate the tech stack.** By Series C, you have tool sprawl. The average 200-person company has 100+ SaaS tools. 40% are redundant. Consolidation saves $200–500K/year and reduces security surface.

**Must-have by Series C:**
- Enterprise SSO (Okta/Google Workspace with MFA everywhere)
- Data warehouse (Snowflake/BigQuery) + BI layer
- HRIS with performance management (Workday, Rippling, BambooHR)
- Revenue intelligence (Gong, Chorus)
- Security tooling (endpoint, SIEM basics, SOC 2 compliance)

### Communication

**Internal comms becomes a function.** You cannot rely on ad-hoc Slack and email at 200+ people. Someone needs to own internal communications.

- **Monthly CEO update** (written, 500 words max): company performance, strategic context, what's next
- **Quarterly all-hands** (2 hrs): comprehensive business review, open Q&A
- **Leadership alignment sessions** (quarterly): leadership team off-site to calibrate on strategy
- **Manager cascade** (after every major announcement): managers brief their teams with tailored context

### Culture

**Culture is now a function, not an instinct.** By Series C, your original culture-carriers are managers or have left. New people joining have never seen how you worked when you were small.

- **Culture explicitly documented** — not a values poster, a behavioral handbook
- **Onboarding redesigned** for culture transmission at scale
- **Manager enablement** — managers are your primary culture delivery mechanism; invest heavily
- **Listening infrastructure** — eNPS quarterly, exit interviews, skip-level feedback — all analyzed systematically

---

## Stage 4: Growth Stage ($75M+ ARR, 500+ people)

### Key Benchmarks
| Metric | Benchmark |
|--------|-----------|
| Revenue per employee | $300–$600K |
| Manager:IC ratio | 1:4–1:6 |
| Burn multiple (path to profitability) | <0.5x |
| NRR | >120% |
| S&M as % of revenue | 25–35% |
| R&D as % of revenue | 15–25% |
| G&A as % of revenue | 8–12% |
| Rule of 40 | >40 (growth rate + profit margin) |
| Annual attrition target | <10% voluntary |

### What Breaks

**Execution at scale.** The larger you are, the harder it is to move fast. The average decision at a 500-person company takes 3x longer than at a 50-person company. This is not inevitable — but fixing it requires explicit investment.

**Internal politics.** Org boundaries create fiefdoms. VPs protect headcount. Teams optimize for their metrics at the expense of company metrics. This is the #1 culture problem at scale.

**Innovation starvation.** The core business is optimized, but new bets are starved of resources. The people working on new initiatives are constrained by processes designed for a mature product. Structural solution required: separate P&L, separate team, different metrics.

**Middle management bloat.** Growth-stage companies often have too many managers and not enough ICs. A manager managing one other manager managing three ICs is a 3-level chain where 2 people add no value. Flatten aggressively.

### Hiring

**You're now competing for talent with FAANG.** Your advantage is mission, equity, and the ability to have impact. Candidates who want to join a Fortune 500 will not join you. Stop trying to attract them.

- **Leadership pipeline**: promote from within at 50%+ for senior roles
- **Talent density over headcount**: 30 strong engineers > 50 average engineers
- **Diverse hiring**: by this stage, lack of diversity is a business problem, not just an ethical one

### Operational Priorities at Scale

1. **Operational efficiency over growth**: headcount growth should lag revenue growth
2. **Process ownership**: every major process has a named owner accountable for outcomes
3. **Quarterly operating model**: budget vs. actual, full P&L transparency to VP level
4. **Automation**: manual operational processes that cost >40 hrs/week should be automated

---

## Cross-Stage Principles

### The Three Things That Kill Companies at Every Stage
1. **Running out of cash before finding the next unlock** — runway management is sacred
2. **Hiring the wrong person for a critical role** — one bad VP can set you back 18 months
3. **Moving too slowly** — market timing matters; perfect is the enemy of shipped

### The Org Design Progression
```
Seed:     Flat | Everyone reports to founder | No structure
Series A: Functional pods | First-line managers | Light structure
Series B: Functional departments | VPs emerge | Defined structure
Series C: Business units or product squads | Directors + VPs | Full structure
Growth:   Divisional or matrix | EVPs/SVPs | Corporate structure
```

### Revenue per Employee by Function (B2B SaaS benchmarks)
| Function | Series A | Series B | Series C | Growth |
|----------|----------|----------|----------|--------|
| Engineering | $400K | $500K | $600K | $700K |
| Sales | $250K | $350K | $450K | $500K |
| Customer Success | $300K | $400K | $500K | $600K |
| Marketing | $500K | $700K | $900K | $1M+ |
| G&A | $600K | $800K | $1M | $1.2M |

*Revenue per employee = ARR / headcount in function*

### The Management Span Rule
- **Individual contributors being managed**: 1 manager per 6–8 ICs
- **Managers being managed**: 1 director per 4–6 managers
- **Directors being managed**: 1 VP per 3–5 directors
- **VPs being managed**: 1 C-level per 5–8 VPs

Violation of this creates either manager burnout (too wide) or management theater (too narrow).

---

## Red Flags by Stage

| Stage | Red Flag | Likely Cause |
|-------|----------|-------------|
| Seed | Missed 3+ product deadlines | Wrong team or unclear prioritization |
| Series A | Churn >20% | PMF not actually found, or CS underfunded |
| Series B | >6-month sales cycle on SMB | Pricing/packaging problem |
| Series C | NRR <100% | Product-market fit eroding or CS broken |
| Growth | Rule of 40 <20 | Efficiency problem; hiring ahead of revenue |

---

*Sources: Sequoia, a16z operating frameworks; First Round Capital COO benchmarks; SaaStr metrics databases; OpenView SaaS benchmarks; Bain operational maturity models.*
