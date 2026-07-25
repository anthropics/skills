# Operational Cadence: Meetings, Async, Decisions, and Reporting

> The rhythm of your company determines its output. Bad cadence = constant context-switching, decisions made without information, and a leadership team that's always reactive.

---

## Philosophy

**Meetings are a tax.** Every hour in a meeting is an hour not spent building, selling, or serving customers. A good cadence minimizes meeting time while ensuring the right people have the right information at the right time.

**Async is default, sync is exception.** Most information sharing and routine updates should happen in writing. Reserve synchronous time for things that genuinely require real-time discussion: decisions with significant disagreement, complex problem-solving, relationship-building.

**Cadence serves strategy.** The calendar reflects priorities. If you're doing monthly all-hands but weekly status updates, you've inverted the importance.

---

## Meeting Cadence Templates

### Daily Operations

#### Daily Standup (Engineering / Product Teams)
**Format:** Async-first (Slack/Loom); sync only if blocked  
**Sync duration:** 15 minutes max  
**Participants:** Team (5–10 people)  
**Facilitator:** Team lead or rotating

```
ASYNC FORMAT (post in #standup channel):
Yesterday: [What I completed]
Today: [What I'm working on]
Blocked: [Anything blocking me — tag the person who can unblock]
```

**Rules:**
- No status reporting in sync standup if everyone can read the async update
- Standups are not problem-solving sessions — take issues offline
- Skip standup if the team has a full-team session that day
- Kill standup if the team consistently has nothing blocked; replace with async

#### Daily Leadership Check-in (COO)
**Format:** Async only — read, don't meet  
**Time:** 8:00–8:30 AM

**COO morning read:**
1. Yesterday's key metrics dashboard (5 min)
2. Overnight Slack/email escalations (5 min)
3. Today's decisions needed list (5 min)
4. Any P0/P1 incidents (check status page + on-call logs)

---

### Weekly Cadence

#### Leadership Sync (Weekly)
**Duration:** 60–90 minutes  
**Participants:** C-suite + VP level  
**Owner:** COO (or CEO)  
**Day/Time:** Monday or Tuesday, morning

```
AGENDA TEMPLATE:
00:00–10:00  Metrics pulse (pre-read required — no presenting charts)
  - Revenue: ACV, pipeline, churn delta
  - Product: shipped last week, blockers this week
  - Engineering: incidents, velocity
  - CS: escalations, NPS delta
  - People: open reqs, attrition flag

10:00–45:00  Priority items (submitted in advance, max 3)
  - Item 1: [Owner: Name] [Decision needed / FYI / Input needed]
  - Item 2: [Owner: Name]
  - Item 3: [Owner: Name]

45:00–60:00  Parking lot / open
  - Anything not covered
  - Next week flagging
```

**Pre-meeting requirements:**
- Metrics dashboard updated by EOD Friday
- Priority items submitted by Sunday 6 PM
- Anyone who hasn't read the pre-read gets no floor time

**Output:** Decision log updated with outcomes, action items assigned in tracking system

#### 1:1 (Manager ↔ Direct Report)
**Duration:** 30–45 minutes  
**Frequency:** Weekly (skip-levels: bi-weekly)  
**Owner:** Report (the direct report sets agenda)

```
1:1 STRUCTURE:
[5 min]  What's on your mind / temperature check
[15 min] Their agenda — what they want to discuss
[10 min] Manager agenda — feedback, context, decisions
[5 min]  Action items review from last week
```

**1:1 anti-patterns to eliminate:**
- Using 1:1 for status updates (that's what standups are for)
- Manager dominating the agenda
- Skipping because "things are fine"
- No written record of what was discussed

**Private 1:1 doc:** Every manager/report pair maintains a shared doc with running notes, action items, and career development thread.

#### Cross-Functional Weekly Sync
**Duration:** 45 minutes  
**Participants:** 2–4 team leads with shared dependencies  
**Examples:** Product + Engineering, Sales + CS, Marketing + Sales

```
AGENDA:
00–10  Shared metrics (things both teams care about)
10–30  Active collaboration items — what needs coordination this week
30–40  Blockers + dependencies (what do I need from your team?)
40–45  Upcoming: what's coming that the other team should know about
```

---

### Monthly Cadence

#### All-Hands / Town Hall
**Duration:** 60–90 minutes  
**Participants:** Entire company  
**Owner:** CEO + functional heads  
**Format:** In-person preferred; video if distributed

```
ALL-HANDS AGENDA (60 min version):
00–05   Opening — CEO sets the tone
05–20   Business update
        - Where we are vs. plan (actuals vs. budget)
        - Key wins and learning moments from last month
        - What we're focused on this month
20–40   Functional spotlights (2 functions, 10 min each)
        - What we shipped / what we did
        - What we learned
        - What's next
40–55   Open Q&A (no screened questions — take everything)
55–60   Closing

ALL-HANDS PREP CHECKLIST:
□ CEO talking points reviewed 48h in advance
□ Metrics slides reviewed by Finance for accuracy
□ Q&A prep — leadership team briefs on likely questions
□ Recording setup confirmed
□ Async option for timezones (recording posted within 2h)
□ Action items from Q&A captured and published within 24h
```

#### Monthly Business Review (MBR)
**Duration:** 2 hours  
**Participants:** Leadership team  
**Owner:** COO

```
MBR AGENDA:
00–20   Financial review (Finance presents)
        - Revenue vs. plan, by segment
        - Burn rate, runway
        - Headcount actual vs. plan
        - Key cost drivers

20–60   Functional reviews (each VP, 8 min each)
        Standard template per function:
        - Metrics: [3 key metrics vs. prior month vs. plan]
        - Wins: [top 2-3 wins]
        - Gaps: [where we missed and why]
        - Next 30 days: [top 3 priorities]

60–90   Strategic topics (pre-submitted)
        - Items requiring cross-functional decision
        - Risks or issues needing leadership visibility

90–110  Decisions and action items
        - Document decisions made
        - Assign owners and deadlines

110–120 Retrospective
        - What's working in how we operate?
        - What needs to change?
```

**MBR pre-read package** (published 48h before):
- Financial summary (1 page)
- Each function's 1-pager (see template below)

```
FUNCTIONAL 1-PAGER TEMPLATE:
Function: [Name]          Month: [Month Year]
Owner: [VP Name]

TOP METRICS:
| Metric | Target | Actual | vs. LM | vs. Plan |
|--------|--------|--------|--------|----------|
| [M1]   |        |        |        |          |
| [M2]   |        |        |        |          |
| [M3]   |        |        |        |          |

WINS (2-3 bullets):
•
•

GAPS (be honest — no spin):
•
•

DEPENDENCIES (what I need from other teams):
•

NEXT 30 DAYS (top 3 priorities):
1.
2.
3.
```

---

### Quarterly Cadence

#### Quarterly Business Review (QBR)
**Duration:** Half day (4 hours)  
**Participants:** Leadership team + key functional leads  
**Owner:** CEO + COO

```
QBR AGENDA (4 hours):
PART 1: Look back (90 min)
  - CEO: Business context and narrative (15 min)
  - Finance: Full quarter P&L review (20 min)
  - Each function: 10-min review against OKRs
    Format: Hit/Miss/Partial for each objective + root cause

PART 2: Look forward (90 min)
  - Product/Engineering: What ships next quarter (20 min)
  - Sales/Marketing: Pipeline and demand plan (20 min)
  - People: Headcount plan and key hires (15 min)
  - Finance: Budget and forecast (20 min)
  - Cross-functional dependencies (15 min)

PART 3: Strategic discussion (60 min)
  - 1–2 strategic topics requiring deep discussion
  - Pre-submitted and pre-read

PART 4: OKR setting for next quarter (30 min)
  - Draft OKRs reviewed and challenged
  - Final OKRs locked or assigned for next week finalization
```

#### Quarterly Leadership Off-site
**Duration:** 1–2 days (Series B+)  
**Participants:** C-suite + VPs  
**Purpose:** Strategy alignment, relationship building, hard conversations

**Off-site agenda principles:**
- No laptops during sessions (phones away)
- At least 50% discussion, max 50% presentation
- Include one session on how the leadership team is functioning (not just what the business is doing)
- Output: 1-page summary of decisions and commitments shared with the company

---

### Annual Cadence

#### Annual Planning Cycle
**Timeline:** Start 8–10 weeks before fiscal year end

```
ANNUAL PLANNING TIMELINE:
Week -10: Company strategic priorities draft (CEO + COO)
Week -8:  Revenue model + market analysis (Finance + Sales)
Week -7:  Functional goal-setting begins
Week -6:  Headcount planning by function
Week -5:  Draft plans reviewed by COO
Week -4:  Cross-functional dependency alignment
Week -3:  Budget finalization
Week -2:  Board review (if applicable)
Week -1:  Final company OKRs published
Week 0:   Year kick-off all-hands
```

#### Year Kick-off All-Hands
**Duration:** 2–4 hours  
**Participants:** Entire company  
**Purpose:** Align entire company on year strategy and goals

```
KICK-OFF AGENDA:
- Last year retrospective: What we accomplished, what we learned
- Market context: Why now, why us
- Year strategy: The 2-3 things that matter most
- OKRs: Company-level goals, each function's goals
- Culture: How we'll work together
- Q&A: Open and honest
```

---

## Async Communication Frameworks

### The Writing-First Culture

All communication defaults to written unless real-time is genuinely necessary. This is how you scale decision-making without scaling meetings.

**Written first means:**
- Decisions are documented before they're communicated
- Updates are published before questions are asked
- Problems are described before solutions are proposed

### Slack Channel Architecture

```
REQUIRED CHANNELS:
#announcements       Read-only. Major company announcements only.
#general             Company-wide conversation
#leadership-public   Leadership decisions visible to all (transparency)
#incidents           P0/P1 incidents only. Auto-resolved when incident is closed.
#metrics             Automated metric updates. No discussion here.
#wins                Customer wins, team wins. Culture channel.

FUNCTIONAL CHANNELS:
#engineering, #product, #sales, #marketing, #cs, #people, #finance

PROJECT CHANNELS:
#proj-[name]         Temporary. Archive when project ships.

DECISION CHANNELS:
#decisions           All cross-team decisions logged here with context
```

**Anti-patterns to eliminate:**
- DMs for work decisions (decisions belong in channels, visible to team)
- @channel abuse (train people — this means everyone stops what they're doing)
- Thread avoidance (all replies go in threads, period)
- Multiple channels for same function (merge aggressively)

### Async Decision Template

When a decision needs input but doesn't require a meeting:

```
DECISION REQUEST (post in #decisions):

**Context:** [1-3 sentences on why this decision is needed]

**Options considered:**
A) [Option A] — Pros: X. Cons: Y.
B) [Option B] — Pros: X. Cons: Y.

**Recommendation:** [Your recommendation and why]

**Input needed from:** @person1, @person2 (tag specific people)

**Decide by:** [Date/Time — give at least 24 hours]

**If no response:** [Default action if no input received]
```

### Loom / Video for Async Communication

Use async video for:
- Explaining complex technical architecture
- Walking through a design or document with context
- Giving feedback that needs tone/nuance
- Team updates that would otherwise be a meeting

**Loom best practices:**
- Keep under 5 minutes; break up anything longer
- Always include a summary comment with key points
- Ask viewers to leave timestamp comments for specific questions

---

## Decision-Making Frameworks

### RAPID

The most practical decision-making framework for startups scaling to enterprises.

| Role | Meaning | Responsibility |
|------|---------|---------------|
| **R** — Recommend | Proposes decision with analysis | Does the work, gathers input, makes recommendation |
| **A** — Agree | Must agree before decision is final | Has veto power; should be used sparingly |
| **P** — Perform | Executes the decision | Consulted during recommendation phase |
| **I** — Input | Consulted for perspective | Shares point of view; not binding |
| **D** — Decide | Makes the final call | One person only — groups don't decide |

**How to use RAPID:**
1. For every significant decision, explicitly assign R, A, P, I, D before work begins
2. The D role is always one person — never a committee
3. Agree (A) roles should be limited to 2–3 people maximum; more = paralysis
4. Post the RAPID in the decision doc so everyone knows the structure

**Example application:**
```
Decision: Migrate from PostgreSQL to distributed database
R: VP Engineering
A: CTO, COO (for cost implications)
P: Infrastructure team
I: Product leads, Finance
D: CTO
```

### RACI

Better for ongoing processes than one-time decisions. Use RACI for recurring operational responsibilities.

| Role | Meaning |
|------|---------|
| **R** — Responsible | Does the work |
| **A** — Accountable | Owns the outcome; one person only |
| **C** — Consulted | Input before decisions/actions |
| **I** — Informed | Told of decisions/actions after the fact |

**RACI matrix template:**

```
PROCESS: Customer Escalation Handling

Task                    | CS Lead | VP CS | Eng Lead | CEO
------------------------|---------|-------|----------|----
Receive escalation      | R       | I     | I        | -
Diagnose issue          | R       | C     | C        | -
Communicate to customer | R       | A     | -        | I (major)
Resolve technical issue | C       | -     | R        | -
Close escalation        | R       | A     | I        | -
Post-mortem (P0/P1)    | C       | A     | R        | I
```

**Common RACI mistakes:**
- Multiple A roles (breaks accountability)
- R and A always same person (defeats the purpose)
- Too many C roles (everyone's consulted, nothing moves)
- Not distinguishing C from I (different obligations)

### DRI (Directly Responsible Individual)

Apple's framework; used widely in fast-moving tech companies. Simpler than RAPID/RACI for internal use.

**The rule:** Every project, deliverable, and decision has exactly one DRI. The DRI is the person who gets credit when it succeeds and gets called on when it fails. No DRI = no accountability.

**DRI requirements:**
- Listed by name in every project brief
- Has authority to make decisions within scope
- Is responsible for communicating status
- Cannot blame lack of resources — their job is to escalate when blocked

**DRI vs. RACI:** Use DRI for project ownership and RACI for process ownership. They complement each other.

### Decision Log

Every significant decision gets logged. Significant = affects more than one team, costs more than $10K, or is difficult to reverse.

```
DECISION LOG FORMAT:

Date: [YYYY-MM-DD]
Decision: [One sentence summary]
Context: [Why was this decision needed? What was the situation?]
Options considered: [What alternatives were evaluated?]
Decision made: [What was decided?]
Rationale: [Why this option?]
Owner: [Who made the final call?]
Reversible: [Yes / No / Partially]
Review date: [When should this decision be revisited?]
Outcome: [Filled in later — what actually happened?]
```

---

## Reporting Templates

### Weekly CEO/COO Dashboard

```
COMPANY HEALTH — WEEK OF [DATE]

REVENUE
  ARR:                  $[X]M   (vs. plan: +/-X%, vs. LW: +/-X%)
  New ARR this week:    $[X]K
  Churned ARR:          $[X]K
  Pipeline (90-day):    $[X]M

PRODUCT
  Shipped this week:    [Brief list]
  P0/P1 incidents:      [Count] — [1-line summary if any]
  Deploy frequency:     [X per week]

CUSTOMER
  Active customers:     [X]
  NPS (rolling 30d):    [X]
  Open escalations:     [X]   (P0: [X], P1: [X])

PEOPLE
  Headcount:            [X] (vs. plan: [X])
  Open reqs:            [X]
  Attrition (30d):      [X]

CASH
  Cash on hand:         $[X]M
  Burn (last 30d):      $[X]M
  Runway:               [X] months

🔴 ISSUES (needs leadership attention):
  •
  •

🟡 WATCH (monitor, no action yet):
  •

🟢 WINS:
  •
```

### Monthly Investor/Board Update

```
[COMPANY NAME] — MONTHLY UPDATE — [MONTH YEAR]

THE HEADLINE
[2-3 sentences: what was the defining story of this month?]

KEY METRICS
| Metric | [Month] | vs. Prior | vs. Plan |
|--------|---------|-----------|----------|
| ARR | | | |
| MRR Added | | | |
| Churn | | | |
| NRR | | | |
| Burn | | | |
| Runway | | | |

WINS
1. [Specific, concrete win with numbers]
2. [Second win]
3. [Third win]

CHALLENGES
1. [Honest description of challenge + what you're doing about it]
2. [Second challenge]

KEY DECISIONS MADE
• [Decision + brief rationale]

ASKS FROM INVESTORS
• [Specific ask with context — intros, advice, etc.]

NEXT MONTH PRIORITIES
1.
2.
3.
```

### Quarterly OKR Progress Report

```
Q[X] OKR PROGRESS — [COMPANY NAME]

SCORING GUIDE:
🟢 On track (>70% confidence of hitting target)
🟡 At risk (50-70% confidence)
🔴 Off track (<50% confidence)

COMPANY OBJECTIVES:

O1: [Objective title]
  KR1.1: [Key Result] ............... [X]% 🟢
  KR1.2: [Key Result] ............... [X]% 🟡
  Objective confidence: 🟢 | Notes: [1 line]

O2: [Objective title]
  KR2.1: [Key Result] ............... [X]% 🔴
  KR2.2: [Key Result] ............... [X]% 🟢
  Objective confidence: 🟡 | Notes: [1 line]

FUNCTIONAL OBJECTIVES:
[Same format per function]

OVERALL QUARTER HEALTH: 🟡
Summary: [2-3 sentences on overall trajectory]

TOP 3 ACTIONS TO GET BACK ON TRACK:
1. [Action + owner + deadline]
2.
3.
```

---

## Cadence Anti-Patterns to Eliminate

| Anti-Pattern | What It Looks Like | Fix |
|---|---|---|
| **Meeting creep** | Calendar blocks added over time, never removed | Quarterly calendar audit — delete all recurring meetings, re-add only what's essential |
| **Update theater** | Meetings where people read from slides | Require pre-reads; ban in-meeting presentations |
| **Decision avoidance** | Topics recur across multiple meetings | Assign a D (decider) before the meeting. If no D, don't hold the meeting. |
| **Sync for async** | Using meetings for information sharing | Move updates to Loom/Slack; protect sync time for discussion |
| **HIPPO problem** | Highest-paid person in room wins | Structure discussions so data is presented before opinions |
| **Retrospective theater** | Retros with no action items | Every retro must produce ≥1 committed change |
| **Silent agenda** | Agenda not shared until meeting starts | Agendas published 24h in advance, required reading |

---

*Cadence framework synthesized from Amazon's PR/FAQ culture, Google's OKR playbook, GitLab's remote work handbook, and operational patterns from 50+ Series A–C companies.*
