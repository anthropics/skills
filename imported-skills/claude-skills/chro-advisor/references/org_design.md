# Org Design Reference

Spans of control, layering decisions, reorgs, title frameworks, career ladders, and the founder→professional management transition.

---

## Core Org Design Principles

1. **Structure follows strategy.** Reorg after strategy shifts, not before.
2. **Optimize for the bottleneck.** Where does work get slow? Design around that.
3. **Minimize coordination cost.** Conway's Law: your org structure becomes your product architecture. Design intentionally.
4. **Bias toward flatness until it breaks.** Adding layers adds cost and slows decisions.
5. **Reorgs have transition costs.** Relationships reset. Count the cost before you restructure.

---

## Spans of Control

Span of control = number of direct reports a manager has.

### Benchmarks

| Role Type | Optimal Span | Min | Max |
|-----------|-------------|-----|-----|
| IC manager (predictable work) | 7–10 | 5 | 12 |
| IC manager (complex/creative work) | 5–7 | 4 | 8 |
| Manager of managers | 4–6 | 3 | 7 |
| VP / Director | 4–7 | 3 | 8 |
| C-Suite | 5–9 | 4 | 10 |

**Too narrow (< 4 ICs):** Over-management, high cost per output, manager becomes a bottleneck
**Too wide (> 12 ICs):** Under-management, degraded 1:1 quality, feedback loops collapse

### Factors that allow wider spans
- Highly autonomous, senior team (L3+ ICs)
- Predictable, well-defined work (support, ops)
- Strong tooling and process (reduces manager overhead)
- Experienced manager

### Factors that require narrower spans
- High-complexity, undefined problems (research, early product)
- Junior or newly promoted team members
- High interdependence between reports (coordination overhead)
- Manager is also an IC contributor (player-coach)

---

## When to Add Management Layers

**The wrong reason to add layers:** "We need to give good people somewhere to grow."
**The right reason:** "This manager has too many direct reports to do the job well."

### Layer triggers by growth stage

**0 → 15 people:** No layers. Everyone reports to founders.

**15 → 30 people:** First managers emerge. Usually technical leads or function leads. Should still be player-coaches.

**30 → 60 people:** Second layer forms. Engineering splits into squads. Sales gets a frontline manager. Each function has a head.

**60 → 150 people:** Director layer becomes necessary in large functions. Engineering VP + Engineering Directors + Team Managers.

**150+ people:** VP layer fully staffed. Senior Director / Director split. Clear IC → M → Senior M → Director → VP paths.

### The Rule of 7

When any manager has 7 or more direct reports and:
- 1:1s are skipped regularly
- Feedback quality drops
- Manager can't answer "how is each person doing?" without checking notes

→ Time to split or hire a manager.

### Management overhead cost

Every manager layer costs 10–15% in decision speed (communication hops).
Every management role without a team = pure overhead.

**Litmus test for each management role:**
- Does this person have at least 4 ICs under them?
- Would removing this role improve decision speed?
- Is this a management job or a "we ran out of IC levels" job?

---

## Functional vs. Product Org Structures

### Functional Structure (by discipline)

```
CEO
├── VP Engineering
│   ├── Backend Team
│   ├── Frontend Team
│   └── DevOps
├── VP Product
│   ├── PM (Feature A)
│   └── PM (Feature B)
└── VP Design
    └── UX Designers
```

**Best for:** Early stage, < 100 people, single product
**Advantage:** Deep expertise development, clear career paths per discipline
**Disadvantage:** Cross-functional coordination is heavy; features require synchronization across silos

### Product/Pod Structure (by product area)

```
CEO
├── Product Area A (autonomous team)
│   ├── EM
│   ├── PM
│   └── Designer
├── Product Area B (autonomous team)
│   ├── EM
│   ├── PM
│   └── Designer
└── Platform (shared services)
    └── Platform EM + team
```

**Best for:** Multiple products or large user segments, 50+ in product/eng
**Advantage:** Speed and autonomy; less cross-team coordination for most features
**Disadvantage:** Duplication risk; harder to maintain technical coherence; harder career paths

### When to shift from Functional → Product org
- You have 2+ distinct product lines that rarely share features
- Cross-functional feature delivery takes > 3 sprints of coordination overhead
- Teams are > 8 engineers and still waiting on shared resources

### Hybrid / Matrix (avoid unless necessary)
Matrix reporting (e.g., engineer reports to EM + PM) creates accountability confusion. Avoid at < 500 people.

---

## Title Frameworks

### The Problem with Title Inflation

Early startups over-title to compete with cash. "VP of Engineering" with 2 reports. "Head of Marketing" with no team.

**Consequences:**
- Can't add leadership above inflated titles without awkward conversations
- Candidates from mature companies expect scope commensurate with titles
- Internal equity breaks when the same title means different things

### Preventing Title Inflation

**Rule 1:** VP titles require managing managers (not just ICs).
**Rule 2:** Director titles require managing multiple ICs or a large function.
**Rule 3:** No more than one "Head of X" per function.
**Rule 4:** Document scope expectations per title before making offers.

### Engineering Title Ladder (example)

| Title | Level | Scope | Reports |
|-------|-------|-------|---------|
| Software Engineer I | L1 | Executes defined tasks | — |
| Software Engineer II | L2 | Independent delivery | — |
| Senior Software Engineer | L3 | Leads features, mentors | — |
| Staff Software Engineer | L4 | Cross-team technical leadership | — |
| Principal Software Engineer | L5 | Company-wide technical direction | — |
| Distinguished Engineer | L6 | External recognition, defining practice | — |
| Engineering Manager | M1 | Team of 4–8 engineers | 4–8 ICs |
| Senior Engineering Manager | M2 | Larger team or manager of managers | 2–4 managers |
| Director of Engineering | M3 | Functional area | Multiple managers |
| VP of Engineering | M4 | Engineering org | Directors |
| CTO | M5 | Technical organization + strategy | VPs |

**IC vs. Management track:** Explicitly separate. Senior ICs should not need to move to management for career advancement. Staff/Principal/Distinguished track provides this.

### Go-to-Market Title Ladder (example)

| Title | Level | Focus |
|-------|-------|-------|
| SDR / BDR | S1 | Outbound prospecting |
| Account Executive I | S2 | SMB closing |
| Account Executive II | S3 | Mid-market closing |
| Senior Account Executive | S4 | Enterprise closing |
| Principal / Strategic AE | S5 | Named accounts, complex deals |
| Sales Manager | M1 | 6–8 reps |
| Director of Sales | M2 | Multiple teams or segments |
| VP of Sales | M3 | Full sales org |
| CRO | M4 | Revenue org (sales + CS + marketing) |

---

## Career Ladders

A career ladder is a documented set of expectations per level. Not aspirational — behavioral. "What does a P3 engineer do that a P2 doesn't?"

### Why career ladders matter for HR

1. **Retention:** Employees can see where they're going
2. **Consistency:** Managers use the same criteria for promotions
3. **Compensation:** Bands anchor to levels; levels require definitions
4. **Equity:** Removes "who's the manager's favorite" from promotion decisions

### Career Ladder Structure

For each level, define 4 dimensions:

**1. Scope** — How big is the problem space? Team / cross-team / org-wide / company-wide?
**2. Impact** — How does work connect to outcomes? (Task → Feature → Product → Business)
**3. Craft** — Technical/functional skill expectations
**4. Influence** — How does this person improve others? (Self → peers → team → org)

**Example: Senior Software Engineer (L3) vs. Staff Software Engineer (L4)**

| Dimension | L3 (Senior SWE) | L4 (Staff SWE) |
|-----------|----------------|----------------|
| Scope | Owns features or services | Owns technical domains across teams |
| Impact | Ships features that improve user outcomes | Shapes technical direction for a product area |
| Craft | Writes high-quality code, good design skills | Sets coding standards, contributes to architecture |
| Influence | Mentors L1–L2, code reviews | Mentors L3+, identifies org-wide technical gaps |

### How to build a career ladder from scratch

1. **Interview your best performers** — "What do you do that your junior peers don't?" Collect behaviors, not aspirations.
2. **Draft 3 levels** — Don't start with 6. Start with junior, mid, senior. Add staff/principal only when you have enough people to warrant it.
3. **Manager calibration** — Every manager rates 5 current employees against the draft. Gaps surface immediately.
4. **Publish and iterate** — Don't wait for perfection. A 70% ladder shipped is better than a 100% ladder in a drawer.

---

## Reorg Playbook

### When reorgs are necessary
- Strategy pivot requires different team structure (e.g., single product → multi-product)
- Acquisition or team merger
- Function is genuinely too slow due to coordination overhead
- Leadership departure creates structural opportunity

### When reorgs are a mistake
- "We need to shake things up" (disruption for its own sake)
- Avoiding a specific personnel decision (use the right tool)
- Solving a cultural problem with a structural change
- Reacting to one team's complaint without systemic evidence

### Reorg Process (4–8 weeks)

**Week 1–2: Diagnose**
- Map current org: every role, reporting line, team output
- Identify where work is slow, duplicated, or falling through cracks
- Interview 5–10 people across teams: "What takes longer than it should? What decisions are hard to make?"

**Week 3–4: Design options**
- Draft 2–3 structural alternatives
- For each: estimated coordination costs, manager span impact, open roles created
- Validate with CEO + 1–2 trusted operators. Don't crowdsource the design.

**Week 5–6: Decide and prepare**
- Select option; finalize all reporting changes
- Prepare communications for every affected person (individual conversations before all-hands)
- Write the "why" — employees need to understand the business reason, not just the result

**Week 7–8: Communicate and implement**
- Individual conversations with all manager+ changes (first)
- Team-level conversations with managers (second)
- All-hands with full context (third)
- Updated org chart published within 24 hours of announcement

### Communication sequence (non-negotiable)

1. Affected individuals first (private, before anything else)
2. Affected managers second (to prepare for team conversations)
3. Full team/company third (all-hands or company note)
4. External (clients, board) only if materially impacted

**Never:** Email blast first. No individual conversations. Discovered on the org chart.

---

## Founder → Professional Management Transition

The most common scaling failure point in startups.

### Stage 1: Founder-Led (0–30 people)

Founders make all decisions, know everyone personally, set culture through behavior. Works because trust and context are built directly.

**What breaks:**
- Decisions bottleneck at founders
- New hires don't get enough context (founders can't be everywhere)
- Culture transmitted through osmosis, not documentation

### Stage 2: First Managers (30–80 people)

Founders can no longer manage all ICs. First manager layer typically = promoted high performers.

**The "brilliant IC → struggling manager" trap:**
- Individual contributor skills ≠ management skills
- Promoted ICs often continue doing IC work while ignoring management work
- No one holds them accountable to management output (1:1 quality, team health, performance feedback)

**What to do:**
- Explicit manager training before promotion (not after)
- Management KPIs separate from IC KPIs
- Peer community for new managers (monthly cohort session)
- HR check-ins on manager health at 30/60/90 days

### Stage 3: Professional Management (80–200 people)

External hires at Director/VP level bring professional management skills but lack company context.

**Common failure modes:**
- Hired "too senior" — VP who's used to 200-person teams in a 50-person function
- Culture clash — Big-company manager who adds process that kills startup speed
- Authority vacuum — External VP doesn't earn trust; team ignores them; founder continues to bypass hierarchy

**Mitigation:**
- Hiring bar: Has this person scaled from this stage to 2x this stage before? Not managed a team at 2x — built a team to 2x.
- Explicit onboarding on "how we make decisions here"
- 90-day milestones focused on relationship-building before any structural changes
- Founders explicitly hand off ownership and reinforce new manager's authority publicly

### Stage 4: Founder Transition from Operator to Executive

The hardest personal transition. Founder moves from doing to enabling.

**Signs you haven't made the transition:**
- You're still in every technical decision
- Teams come to you instead of their manager for approvals
- You know more about the team's work than the manager does
- Managers feel they need to check in before acting

**What the transition requires:**
- Explicit authority delegation in writing (not just verbal)
- Willingness to let managers make decisions you'd make differently
- Redirecting team members to their manager consistently
- Measuring managers on outcomes, not just process adherence
- Letting managers hire and fire without founder override (except final call on VPs)
