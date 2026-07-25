---
name: "strategic-alignment"
description: "Cascades strategy from boardroom to individual contributor. Detects and fixes misalignment between company goals and team execution. Covers strategy articulation, cascade mapping, orphan goal detection, silo identification, communication gap analysis, and realignment protocols. Use when teams are pulling in different directions, OKRs don't connect, departments optimize locally at company expense, or when user mentions alignment, strategy cascade, silo, conflicting OKRs, or strategy communication."
license: MIT
metadata:
  version: 1.0.0
  author: Alireza Rezvani
  category: c-level
  domain: strategic-alignment
  updated: 2026-03-05
  python-tools: alignment_checker.py
  frameworks: alignment-playbook
---

# Strategic Alignment Engine

Strategy fails at the cascade, not the boardroom. This skill detects misalignment before it becomes dysfunction and builds systems that keep strategy connected from CEO to individual contributor.

## Keywords
strategic alignment, strategy cascade, OKR alignment, orphan OKRs, conflicting goals, silos, communication gap, department alignment, alignment checker, strategy articulation, cross-functional, goal cascade, misalignment, alignment score

## Quick Start

```bash
python scripts/alignment_checker.py    # Check OKR alignment: orphans, conflicts, coverage gaps
```

## Core Framework

The alignment problem: **The further a goal gets from the strategy that created it, the less likely it reflects the original intent.** This is the organizational telephone game. It happens at every stage. The question is how bad it is and how to fix it.

### Step 1: Strategy Articulation Test

Before checking cascade, check the source. Ask five people from five different teams:
**"What is the company's most important strategic priority right now?"**

**Scoring:**
- All five give the same answer: ✅ Articulation is clear
- 3–4 give similar answers: 🟡 Loose alignment — clarify and communicate
- < 3 agree: 🔴 Strategy isn't clear enough to cascade. Fix this before fixing cascade.

**Format test:** The strategy should be statable in one sentence. If leadership needs a paragraph, teams won't internalize it.
- ❌ "We focus on product-led growth while maintaining enterprise relationships and expanding our international presence and investing in platform capabilities"
- ✅ "Win the mid-market healthcare segment in DACH before Series B"

### Step 2: Cascade Mapping

Map the flow from company strategy → each level of the organization.

```
Company level:  OKR-1, OKR-2, OKR-3
    ↓
Dept level:     Sales OKRs, Eng OKRs, Product OKRs, CS OKRs
    ↓
Team level:     Team A OKRs, Team B OKRs...
    ↓
Individual:     Personal goals / rocks
```

**For each goal at every level, ask:**
- Which company-level goal does this support?
- If this goal is 100% achieved, how much does it move the company goal?
- Is the connection direct or theoretical?

### Step 3: Alignment Detection

Three failure patterns:

**Orphan goals:** Team or individual goals that don't connect to any company goal.
- Symptom: "We've been working on this for a quarter and nobody above us seems to care"
- Root cause: Goals set bottom-up or from last quarter's priorities without reconciling to current company OKRs
- Fix: Connect or cut. Every goal needs a parent.

**Conflicting goals:** Two teams' goals, when both succeed, create a worse outcome.
- Classic example: Sales commits to volume contracts (revenue), CS is measured on satisfaction scores. Sales closes bad-fit customers; CS scores tank.
- Fix: Cross-functional OKR review before quarter begins. Shared metrics where teams interact.

**Coverage gaps:** Company has 3 OKRs. 5 teams support OKR-1, 2 support OKR-2, 0 support OKR-3.
- Symptom: Company OKR-3 consistently misses; nobody owns it
- Fix: Explicit ownership assignment. If no team owns a company OKR, it won't happen.

See `scripts/alignment_checker.py` for automated detection against your JSON-formatted OKRs.

### Step 4: Silo Identification

Silos exist when teams optimize for local metrics at the expense of company metrics.

**Silo signals:**
- A department consistently hits their goals while the company misses
- Teams don't know what other teams are working on
- "That's not our problem" is a common phrase
- Escalations only flow up; coordination never flows sideways
- Data isn't shared between teams that depend on each other

**Silo root causes:**
1. **Incentive misalignment:** Teams rewarded for local metrics don't optimize for company metrics
2. **No shared goals:** When teams share a goal, they coordinate. When they don't, they drift.
3. **No shared language:** Engineering doesn't understand sales metrics; sales doesn't understand technical debt
4. **Geography or time zones:** Silos accelerate when teams don't interact organically

**Silo measurement:**
- How often do teams request something from each other vs. proceed independently?
- How much time does it take to resolve a cross-functional issue?
- Can a team member describe the current priorities of an adjacent team?

### Step 5: Communication Gap Analysis

What the CEO says ≠ what teams hear. The gap grows with company size.

**The message decay model:**
- CEO communicates strategy at all-hands → managers filter through their lens → teams receive modified version → individuals interpret further

**Gap sources:**
- **Ambiguity:** Strategy stated at too high a level ("grow the business") lets each team fill in their own interpretation
- **Frequency:** One all-hands per quarter isn't enough repetition to change behavior
- **Medium mismatch:** Long written strategy doc for teams that respond to visual communication
- **Trust deficit:** Teams don't believe the strategy is real ("we've heard this before")

**Gap detection:**
- Run the Step 1 articulation test across all levels
- Compare what leadership thinks they communicated vs. what teams say they heard
- Survey: "What changed about how you work since the last strategy update?"

### Step 6: Realignment Protocol

How to fix misalignment without calling it a "realignment" (which creates fear).

**Step 6a: Don't start with what's wrong**
Starting with "here's our misalignment" creates defensiveness. Start with "here's where we're heading and I want to make sure we're connected."

**Step 6b: Re-cascade in a workshop, not a memo**
Alignment workshops are more effective than documents. Get company-level OKR owners and department leads in a room. Map connections. Find gaps together.

**Step 6c: Fix incentives before fixing goals**
If department heads are rewarded for local metrics that conflict with company goals, no amount of goal-setting fixes the problem. The incentive structure must change first.

**Step 6d: Install a quarterly alignment check**
After fixing, prevent recurrence. See `references/alignment-playbook.md` for quarterly cadence.

---

## Alignment Score

A quick health check. Score each area 0–10:

| Area | Question | Score |
|------|----------|-------|
| Strategy clarity | Can 5 people from different teams state the strategy consistently? | /10 |
| Cascade completeness | Do all team goals connect to company goals? | /10 |
| Conflict detection | Have cross-team OKR conflicts been reviewed and resolved? | /10 |
| Coverage | Does each company OKR have explicit team ownership? | /10 |
| Communication | Do teams' behaviors reflect the strategy (not just their stated understanding)? | /10 |

**Total: __ / 50**

| Score | Status |
|-------|--------|
| 45–50 | Excellent. Maintain the system. |
| 35–44 | Good. Address specific weak areas. |
| 20–34 | Misalignment is costing you. Immediate attention required. |
| < 20 | Strategic drift. Treat as crisis. |

---

## Key Questions for Alignment

- "Ask your newest team member: what is the most important thing the company is trying to achieve right now?"
- "Which company OKR does your team's top priority support? Can you trace the connection?"
- "When Team A and Team B both hit their goals, does the company always win? Are there scenarios where they don't?"
- "What changed in how your team works since the last strategy update?"
- "Name a decision made last week that was influenced by the company strategy."

## Red Flags

- Teams consistently hit goals while company misses targets
- Cross-functional projects take 3x longer than expected (coordination failure)
- Strategy updated quarterly but team priorities don't change
- "That's a leadership problem, not our problem" attitude at the team level
- New initiatives announced without connecting them to existing OKRs
- Department heads optimize for headcount or budget rather than company outcomes

## Integration with Other C-Suite Roles

| When... | Work with... | To... |
|---------|-------------|-------|
| New strategy is set | CEO + COO | Cascade into quarterly rocks before announcing |
| OKR cycle starts | COO | Run cross-team conflict check before finalizing |
| Team consistently misses goals | CHRO | Diagnose: capability gap or alignment gap? |
| Silo identified | COO | Design shared metrics or cross-functional OKRs |
| Post-M&A | CEO + Culture Architect | Detect strategy conflicts between merged entities |

## Detailed References
- `scripts/alignment_checker.py` — Automated OKR alignment analysis (orphans, conflicts, coverage)
- `references/alignment-playbook.md` — Cascade techniques, quarterly alignment check, common patterns
