# Process Frameworks for Startup Operations

> Theory of Constraints, Lean, process mapping, automation, and change management — applied to real startup contexts, not factory floors.

---

## Part 1: Theory of Constraints (TOC) Applied to Startups

### What TOC Actually Says

Eliyahu Goldratt's core insight: **every system has exactly one constraint that limits throughput.** Improving anything other than the constraint is waste. The goal isn't to optimize every function — it's to identify the single bottleneck and exploit it until a new constraint emerges.

**The Five Focusing Steps:**
1. **Identify** the constraint — what limits the system's output?
2. **Exploit** it — get maximum output from the constraint without adding resources
3. **Subordinate** everything else — other activities serve the constraint's needs
4. **Elevate** it — add resources to increase constraint capacity
5. **Repeat** — when the constraint moves, find the new one

### Finding the Constraint in Your Startup

The constraint is almost never where people think it is. Sales thinks it's Marketing. Engineering thinks it's Product. Everyone thinks it's someone else.

**Method:** Map your value stream (see Part 3), measure throughput at each step, find the step with the lowest throughput or the highest queue in front of it.

**Common startup constraints by stage:**

| Stage | Most Common Constraint | Why |
|-------|----------------------|-----|
| Pre-PMF | Learning speed | Not enough customer feedback cycles |
| Series A | Sales capacity | Demand > sales team's ability to close |
| Series B | Engineering velocity | Product backlog growing faster than shipping rate |
| Series C | Onboarding throughput | New customer volume > CS team's onboarding capacity |
| Growth | Hiring throughput | Headcount plan > recruiting team's capacity |

### Applying TOC to Product Development

**The five visible constraints in product development:**

**1. Requirements clarity**
*Symptom:* Engineering asks for clarification mid-sprint. Tickets re-opened. Scope creep.
*Fix:* Never pull a story into sprint until acceptance criteria are written and reviewed. Product manager must be available same-day for clarification.

**2. Review and approval bottleneck**
*Symptom:* PRs sit unreviewed for >24 hours. Deploys waiting for sign-off.
*Fix:* Code review SLA: 2-hour response for small PRs (<100 lines), 4-hour for medium. Design reviews: 24-hour turnaround. Anyone waiting >SLA can escalate to manager.

**3. QA throughput**
*Symptom:* "Done" pile grows faster than QA can test. Release day crunch.
*Fix:* QA is pulled into sprint planning and sprint review. Testing starts as features finish, not all at end. Automated test coverage as a sprint exit criterion.

**4. Deployment pipeline speed**
*Symptom:* Deploy takes 45+ minutes. Engineers wait. Hotfix urgency causes dangerous shortcuts.
*Fix:* Measure deploy time weekly. Set target (10 min for most apps). Build optimization into engineering roadmap as a real ticket.

**5. Feedback loop latency**
*Symptom:* You ship features and don't know if they worked for weeks.
*Fix:* Every shipped feature has instrumented metrics reviewed within 5 business days. If no metrics exist, feature doesn't ship.

### Applying TOC to Sales

**The sales pipeline as a system of constraints:**

```
Lead generation → Qualification → Demo → Proposal → Negotiation → Close
     [X]      →      [X]      →  [X]  →    [X]   →    [X]      →  [X]

Measure: conversion rate and time-in-stage at each step.
The constraint is the step with the LOWEST conversion rate × volume.
```

**Example diagnosis:**
- Lead → Qualified: 40% conversion, 2 days
- Qualified → Demo: 80% conversion, 5 days ← High conversion but slow (queue)
- Demo → Proposal: 60% conversion, 3 days
- Proposal → Close: 30% conversion, 14 days ← **Constraint** (lowest conversion)

*Diagnosis:* Proposals are being sent to wrong buyers or proposals aren't compelling. Fix: proposal template audit, champion coaching, economic buyer access earlier in process.

---

## Part 2: Lean Operations for Tech Companies

### The Lean Toolkit (What's Actually Useful)

Lean Manufacturing was designed for car factories. Most of the original toolkit doesn't apply to software. Here's what does:

**Value Stream Mapping** — Map the full flow of work from customer request to delivery. Label value-add time vs. wait time. Most processes are 90% wait time and 10% actual work.

**5S** — Sort, Set in order, Shine, Standardize, Sustain. Applied to digital work:
- *Sort:* Delete unused tools, channels, documents
- *Set in order:* Organize information architecture so things are findable
- *Shine:* Regular cleanup sprints (documentation, tech debt, tool hygiene)
- *Standardize:* Templates, conventions, naming standards
- *Sustain:* Assign owners; entropy is the default state

**Pull vs. Push** — Don't push work onto people's plates. Pull = people take work when they have capacity. Push = work is assigned to people regardless of capacity. Most companies push; lean companies pull.

**Kaizen** — Continuous small improvements. Build this into your operating rhythm:
- Weekly: each team identifies one small improvement to their process
- Monthly: review and close out improvement items
- Quarterly: broader process retrospective

**Waste Categories (TIMWOODS) — Applied to Operations:**

| Waste Type | Factory Example | Startup Example |
|-----------|----------------|-----------------|
| **T**ransportation | Moving parts | Handing off work between tools with no integration |
| **I**nventory | Parts stockpile | Unreviewed PRs, unworked backlog items, unread reports |
| **M**otion | Worker movement | Context switching between apps / communication channels |
| **W**aiting | Machine idle | Waiting for approvals, waiting for data, waiting for decisions |
| **O**verproduction | Making more than needed | Features built that weren't validated |
| **O**verprocessing | Extra steps | 6-step approval for $200 purchase |
| **D**efects | Rework | Bug fixes, incorrect specs, miscommunicated requirements |
| **S**kills | Underutilized talent | Senior engineers doing manual QA |

**Exercise:** For your most important process, walk through each waste category and estimate hours/week wasted. This exercise typically reveals 20–40% improvement opportunities in the first pass.

### Cycle Time and Lead Time

**Lead time:** Time from when a request enters the system to when it exits (customer perspective).
**Cycle time:** Time a unit of work is actively being worked on (team perspective).

```
Lead Time = Cycle Time + Wait Time
```

Most teams only measure cycle time. Customers only experience lead time. The gap between the two is pure waste.

**Measuring in your context:**
- Engineering: Lead time = ticket created → in production. Cycle time = in progress → PR merged.
- Sales: Lead time = lead created → closed won. Cycle time = demo completed → proposal sent.
- CS: Lead time = ticket opened → customer confirms resolved. Cycle time = ticket in-progress → resolution sent.

**Improvement pattern:**
1. Measure lead time (not just cycle time)
2. Find the steps where tickets sit waiting
3. Remove the wait (automation, reduced approval layers, clearer handoff criteria)

### WIP Limits

Work-In-Progress limits prevent the multi-tasking trap. When people work on 5 things simultaneously, each thing takes 5x longer and quality drops.

**Recommended WIP limits:**
- Individual IC: 2–3 active items at once
- Team sprint: WIP = number of engineers × 1.5
- Leadership team: No more than 3 company-level priorities per quarter

**Implementation:** In Jira/Linear, add a WIP column. Set a hard limit. When the column is full, no new work starts until something ships.

---

## Part 3: Process Mapping Techniques

### When to Map a Process

Map a process when:
- It's done by more than 2 people
- It fails regularly (errors, rework, complaints)
- It needs to scale (you're about to add people or volume)
- You're automating it (you must understand the manual process first)
- You're onboarding someone new to it

Don't map processes that are genuinely ad-hoc, one-person, or will change significantly in the next 90 days.

### The Three Levels of Process Maps

**Level 1: Swim Lane Map (for cross-functional processes)**

Best for: Customer onboarding, sales-to-CS handoff, escalation handling, hiring

```
Example: Sales to CS Handoff

        | Sales AE      | Sales Ops     | CS Manager    | CS Rep        |
--------|---------------|---------------|---------------|---------------|
Step 1  | Close deal    |               |               |               |
Step 2  | Fill handoff  |               |               |               |
        | doc           |               |               |               |
Step 3  |               | Route to CS   |               |               |
Step 4  |               |               | Review &      |               |
        |               |               | assign        |               |
Step 5  |               |               |               | Send welcome  |
Step 6  |               |               |               | Schedule kick-|
        |               |               |               | off           |
```

**Level 2: Flowchart (for decision-heavy processes)**

Best for: Escalation routing, incident response, approval workflows

Use standard symbols:
- Rectangle = action/task
- Diamond = decision (yes/no branch)
- Oval = start/end
- Parallelogram = input/output

**Level 3: Work Instructions (for execution-level processes)**

Best for: Checklists, SOPs, how-to guides

Format:
```
Process: [Name]
Owner: [Role]
Last reviewed: [Date]
Trigger: [What starts this process]

Step 1: [Action] — [Who does it] — [Tool used] — [Expected output]
Step 2: ...

Exceptions:
- If [condition], then [alternative action]

Done when: [Definition of done]
```

### Process Audit Technique

Run this quarterly on your most critical processes:

**1. Walk the process** — Literally follow a unit of work from start to finish. Ask the people doing it, not the people managing it.

**2. Measure three numbers:**
- How long does it actually take? (lead time)
- How often does it go wrong? (error/rework rate)
- What's the cost of a failure? (downstream impact)

**3. Score it:**
```
PROCESS HEALTH SCORE:
Lead time vs. target:          [+2 on target / 0 delayed / -2 significantly delayed]
Error rate:                    [+2 <5% / 0 5-15% / -2 >15%]
Documented:                    [+1 yes / -1 no]
Owner named:                   [+1 yes / -1 no]
Last reviewed (< 6 months):    [+1 yes / -1 no]

Max: 7. Score <3 = needs immediate attention.
```

---

## Part 4: Automation Decision Framework

### The "Should I Automate This?" Test

Not everything should be automated. Bad automation of a broken process = faster broken process.

**The five-question filter:**

1. **Is the process stable?** If it changes monthly, automate later. Automating unstable processes locks in the wrong behavior.

2. **How often does it happen?** Weekly or more frequent = good candidate. Monthly or less = probably not worth it.

3. **What's the error rate without automation?** If the manual process is accurate 95%+ of the time, automation ROI is lower.

4. **What's the cost of failure?** Customer-facing, compliance, or financial processes deserve higher automation priority than internal reporting.

5. **Is the process well-documented?** If you can't describe it in a flowchart, you can't automate it. Document first.

### Automation ROI Calculation

```
Annual hours saved = (minutes per occurrence / 60) × occurrences per year
Annual labor cost saved = hours saved × fully-loaded cost per hour
Net annual value = labor cost saved + error reduction value + speed improvement value

Build/buy cost = development time + maintenance overhead
Payback period = build/buy cost ÷ net annual value

Rule of thumb: automate if payback period < 12 months
```

**Example:**
- Process: Weekly sales report compilation
- Time: 3 hours/week manually
- Fully-loaded cost: $75/hour
- Annual manual cost: 3 × 52 × $75 = $11,700
- Automation cost: 40 hours to build = $3,000
- Payback: 3,000 ÷ 11,700 = 3 months → **Automate**

### Automation Tiers

**Tier 1: No-code automation** (0–8 hours to implement)
- Tools: Zapier, Make (Integromat), n8n, HubSpot workflows
- Use for: Notification triggers, data syncs between tools, simple conditional routing
- Example: New customer in CRM → create CS ticket → send welcome Slack message

**Tier 2: Low-code automation** (8–40 hours to implement)
- Tools: Retool, internal scripts, Google Apps Script, Airtable Automations
- Use for: Internal dashboards, data transformation, approval workflows
- Example: Weekly metrics compilation from Salesforce + Mixpanel + HubSpot into Notion dashboard

**Tier 3: Engineered automation** (40+ hours to implement)
- Built by engineering team as product/infrastructure work
- Use for: Customer-facing workflows, compliance-critical processes, high-volume operations
- Example: Automated customer health score calculation → CS alert → playbook trigger

### Automation Prioritization Matrix

```
                    HIGH FREQUENCY
                          |
          Tier 1 now      |    Tier 2-3 now
          (quick win)     |    (high-value)
                          |
LOW VALUE ________________|________________ HIGH VALUE
                          |
          Don't bother    |    Plan for later
                          |    (when it's bigger)
                          |
                    LOW FREQUENCY
```

Place each manual process in the quadrant. Execute top-right first, Tier 1 items second.

### Automation Governance

As automation grows, it needs governance:

**Automation registry:** Maintain a list of all automations with:
- Name and description
- Owner (person responsible if it breaks)
- Tools used
- Trigger and action
- Last tested date
- Business impact if down

**Review cadence:** Quarterly review of automation registry. Kill automations nobody uses.

**Failure alerting:** Every production automation must have failure notifications sent to a named owner. Silent failures are worse than no automation.

---

## Part 5: Change Management for Process Rollouts

### Why Process Changes Fail

Most process changes fail not because the process is wrong, but because of how it's rolled out. Common failure modes:

- **Top-down dictate:** Process designed by leadership, announced to team, implemented poorly because people weren't involved and don't understand why.
- **No training:** "Here's the new process" with no demonstration or practice.
- **No feedback loop:** Process is rolled out and never adjusted based on what the team discovers.
- **No accountability:** Process is optional in practice because there are no consequences for ignoring it.
- **Old behavior still possible:** You introduce a new tool but don't turn off the old way.

### The Change Management Framework (ADKAR)

ADKAR (Awareness, Desire, Knowledge, Ability, Reinforcement) is the most practical model for operational change.

**A — Awareness:** Does everyone understand WHY the change is needed?
- Don't just announce the new process — explain what was broken about the old one
- Share the data: "Our current onboarding takes 45 days, customers who onboard faster have 2x better retention. The new process targets 21 days."

**D — Desire:** Do people want to change?
- Resistance is information. Listen to it.
- Involve front-line workers in process design. People support what they help build.
- Address WIIFM (What's In It For Me) for each affected group

**K — Knowledge:** Do people know HOW to do the new process?
- Write it down (work instructions format above)
- Run live demos and practice sessions
- Create a "first time" checklist

**A — Ability:** Can people actually do the new process?
- Identify where people get stuck (first 2 weeks of rollout)
- Have a designated expert for questions
- Remove friction: if the new process requires 3 clicks where the old required 1, people will revert

**R — Reinforcement:** Does the change stick?
- Measure adoption (are people actually using the new process?)
- Celebrate early adopters
- Address non-adoption promptly — call it out without shame

### Change Rollout Checklist

```
PRE-LAUNCH:
□ Process designed and documented
□ Stakeholders identified (people affected by change)
□ Champions identified (people who will help adoption)
□ Training materials created
□ Success metrics defined (how will you know it worked?)
□ Rollback plan documented (what if it breaks something?)
□ Launch timeline set and communicated

LAUNCH WEEK:
□ Announcement sent with WHY, WHAT, and WHEN
□ Training sessions held (at least 2 options for different schedules)
□ Feedback channel opened (Slack thread, form, or dedicated meeting)
□ Champions briefed to support peers

2-WEEK CHECK:
□ Adoption rate measured
□ Friction points documented
□ Quick fixes implemented
□ Feedback reviewed and responded to

30-DAY REVIEW:
□ Success metrics reviewed vs. baseline
□ Process adjustments made based on learnings
□ Champions recognized
□ Process documentation updated with lessons learned

90-DAY CLOSE:
□ Full adoption confirmed or non-adoption addressed
□ Process owners confirmed
□ Handoff to BAU (business as usual) operations
```

### Managing Resistance

**Types of resistance and responses:**

| Resistance Type | What It Sounds Like | Right Response |
|----------------|---------------------|----------------|
| Legitimate concern | "This process won't work because X happens" | Acknowledge, investigate, fix or explain |
| Anxiety | "I don't know how to do this" | Training, support, reassurance |
| Loss of control | "This takes away my judgment" | Involve them in design; give them ownership of part of it |
| Passive non-compliance | Silent ignoring of the new process | Direct conversation; make it visible and required |
| Organizational inertia | "We've always done it this way" | Show the cost of the status quo in concrete terms |

**The three levers of adoption:**
1. **Make the new way easier than the old way** (remove the old path if possible)
2. **Make non-adoption visible** (dashboards showing who's using the process)
3. **Connect process to meaningful outcomes** (show how it affects things people care about)

### Process Documentation Standards

Every process should have exactly one owner responsible for keeping it current.

**Minimum documentation for any process:**
- **Process name** and one-sentence purpose
- **Owner:** Named individual, not a team
- **Trigger:** What starts this process
- **Steps:** Written at the level that a new employee could execute
- **Exceptions:** Common edge cases and how to handle them
- **Done definition:** How you know the process is complete
- **Review date:** Set a future date when this gets reviewed

**Documentation debt kills scale.** The most valuable time to document is right after you've run the process for the third time — you've found the edge cases, you know the real steps, and the process is still fresh.

---

## Framework Selection Guide

| Situation | Framework |
|-----------|-----------|
| We're slow and can't figure out why | Theory of Constraints — find the bottleneck |
| We have lots of waste and overhead | Lean — waste audit (TIMWOODS) |
| Process is inconsistent across team | Process mapping — Level 1 swim lane |
| Deciding what to automate | Automation decision framework + ROI calc |
| New process keeps getting ignored | ADKAR change management |
| Unclear who's responsible | RACI or DRI framework |
| Too many decisions escalating to leadership | RAPID decision rights |

---

*Frameworks synthesized from: Eliyahu Goldratt's The Goal and Critical Chain; Womack and Jones' Lean Thinking; Prosci ADKAR model; Scaled Agile Framework (SAFe) process guidance; operational playbooks from Stripe, Airbnb, and Shopify operations teams.*
