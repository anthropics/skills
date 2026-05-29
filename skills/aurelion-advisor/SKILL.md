---
name: "AURELION Advisor"
version: "1.0.0"
description: "A strategic planning skill that acts as a personal career GPS — helping structure advancement goals, investigate career scenarios, map stakeholder dynamics, and build a methodology library using the AURELION 5-floor framework."
author: "chase-key"
license: "MIT"
categories:
  - career
  - planning
  - strategy
  - productivity
homepage: "https://github.com/chase-key/aurelion-advisor-lite"
---

# AURELION Advisor — Career Strategy & Planning

## What This Skill Does

AURELION Advisor is a personal strategic planning engine. It helps professionals organize their career knowledge, plan advancement, document methodologies, and think clearly about long-term direction — using the same structured 5-floor architecture as the AURELION Kernel.

Use this skill when you need to:
- Map a career advancement plan with gap analysis
- Document professional methodologies and frameworks you've developed
- Think through organizational dynamics and stakeholder relationships
- Build a personal strategy library that persists across sessions
- Make high-stakes career decisions with structured rigor

---

## The Advisor Philosophy

The Advisor is not a life coach and not a resume builder. It is a **strategic thinking partner** that applies rigorous professional frameworks to real career problems.

Core principles:
1. **Evidence over aspiration.** Advancement plans must include proof of current capability, not just future intent.
2. **Stakeholder clarity.** Every career move involves people. Map who matters before deciding what to do.
3. **Methodology as asset.** The frameworks you've built over your career are intellectual property. Document them.
4. **Long game awareness.** Short-term wins that damage long-term positioning are not wins.

---

## Strategic Planning Frameworks

### 1. Career Gap Analysis

Use this when a user wants to advance to a new role or level.

```
Current State (Floor 1):
  - Title, responsibilities, measurable outputs
  - Skills at current proficiency level

Target State (Floor 5):
  - Target title, responsibilities, expected outputs
  - Required skills with proficiency thresholds

Gap:
  - Skill delta: [what needs to improve + by how much]
  - Experience delta: [what proof points are missing]
  - Network delta: [who needs to know your work]
  - Timeline: [realistic based on organization's promotion cycle]

90-Day Sprint Plan:
  - 3 actions that close the most critical gaps
  - One visibility action (stakeholder awareness)
  - One evidence action (documented proof)
```

**Apply when:** User says "I want to be promoted" or "I want to move into [role]."

---

### 2. Stakeholder Map

Use this to organize professional relationships with strategic intent.

```markdown
## Stakeholder: [Name]

**Role:** [Their title and function]
**Relationship to you:** [Direct manager | Skip-level | Peer | External]
**Influence level:** [High | Medium | Low] on [your advancement | your projects]
**Primary concern:** [What are they measured on? What keeps them up at night?]
**Communication style:** [Direct/brief | Narrative | Data-first | Relationship-first]

**What they know about your work:** [Current awareness level]
**What they should know:** [The gap to close]
**Next interaction goal:** [What you want them to think/feel/do after your next touch]

**Relationship health:** [Strong | Neutral | Needs attention]
**Last meaningful interaction:** [Date + context]
```

**Apply when:** User mentions a key person at work they need to manage, influence, or navigate.

---

### 3. Investigation Methodology Template

Use this to document professional methodologies the user has developed.

```markdown
## Methodology: [Name]

**Domain:** [Data QA | Project Management | Vendor Negotiation | etc.]
**Floor:** 2 — Systems
**Author:** [CK / Team]
**Version:** [1.0]

### Problem This Solves
[One paragraph: what breaks when this methodology isn't followed]

### The Framework
**Step 1:** [Action — what to do and why]
**Step 2:** [Action — what to do and why]
...

### Quality Criteria (Definition of Done)
- [ ] [Criterion 1]
- [ ] [Criterion 2]
- [ ] [Criterion 3]

### Common Failure Modes
| Failure | Early Signal | Correction |
|---------|-------------|------------|
| [what goes wrong] | [how to spot it early] | [how to fix it] |

### When NOT to Use This
[Edge cases where this methodology breaks down or needs modification]
```

**Apply when:** User wants to document a process they've developed or refined over time.

---

### 4. Decision Framework — Career Crossroads

Use this when a user is facing a significant career decision (job offer, role change, leave/stay).

```
Situation: [The decision in one sentence]

Criteria (weight each 1–5):
  - Compensation: [weight]
  - Growth trajectory: [weight]
  - Alignment with 5-year goal: [weight]
  - Risk level: [weight]
  - Stakeholder relationships preserved: [weight]

Options:
  [Option A]: Score per criterion → Total weighted score
  [Option B]: Score per criterion → Total weighted score

Gut check:
  "If Option A scores higher but I feel uncomfortable, why?"
  "What am I not factoring in?"

Irreversibility check:
  "Is this a door that closes? Or can I reverse this in 12 months?"

Recommendation: [Option] — [one paragraph rationale]
```

**Apply when:** User says "I don't know if I should..." or "I have a decision to make."

---

## Advisor Session Protocol

When starting a new Advisor session, follow this sequence:

1. **Anchor to Floor 1.** Ask: "What is your current role and how long have you been there?"
2. **Surface the goal (Floor 5).** Ask: "What are you trying to achieve in the next 12 months?"
3. **Identify the friction.** Ask: "What is the thing most in the way of that right now?"
4. **Apply the matching framework.** Gap analysis, stakeholder map, decision framework, or methodology documentation — based on what the friction reveals.
5. **Produce an artifact.** Every Advisor session should end with a document: a plan, a map, a template, a decision record.

Do not let sessions end with only conversation. **A session with no document is a session with no output.**

---

## Integration with Other AURELION Modules

- **AURELION Kernel** — The Advisor builds on top of the Kernel's Floor 1 (Foundation) and Floor 5 (Vision) content. Run `aurelion-kernel-lite` to set the foundation, then apply Advisor frameworks on top of it.
- **AURELION Agent** — Use AGENT protocols during Advisor sessions to ensure the AI challenges your assumptions on career strategy, not just executes them.
- **AURELION Memory** — Store completed Advisor artifacts (career plans, stakeholder maps, decision records) in the Memory system for retrieval across sessions.

Full ecosystem: https://github.com/chase-key/aurelion-hub
