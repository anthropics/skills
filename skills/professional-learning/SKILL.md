---
name: professional-learning
description: >
  Design professional development sessions, workshop agendas, PLC (professional learning community)
  protocols, coaching cycles, and adult learning experiences for educators and organizational staff.
  Use this skill whenever a user asks to plan, build, design, or facilitate any form of professional
  learning — including PD days, staff training, team meetings with a learning goal, instructional
  coaching cycles, onboarding programs, or capacity-building workshops. Trigger even when the user
  says things like "help me plan a PD session," "build a PLC agenda," "design a coaching cycle,"
  "create a staff training," "facilitate a team learning experience," or "help me run a workshop."
  Serves K-12 teachers and coaches, school/district administrators, higher education faculty,
  nonprofit/NGO staff, and corporate L&D teams.
---

# Professional Learning Skill

## Purpose
Generate rigorous, equity-centered, outcomes-driven professional learning artifacts grounded in
adult learning science. All outputs are **Structured Markdown** by default (headers, tables,
timelines). Offer DOCX conversion via the `docx` skill when the user requests a downloadable file.

---

## Output Types

| Output Type | Trigger Phrases |
|---|---|
| **Workshop Agenda & Facilitation Guide** | "agenda," "workshop," "PD session," "facilitation plan" |
| **PLC Meeting Protocol & Norms** | "PLC," "team meeting," "collaborative inquiry," "professional learning community" |
| **Coaching Cycle Framework** | "coaching cycle," "observation," "debrief," "coaching plan," "instructional coaching" |
| **Full PD Session Design** | "full session," "PD design," "training plan," "objectives + materials" |
| **Adult Learning Experience Plan** | "onboarding," "staff training," "org development," "capacity building," "L&D" |

---

## Mandatory Embedded Frameworks

Always apply **all five** frameworks. They are not optional add-ons.

### 1. Andragogy (Knowles)
Every design must honor the six assumptions of adult learners:
- Self-concept: treat participants as autonomous learners
- Experience: surface and build on prior knowledge
- Readiness: connect content to immediate professional needs
- Orientation: problem-centered, not subject-centered
- Motivation: intrinsic over extrinsic
- Need to know: state the "why" before the "what"

### 2. Backward Design (ADDIE-aligned)
Build in this sequence — never skip steps:
1. **Outcomes first** → What should participants *know, do, believe* after?
2. **Evidence** → How will you measure transfer? (feeds Kirkpatrick)
3. **Learning experiences** → Activities, protocols, materials
4. **Facilitation plan** → Timing, transitions, facilitation moves
5. **Evaluation** → Always embed (see Kirkpatrick section)

### 3. Kirkpatrick Levels 1–4 (always embed L1–L2 minimum)

| Level | Focus | Artifact to Include |
|---|---|---|
| L1 Reaction | Did participants find it valuable? | Exit ticket, pulse check, satisfaction survey |
| L2 Learning | Did they acquire knowledge/skill? | Pre/post prompt, performance task, reflection rubric |
| L3 Behavior | Did they apply it on the job? | 30-day follow-up protocol, classroom walkthrough tool |
| L4 Results | Did it impact outcomes? | Data collection plan, metric linkage |

> **Default rule**: Always embed L1 + L2 artifacts in every output. Include L3 when session length ≥ half-day or multi-session. Include L4 only when explicitly requested or when the user mentions program evaluation/impact.

### 4. Cognitive Coaching / GROWTH Model
Use this structure for all coaching cycle outputs:

| Phase | GROWTH Anchor | Key Questions |
|---|---|---|
| Pre-observation | **G**oal + **R**eality | What are you hoping participants/students will do? What's currently happening? |
| Observation | **O**ptions | What evidence are you collecting? |
| Debrief | **W**ay forward | What patterns did you notice? What would you keep/change? |
| Follow-up | **T**imeline + **H**abits | What's the next step? By when? What support do you need? |

### 5. UDL & Equity-Centered Facilitation
Every output must include at least **one explicit UDL annotation** per activity:
- Representation: How is content accessible (visual, text, audio)?
- Action/Expression: How can participants engage/respond flexibly?
- Engagement: What sustains motivation across diverse participants?

Additionally flag:
- Power dynamics in facilitation (who speaks, who decides)
- Language access (multilingual participants, jargon reduction)
- Psychological safety protocols (norms, anonymous response options)

---

## Session Length Inference Rules

When duration is not specified, infer from context:

| Context Clue | Inferred Duration |
|---|---|
| "Quick meeting," "check-in," "team huddle" | 30–45 min |
| "PLC meeting," "team PD," single topic | 60–90 min |
| "Workshop," "PD session," "training" | 2–3 hours |
| "PD day," "full-day," "retreat" | 6–7 hours |
| "Series," "cycle," "program" | Multi-session (note sessions + total hours) |

Always state the inferred duration at the top of the output with a note: *"Duration inferred as [X] — adjust if needed."*

---

## Output Structure Templates

### Template A: Workshop Agenda & Facilitation Guide

```
## [Title]
**Audience**: [role/level]  **Duration**: [X min/hrs]  **Facilitator**: [name/role]
**Learning Objectives** (Bloom's action verbs):
  - Participants will [verb] [content] in order to [purpose].

---
### Agenda

| Time | Segment | Activity | Materials | Facilitation Notes | UDL Note |
|------|---------|----------|-----------|-------------------|----------|

---
### Evaluation Artifacts
- **L1 Exit Ticket**: [prompt]
- **L2 Performance Indicator**: [task or reflection rubric]
```

### Template B: PLC Meeting Protocol

```
## PLC Meeting — [Date/Cycle]
**Team**: [grade/dept/school]  **Duration**: [X min]  **Facilitator**: [name]
**Inquiry Question**: [student-centered question driving this cycle]
**Norms**: [list or link]

---
### Protocol Sequence

| Time | Phase | Purpose | Facilitation Move |
|------|-------|---------|------------------|

---
### Data Examined: [source + artifact]
### Decisions Made: [action items + owner + deadline]
### L1 Check: [team pulse — 1-word whip-around or thumb vote]
```

### Template C: Coaching Cycle Framework

```
## Coaching Cycle — [Coachee Name/Role]
**Coach**: [name]  **Cycle Goal**: [SMART goal]  **Timeline**: [start → end]

---
### GROWTH Cycle Log

| Date | Phase | Key Questions Used | Evidence Collected | Next Step |
|------|-------|-------------------|-------------------|-----------|

---
### L2 Indicator: [observable behavior shift to track]
### L3 Follow-up: [30-day check-in protocol]
```

### Template D: Full PD Session Design

```
## PD Session Design Document
**Title** | **Audience** | **Duration** | **Designer** | **Date**

### Part 1: Outcomes & Alignment
| Objective | Bloom's Level | Kirkpatrick Level | Standard/Competency Aligned |

### Part 2: Learning Arc
[Opening hook → Activate prior knowledge → New learning → Application → Transfer → Closure]

### Part 3: Materials & Resources
[List with access/equity notes]

### Part 4: Facilitation Guide
[Full timed agenda — see Template A format]

### Part 5: Evaluation Suite
- L1 Reaction instrument
- L2 Learning artifact
- L3 Transfer protocol (if ≥ half-day)
```

### Template E: Adult Learning Experience Plan (Onboarding / Org Training)

```
## Adult Learning Experience Plan
**Program**: [name]  **Audience**: [role]  **Duration**: [hours/days/weeks]
**Organizational Goal Linkage**: [strategic priority or KPI]

### Learning Pathway

| Module | Duration | Mode | Outcome | Kirkpatrick Level Targeted |
|--------|---------|------|---------|---------------------------|

### Andragogy Alignment Check
[One row per Knowles assumption — confirm each is addressed]

### Evaluation Plan
| Kirkpatrick Level | Instrument | Timing | Owner |
```

---

## Facilitation Language Bank
Reference when writing facilitation notes:

- **Activating prior knowledge**: "Turn and talk: What do you already know about…?"
- **Cognitive conflict**: "Look at this data. What surprises you?"
- **Sense-making**: "What patterns are you noticing across these examples?"
- **Transfer**: "How would you apply this in your context next week?"
- **Psychological safety**: "Take 60 seconds to write before we share aloud."
- **Equity check**: "Who hasn't spoken yet? Let's hear from a different voice."

---

## Out of Scope
This skill does **not** produce:
- Student-facing lesson plans or K-12 curriculum units (→ use `instructional-design` skill)
- HR performance reviews or disciplinary documentation
- Grant proposals or logic models (→ use `grant-writing` skill)
- Program evaluation reports (→ use `program-evaluation` skill)

If a request overlaps with these, note the boundary and offer to hand off to the appropriate skill.

---

## Quick-Start Decision Tree

```
User request received
        │
        ├─ Mentions "coaching," "observation," "debrief" ──→ Template C
        ├─ Mentions "PLC," "team protocol," "inquiry" ────→ Template B
        ├─ Mentions "agenda," "workshop," "facilitate" ───→ Template A
        ├─ Mentions "onboarding," "training program" ─────→ Template E
        └─ Mentions "design," "full session," "materials" → Template D
```

When in doubt between A and D: **A** if the user wants a single session run document; **D** if they want a complete design package with materials and evaluation suite.

---

## Reference Files
- `references/frameworks.md` — Extended framework citations (Knowles, Kirkpatrick, UDL guidelines, GROWTH model source literature)
- `references/evaluation-instruments.md` — Ready-to-use L1–L3 instruments, rubrics, and survey stems
