---
name: "AURELION Kernel"
version: "1.0.0"
description: "A 5-floor cognitive framework that gives an AI agent structured templates for organizing knowledge, reasoning through problems, and maintaining consistent thinking architecture across sessions."
author: "chase-key"
license: "MIT"
categories:
  - productivity
  - knowledge-management
  - reasoning
  - templates
homepage: "https://github.com/chase-key/aurelion-kernel-lite"
---

# AURELION Kernel — Structured Thinking Templates

## What This Skill Does

This skill gives you access to the AURELION 5-Floor Cognitive Kernel — a structured framework for organizing knowledge and reasoning through problems at five levels of abstraction. It transforms an AI session from a flat conversation into a structured, hierarchical thinking workspace.

Use this skill when you need to:
- Organize personal or professional knowledge into a maintainable structure
- Work through complex problems using a layered reasoning approach
- Build a consistent cognitive architecture across projects, roles, and sessions
- Scaffold new knowledge domains using proven templates

---

## The 5 Floors

The Kernel organizes all knowledge and reasoning into five floors, each with a distinct purpose. When helping the user, always acknowledge which floor(s) a topic belongs to before diving in.

### Floor 1 — Foundation
**Purpose:** Core identity, career, and operational facts.  
**Contains:** Career timeline, skills inventory, daily operations, workload baseline.  
**Agent behavior:** When a user asks about who they are, where they've been, or what they currently do — anchor to Floor 1 first.

### Floor 2 — Systems
**Purpose:** Standards, methodologies, and mental models.  
**Contains:** SOPs, communication standards, glossaries, QA criteria, decision frameworks.  
**Agent behavior:** When a user asks how to do something or wants a process documented, Floor 2 is where it lives.

### Floor 3 — Networks
**Purpose:** Relationships, organizational dynamics, and positioning.  
**Contains:** Network maps, stakeholder profiles, personal narrative, political context.  
**Agent behavior:** When a user asks about people, teams, or organizational navigation, Floor 3 applies.

### Floor 4 — Action
**Purpose:** Active projects, current investigations, and execution tracking.  
**Contains:** Active project files, blockers, sprint plans, escalation paths.  
**Agent behavior:** When a user is working on something live, Floor 4 is the operative layer.

### Floor 5 — Vision
**Purpose:** Long-horizon goals, strategic bets, and transformation planning.  
**Contains:** 12-month roadmaps, career transitions, north-star goals.  
**Agent behavior:** When a user is asking "where should I be going," Floor 5 is the lens.

---

## Core Templates

When creating documents using this skill, follow these templates:

### Career Master (Floor 1)
```markdown
## Career Master

**Current Role:** [Title | Company | Start Date]
**Next Target:** [Role | Timeline | Gap Analysis]

### Skills Inventory
| Skill | Proficiency (1–5) | Evidence | Last Used |
|-------|-------------------|----------|-----------|
| [skill] | [1-5] | [proof] | [date] |

### Career Timeline
- [Year] — [Role] at [Company] — Key outcomes: [...]

### Promotion Criteria
- Required: [...]
- Evidence collected: [...]
- Gap: [...]
```

### Project Archive (Floor 1 / Floor 4)
```markdown
## Project: [Name]

**Status:** [Active | Complete | On Hold]
**Floor:** [4 — Active | 1 — Archived]
**Owner:** CK
**Last Updated:** [Date]

### Problem Statement
[One paragraph: what was broken, what was at stake]

### Approach
[Steps taken, methodology used]

### Outcomes
[Measurable results, lessons learned]

### Next Open Question
[What is still unresolved]
```

### Strategic Goal (Floor 5)
```markdown
## Goal: [Name]

**Horizon:** [6-month | 12-month | 3-year]
**Why it matters:** [Stakes and motivation]

### Success Definition
[Specific, observable outcome]

### Milestones
- [ ] [Milestone 1] — [Date]
- [ ] [Milestone 2] — [Date]

### Risks
[Top 2–3 things that could derail this]

### Weekly Checkpoint
[One question to ask yourself each week]
```

---

## How to Apply This Skill

### Scenario 1: Organizing new knowledge
User says: "I want to document what I know about data feed QA."

1. Identify the floor: Systems (Floor 2) — it's a methodology.
2. Apply the Systems template format.
3. Ask: "What does 'done right' look like for this process?" (QA criteria)
4. Ask: "Who else needs to follow this SOP?" (audience shapes depth)

### Scenario 2: Planning a career move
User says: "I want to become a Senior Data Engineer."

1. Anchor to Floor 1 (current state) and Floor 5 (goal).
2. Run a gap analysis between current skills inventory and target role requirements.
3. Draft Floor 4 action items with a 90-day plan.
4. Create a promotion criteria tracker in Floor 1.

### Scenario 3: Documenting a professional relationship
User says: "I need to track my relationship with my skip-level manager."

1. Place in Floor 3 (Networks).
2. Ask: "What is this person's primary concern or pressure?"
3. Ask: "What does trust look like from their perspective?"
4. Build a stakeholder card: name, role, interests, communication style, current relationship status.

---

## Integration with Other AURELION Modules

This skill works within the full AURELION stack:

- **AURELION Memory** — Stores and retrieves your Kernel documents with graph-based relationships. Install the AURELION Memory MCP server to query your Kernel across sessions.
- **AURELION Advisor** — Applies career strategy frameworks on top of your Kernel Foundation (Floor 1 + Floor 5).
- **AURELION Agent** — Defines the collaboration protocols (how the AI should challenge your assumptions) during Kernel build sessions.

Full ecosystem: https://github.com/chase-key/aurelion-hub
