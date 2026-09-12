---
name: game-design
description: Game design skill using the MDA (Mechanics, Dynamics, Aesthetics) framework with supporting concepts for indie developers. Use when designing new games from scratch, analyzing existing games, iterating on game designs, creating Game Design Documents (GDDs), writing analysis reports, or brainstorming game concepts. Triggers on requests involving game mechanics, player experience, game balance, fun factors, or game development planning.
---

# Game Design

A framework-driven approach to game design for indie developers, centered on MDA (Mechanics, Dynamics, Aesthetics) with supporting concepts: Bartle player types, game loops, and flow theory.

## Workflow Decision Tree

**What does the user need?**

- **"I want to make a game about X"** → Design from Scratch workflow
- **"Analyze/break down this game"** → Analysis workflow
- **"My game has a problem with Y"** → Iteration workflow
- **"Quick ideas for X"** → Rapid Ideation (skip to Quick Concepts section)

## Design from Scratch

Use when creating a new game concept.

**Steps:**

1. **Start with Aesthetics** — What emotions should players feel?
   - See [MDA.md](references/MDA.md) for the 8 aesthetic categories
   - Pick 1-2 primary aesthetics (focus is key for indie scope)

2. **Identify target players** — Who will feel these emotions?
   - See [CONCEPTS.md](references/CONCEPTS.md) for Bartle player types
   - Match aesthetics to player motivations

3. **Design core loop** — What repeated action delivers the aesthetic?
   - See [CONCEPTS.md](references/CONCEPTS.md) for loop patterns
   - Keep indie-scope: one tight loop beats three loose ones

4. **Define mechanics** — What rules enable the dynamics?
   - Work backward from desired player behavior
   - Test: "If players do X, will they feel Y?"

5. **Check flow** — Is the challenge curve right?
   - See [CONCEPTS.md](references/CONCEPTS.md) for flow theory
   - Plan difficulty progression

**Output:** Produce a GDD using the template in [GDD_TEMPLATE.md](references/GDD_TEMPLATE.md)

## Analysis Workflow

Use when breaking down an existing game.

**Steps:**

1. **Identify Mechanics** — List all rules, systems, components
   - What can players do?
   - What happens automatically?
   - What are the win/lose conditions?

2. **Observe Dynamics** — What behaviors emerge?
   - How do mechanics interact?
   - What strategies develop?
   - What's the core loop in practice?

3. **Extract Aesthetics** — What emotions result?
   - Map observed dynamics to aesthetic categories
   - Identify primary vs secondary aesthetics

4. **Evaluate fit** — Does MDA alignment work?
   - Do mechanics actually produce intended aesthetics?
   - Where are the gaps or unintended effects?

**Output:** Produce an analysis report with: Overview → Mechanics breakdown → Dynamics observed → Aesthetics delivered → Alignment assessment → Lessons for designers

## Iteration Workflow

Use when improving an existing design.

**Steps:**

1. **Diagnose the layer** — Where is the problem?
   - Players not having fun → Aesthetics mismatch
   - Unexpected behaviors → Dynamics issue
   - Confusion or frustration → Mechanics problem

2. **Trace the chain** — Follow MDA causality
   - Aesthetics problems ← caused by Dynamics
   - Dynamics problems ← caused by Mechanics
   - Fix at the mechanics level to change everything above

3. **Propose changes** — Minimal effective intervention
   - What's the smallest mechanic change that shifts dynamics?
   - Preserve what's working

4. **Predict effects** — Walk through the chain
   - New mechanic → expected new dynamics → predicted aesthetics
   - Check for unintended consequences

**Output:** Iteration report with: Problem diagnosis → Root cause (which layer) → Proposed changes → Predicted effects → Testing recommendations

## Quick Concepts

For rapid ideation, use this lightweight format:

\`\`\`
CONCEPT: [One-line pitch]
CORE AESTHETIC: [Primary emotion]
CORE LOOP: [Action → Feedback → Reward]
KEY MECHANIC: [The unique rule that makes it work]
TARGET PLAYER: [Bartle type or motivation]
\`\`\`

## Output Formats

**Game Design Document** — Full specification for development
- Use [GDD_TEMPLATE.md](references/GDD_TEMPLATE.md)
- Appropriate for: serious projects, team communication

**Analysis Report** — Breakdown of existing game
- Structured prose with MDA sections
- Appropriate for: learning, competitive analysis, post-mortems

**Iteration Report** — Focused improvement plan
- Problem → diagnosis → solution → predictions
- Appropriate for: playtesting feedback, design pivots

**Quick Concept** — Lightweight ideation
- 5-line format above
- Appropriate for: brainstorming, game jams, exploration

## References

Detailed framework documentation:
- [references/MDA.md](references/MDA.md) — Full MDA framework with aesthetic categories
- [references/CONCEPTS.md](references/CONCEPTS.md) — Bartle types, game loops, flow theory
- [references/GDD_TEMPLATE.md](references/GDD_TEMPLATE.md) — Game Design Document template
