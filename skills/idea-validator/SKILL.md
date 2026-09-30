---
name: idea-validator
description: >
  Run a structured, multi-phase idea validation flow for app or business ideas BEFORE
  building anything. Use this skill whenever the user mentions: validating an idea,
  checking if an idea is worth building, pre-build validation, idea stress-test,
  market research for a product, should I build X, is X a good idea, checking PMF
  (product-market fit), or any variation of "I have an idea for [X]". Also trigger
  when the user describes a product concept and wants feedback, competitive analysis,
  or a go/no-go recommendation. This skill produces a structured Idea Validation Report
  as a markdown file covering all five phases: problem clarity, market & competition,
  prototype feasibility, technical risk, and a go/no-go decision memo.
license: Apache-2.0
compatibility: Requires internet access for Phase 2 web research.
metadata:
  author: shadkhan
  version: "1.0.0"
---

# Idea Validator Skill

Produces a thorough **Idea Validation Report** before any code is written.
The goal: kill bad ideas in hours, not weeks.

## Overview of Phases

| Phase | Name | Key Output |
|-------|------|-----------|
| 1 | Problem & User Clarity | Kill/refine decision on the problem itself |
| 2 | Market & Competition | Competitor matrix + gap analysis |
| 3 | Prototype & UX Feasibility | Fake-door / MVP scope |
| 4 | Technical Risk Assessment | Spike targets + architecture risks |
| 5 | Go / No-Go Decision Memo | Confidence score + top assumption to validate |

---

## Step 0 — Gather Context

Before running phases, extract or ask for:

1. **The idea** — one sentence description
2. **Target user** — who specifically (persona, not demographics)
3. **Core problem being solved** — what pain, how acute?
4. **Tech stack in mind** (if any)
5. **Time/resource budget** the builder has
6. **Existing traction** (any users, feedback, revenue?)

If the user has described the idea in the conversation already, extract these from context. Ask only for what's missing — max 2 clarifying questions.

---

## Phase 1 — Problem & User Clarity

Read: `references/phase1-problem.md`

Run the devil's advocate analysis, fake review generation, and persona grid.

Output: a `## Phase 1` section in the report with:
- Problem statement (sharpened)
- 3 reasons the idea could fail
- 2 user personas (would pay vs. wouldn't pay)
- One fake 1-star review surfacing the sharpest edge case

---

## Phase 2 — Market & Competition

Read: `references/phase2-market.md`

Use web search to find real competitors. Build a competitor matrix.

Output: `## Phase 2` section with:
- Competitor matrix (name, pricing, key feature, weakness)
- Gap analysis — where does the idea uniquely fit?
- Market signal assessment (is anyone paying for adjacent solutions?)
- Red flags if the market is too crowded or too thin

---

## Phase 3 — Prototype Feasibility

Read: `references/phase3-prototype.md`

Assess what can be faked/prototyped without real backend.
Define the minimum fake-door test.

Output: `## Phase 3` section with:
- What can be prototyped with Claude Artifacts or a static page
- What the fake-door CTA should be
- What question the prototype answers (UX/demand/pricing)
- Estimate: 1-day prototype scope

---

## Phase 4 — Technical Risk Assessment

Read: `references/phase4-tech.md`

Identify the hardest technical problem. Recommend spike targets.

Output: `## Phase 4` section with:
- Top 3 technical risks ranked by severity
- Recommended spike: "build this one thing first before anything else"
- Third-party dependency risks (APIs, scrapers, infra)
- Scale risk flags (what breaks at 10k / 100k users)

---

## Phase 5 — Go / No-Go Decision Memo

Read: `references/phase5-decision.md`

Synthesize all phases into a ruthless investor-style verdict.

Output: `## Phase 5` section with:
- **Verdict**: GO / CONDITIONAL GO / NO-GO
- **Confidence score**: X/10
- **Single biggest unvalidated assumption**
- **If GO**: the one thing to build first
- **If CONDITIONAL GO**: the condition that must be true before building
- **If NO-GO**: the fundamental flaw and a pivot suggestion

---

## Output Format

Save the full report as:
```
idea-validation-report-[slug].md
```

The report must be structured with these top-level sections:
```markdown
# Idea Validation Report: [Idea Name]
**Date:** [date]
**Validator:** Claude Idea Validator Skill

## Executive Summary
[3 sentences max — problem, verdict, biggest risk]

## Phase 1 — Problem & User Clarity
...

## Phase 2 — Market & Competition
...

## Phase 3 — Prototype Feasibility
...

## Phase 4 — Technical Risk Assessment
...

## Phase 5 — Go / No-Go Decision Memo
...

## Appendix — Validation Checklist
[checklist of what's been validated vs. still open]
```

Present the file to the user when complete.

---

## Tone & Style Rules

- Be **ruthlessly honest** — this is pre-build, not a pitch deck review
- Use **specific language** — no vague hedges like "it depends"
- When you don't know something (e.g., real competitor pricing), **use web search**
- Flag when an assumption is **critical and still unvalidated** — don't paper over it
- Keep each phase focused — the user is a developer, not a business analyst

---

## Example Trigger Phrases

- "I want to build an AI tool that does X — is it worth it?"
- "Validate my idea: [description]"
- "Should I build X before I start coding?"
- "Help me stress-test this idea"
- "Run an idea validation on [concept]"
- "I'm thinking of building [X] — what do you think?"
