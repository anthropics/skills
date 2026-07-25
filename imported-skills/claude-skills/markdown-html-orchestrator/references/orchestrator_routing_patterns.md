# Orchestrator Routing Patterns

**Why this exists:** The two-signal routing discipline (silent-route only above a confidence threshold; otherwise ask one question with a recommended answer) is not original to this plugin. It's been established in the research-ops, commercial, and business-operations domains. This document records the canon so the orchestrator never silently chains or guesses below threshold.

## The pattern

Three discrete behaviors based on the classifier's score:

1. **Silent route** — winner ≥ 3 points AND (runner-up = 0 OR winner ≥ 2× runner-up). Hand off to the sub-skill without asking.
2. **Clarify** — winner ≥ 2 points but ratio against runner-up is too close. Ask ONE question, recommend the winner, take the user's confirmation or override.
3. **Ambiguous** — no signals matched. Ask which lane, default to md-document if the user shrugs.

Filename hint counts double (2 points each) because filename is high-signal user intent — a file named `pr-review.md` is almost certainly a code review.

## Sources

### 1. research-ops/skills/research-ops-skills/SKILL.md §"Routing logic (deterministic)"
The two-signal threshold pattern formalized: "Same two-signal threshold pattern as `commercial-skills`. Single-signal → clarifying question. Mixed signals → highest-confidence first, chain second in a follow-up turn. Never silently chain."

### 2. commercial/skills/commercial-skills/SKILL.md
First domain to ship the explicit "never silently chain" rule, with named signal classes (PRICING / DEAL / PARTNERSHIPS / RFP / FORECAST). The discipline is independent of subject matter — same shape for research, for commercial deals, for markdown docs.

### 3. business-operations/skills/business-operations-skills/SKILL.md
The "explore the workspace first" pattern: filenames like `vendor-list.csv` or `sla-tracker.xlsx` resolve the lane without asking. Filename hint = 2 points is calibrated here.

### 4. Matt Pocock — *grill-with-docs* (engineering/grill-with-docs/SKILL.md, MIT)
Five rules formalized:
1. One question per turn — never bundle.
2. Always recommend an answer with citation-backed rationale.
3. Explore before asking.
4. Walk the decision tree depth-first.
5. Track dependencies (don't ask Q3 before Q1's answer determines whether Q3 applies).

### 5. Anthropic — `context: fork` (SKILL.md frontmatter)
The mechanism that makes orchestrator routing efficient: forked sub-skills run in isolated context, so the parent thread doesn't bloat with the full markdown body, the diff hunks, or the slide bodies. Documented in research-ops, commercial, and business-operations orchestrators.

### 6. The "never silently chain" hard rule
Originates from research-ops Sprint 1 design (`documentation/implementation/research-ops-expansion-plan.md`). The rule prevents the worst orchestrator failure mode: routing to two sub-skills in sequence without explicit user acknowledgment of the chain. Markdown-html applies it: "convert this markdown to HTML and also make slides from it" is two operations, asked explicitly.

### 7. NN/g — *Defaults Are the Best Friend of UX* (Jakob Nielsen, 2007)
Recommended answers in clarifying questions reduce decision fatigue. The orchestrator never asks an open question — every clarification ships with "Recommended: <answer>, because <rationale>" so the user can just say "yes."

## Applied to markdown-html

The classifier produces a `total_scores` dict. The orchestrator's decision tree:

```
if below_min_lines:                          → REFUSE (Shihipar 100-line rule)
elif not setup_completed_at:                 → REFUSE (point at onboarding)
elif winner_score == 0:                      → ASK_USER (lane + recommend md-document)
elif silent_route_allowed:                   → ROUTE_SILENTLY to md-<winner>
elif winner_score >= 2:                      → ASK_USER (recommend md-<winner>)
else:                                        → ASK_USER (treat as md-document by default)
```

Never two routes in one turn. Never "I'll just do both."
