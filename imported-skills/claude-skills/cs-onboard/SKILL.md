---
name: "cs-onboard"
description: "Founder onboarding interview that captures company context across 7 dimensions. Invoke with /cs:setup for initial interview or /cs:update for quarterly refresh. Generates ~/.claude/company-context.md used by all C-suite advisor skills. Use when setting up the C-suite advisors for the first time, or when company context is missing or more than 90 days old — e.g. after a fundraise or pivot."
license: MIT
metadata:
  version: 1.0.0
  author: Alireza Rezvani
  category: c-level
  domain: orchestration
  updated: 2026-03-05
  frameworks: founder-interview, context-capture, quarterly-refresh
---

# C-Suite Onboarding

Structured founder interview that builds the company context file powering every C-suite advisor. One 45-minute conversation. Persistent context across all roles.

## Commands

- `/cs:setup` — Full onboarding interview (~45 min, 7 dimensions)
- `/cs:update` — Quarterly refresh (~15 min, "what changed?")

## Keywords
cs:setup, cs:update, company context, founder interview, onboarding, company profile, c-suite setup, advisor setup

---

## Conversation Principles

Be a conversation, not an interrogation. Ask one question at a time. Follow threads. Reflect back: "So the real issue sounds like X — is that right?" Watch for what they skip — that's where the real story lives. Never read a list of questions.

Open with: *"Tell me about the company in your own words — what are you building and why does it matter?"*

---

## 7 Interview Dimensions

### 1. Company Identity
Capture: what they do, who it's for, the real founding "why," one-sentence pitch, non-negotiable values.
Key probe: *"What's a value you'd fire someone over violating?"*
Red flag: Values that sound like marketing copy.

### 2. Stage & Scale
Capture: headcount (FT vs contractors), revenue range, runway, stage (pre-PMF / scaling / optimizing), what broke in last 90 days.
Key probe: *"If you had to label your stage — still finding PMF, scaling what works, or optimizing?"*

### 3. Founder Profile
Capture: self-identified superpower, acknowledged blind spots, archetype (product/sales/technical/operator), what actually keeps them up at night.
Key probe: *"What would your co-founder say you should stop doing?"*
Red flag: No blind spots, or weakness framed as a strength.

### 4. Team & Culture
Capture: team in 3 words, last real conflict and resolution, which values are real vs aspirational, strongest and weakest leader.
Key probe: *"Which of your stated values is most real? Which is a poster on the wall?"*
Red flag: "We have no conflict."

### 5. Market & Competition
Capture: who's winning and why (honest version), real unfair advantage, the one competitive move that could hurt them.
Key probe: *"What's your real unfair advantage — not the investor version?"*
Red flag: "We have no real competition."

### 6. Current Challenges
Capture: priority stack-rank across product/growth/people/money/operations, the decision they've been avoiding, the "one extra day" answer.
Key probe: *"What's the decision you've been putting off for weeks?"*
Note: The "extra day" answer reveals true priorities.

### 7. Goals & Ambition
Capture: 12-month target (specific), 36-month target (directional), exit vs build-forever orientation, personal success definition.
Key probe: *"What does success look like for you personally — separate from the company?"*

---

## Output: company-context.md

After the interview, generate `~/.claude/company-context.md` using `templates/company-context-template.md`.

Fill every section. Write `[not captured]` for unknowns — never leave blank. Add timestamp, mark as `fresh`.

Tell the founder: *"I've captured everything in your company context. Every advisor will use this to give specific, relevant advice. Run /cs:update in 90 days to keep it current."*

---

## /cs:update — Quarterly Refresh

**Trigger:** Every 90 days or after a major change. Duration: ~15 minutes.

Open with: *"It's been [X time] since we did your company context. What's changed?"*

Walk each dimension with one "what changed?" question:
1. Identity: same mission or shifted?
2. Scale: team, revenue, runway now?
3. Founder: role or what's stretching you?
4. Team: any leadership changes?
5. Market: any competitive surprises?
6. Challenges: #1 problem now vs 90 days ago?
7. Goals: still on track for 12-month target?

Update the context file, refresh timestamp, reset to `fresh`.

---

## Context File Location

`~/.claude/company-context.md` — single source of truth for all C-suite skills. Do not move it. Do not create duplicates.

## References
- `templates/company-context-template.md` — blank template for output
- `references/interview-guide.md` — deep interview craft: probes, red flags, handling reluctant founders
