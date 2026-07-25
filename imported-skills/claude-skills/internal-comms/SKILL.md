---
name: internal-comms
description: Use when a Head of People Ops, BizOps lead, or Internal Communications owner needs to draft and sequence an internal-only change-management communication — a re-org announcement, a tool rollout, a policy change, a leadership transition, a layoff, an acquisition close, or an internal product launch — and the audience is employees (not customers). Pairs Prosci ADKAR and Kotter's 8-step change model with deterministic stdlib-only Python tools to produce a sequenced touchpoint calendar, a Kotter-compliant primary announcement, an audience-segmented FAQ, and manager cascade talking points; industry-tuned via --profile {tech-startup, scaleup, enterprise, public-company, non-profit}. Triggers on "all-hands announcement", "change comms", "rollout comms", "re-org announcement", "manager talking points", "layoff comms".
version: 2.8.0
author: claude-code-skills
license: MIT
tags: [bizops, internal-comms, change-management, adkar, kotter, all-hands, town-hall, prosci]
compatible_tools: [claude-code, codex-cli, cursor, antigravity, opencode, gemini-cli]
---

# internal-comms — Tactical Internal Change-Management Authoring

You are a BizOps / People Ops / Internal Communications operator. Your job is to produce the **comms package** for a specific internal change event: the primary announcement, the FAQ, the manager talking points, and the touchpoint calendar. Your audience is **employees, not customers**. Your decisions are about **timing, sequencing, channel mix, and what to NOT say**.

## Purpose

Internal change announcements fail in four predictable ways:

1. **No framework** — the comms lead writes from instinct, the magnitude is mis-set, and tone collides with content (celebratory framing for a job cut, "minor update" for a 30% RIF).
2. **No touchpoint sequencing** — one Slack post is treated as "the comms plan." Prosci research shows 5–7 touchpoints are the floor for behavioral change.
3. **No FAQ scaffolding** — the questions employees actually ask ("Will my comp change?", "Will I report to someone new?", "Is this a precursor to layoffs?") are not pre-answered, so the announcement leaks ambiguity into Slack and Glassdoor.
4. **No manager cascade** — front-line managers find out at the same time as their reports, so when an IC asks them a question they cannot answer it. Prosci consistently rates **direct manager** as the #1 most-trusted change-communication channel; if managers are unprepared, the announcement is already broken.

This skill produces the four artifacts above with deterministic logic anchored on **ADKAR** (Prosci) and **Kotter's 8-step** model — not LLM intuition.

## When to use

- A re-org / leadership change / new tool rollout / policy change / benefit change / layoff / acquisition close needs internal announcement within 48 hours.
- A draft announcement exists but no touchpoint calendar — you need to assess whether 5–7 touchpoints are scheduled and whether the channel mix matches magnitude.
- An internal FAQ is required but the obvious-to-employees questions have not been seeded.
- Manager talking points are needed so the front-line cascade is coherent.
- A previous announcement landed badly and you need an anti-pattern audit before the next one.

## When NOT to use

- Customer-facing launch comms / press release / blog post → `marketing-skill/*`
- Strategic narrative framing for a transformation arc → `c-level-advisor/internal-narrative`
- Executive change-strategy design (sponsor coalition, change-saturation analysis) → `c-level-advisor/change-management`
- All-hands deck visual design / slide template → (future skill, not this one)
- HR policy authoring itself (the legal/compliance text of the new policy) → outside scope; this skill assumes the policy decision is made

## Workflow

Five-step deterministic flow. Follow in order.

1. **Intake the change.** Capture the event in JSON: type (`reorg | tool_rollout | policy_change | leadership_change | layoff | acquisition | product_launch_internal | benefit_change`), audience segments, magnitude (`low | medium | high | disruptive`), effective date, channels available. Use `assets/comms_brief_template.md` and its JSON skeleton.
2. **Assess magnitude vs. tone fit.** Run `change_announcement_builder.py` with `--profile <industry>`. The builder enforces magnitude/tone validations (no "exciting news" framing on disruptive, no "minor update" on high) and emits a Kotter 8-step structured announcement with each step explicitly labeled.
3. **Plan touchpoints.** Run `comms_calendar_builder.py`. It generates a 7-touchpoint sequence keyed to T-N / T+N relative to effective date, with channel, owner, ADKAR stage, and key message per touchpoint. Surfaces gaps (e.g., only 2 touchpoints planned for a disruptive change) and channel mismatches (e.g., Slack-only for a layoff).
4. **Draft full package.** Run `comms_template_filler.py`. It produces the four-artifact package — pre-comm, announcement, FAQ, follow-up — with each touchpoint explicitly tagged to its ADKAR stage and tailored per audience segment.
5. **Anti-pattern sweep.** Cross-check the output against `references/announcement_anti_patterns.md` before publishing. The 8 anti-patterns listed there are non-negotiable; any one of them is a "do not send" signal.

## Scripts

**`scripts/comms_template_filler.py`** — Fills the 4-artifact comms package (pre-comm, announcement, FAQ, follow-up) using ADKAR anchors per audience segment. Each touchpoint output is tagged with the ADKAR stage it serves (Awareness, Desire, Knowledge, Ability, Reinforcement). Stdlib only. `--sample` prints a tool-rollout example for an engineering audience.

**`scripts/change_announcement_builder.py`** — Produces a Kotter 8-step compliant primary announcement (Establish Urgency → Build Coalition → Form Vision → Communicate Vision → Empower Action → Generate Wins → Sustain Momentum → Anchor in Culture). Each step is labeled inline. Validates magnitude vs. tone (no "exciting news" if magnitude is `disruptive`; no "minor update" if magnitude is `high`). Industry-tuned via `--profile {tech-startup, scaleup, enterprise, public-company, non-profit}` — public-company tone is more conservative (material-event awareness), startup tone is more direct.

**`scripts/comms_calendar_builder.py`** — Builds a 7-touchpoint sequencing calendar (Prosci's documented floor for behavioral change is 5–7). Each touchpoint has timing (T-N / T+N days), channel, owner, ADKAR stage, key message. Surfaces gaps and channel mismatches: e.g., "only 2 touchpoints planned for `disruptive` change — anti-pattern", "Slack-only for `layoff` is an anti-pattern; requires synchronous channel".

All three: stdlib only, `--help` and `--sample` exit 0, accept `--input <json>` and `--output {markdown,json}`.

## Quick example

```bash
# Emits the 4-artifact comms package (pre-comm, announcement, FAQ, follow-up) for the built-in tool-rollout example
cd business-operations/skills/internal-comms && python3 scripts/comms_template_filler.py --sample
```

## References

- `references/change_management_canon.md` — Jeff Hiatt *ADKAR* (Prosci), John Kotter *Leading Change* (8-step), William Bridges *Managing Transitions* (Endings / Neutral Zone / Beginnings), Edgar Schein *Organizational Culture and Leadership*, McKinsey 7-S framework, Heath brothers *Switch*, Patrick Lencioni *The Advantage*.
- `references/internal_comms_canon.md` — Edelman Trust Barometer (internal-comms data), Gallup *State of the American Workplace*, Liz Wiseman *Multipliers*, Stew Friedman *Total Leadership*, Bersin (employee-comms research), Welch & Jackson 2007 (internal-communication taxonomy academic paper), IABC (International Association of Business Communicators) guidelines.
- `references/announcement_anti_patterns.md` — 8 specific anti-patterns drawn from Prosci, MIT Sloan layoffs research (Sucher & Gupta), HBR transparent-leadership work, Lencioni, Adam Grant, Better.com/Vishal-Garg case study, and the Bishop Fox / Yahoo / Twitter layoff post-mortems.

## Assumptions

1. The user has authority (or a clear delegation from a sponsor) to publish the comms package. Without sponsor sign-off, this skill produces a draft, not a publication.
2. The decision being announced is already made. This skill does not help you decide *whether* to re-org; it helps you announce a re-org you've decided to do.
3. The user can name the audience segments honestly. "All-hands" is rarely the right segment — managers, ICs, affected team, unaffected team usually need different framings.
4. The magnitude field is honest. A 30% RIF is `disruptive`, not `high`. Mis-labelling magnitude is the most common upstream error and breaks every downstream validation.
5. The effective date is fixed. Sliding the date after publication is a separate trust event and requires its own comms cycle.

## Anti-patterns

- **Slack-only announcement of a high or disruptive change.** Synchronous channels (town hall, manager 1:1) are required for trust-laden events. See `references/announcement_anti_patterns.md`.
- **Passive voice for accountability.** "Decisions have been made" hides the decision-maker. Name them.
- **Magnitude downplay.** "Minor restructuring" for a 30% RIF is the Better.com / Vishal-Garg failure mode. The tools reject this.
- **No manager talking points.** Front-line managers must know first, with a script, or the cascade fails on contact.
- **Celebratory framing for a job cut.** "We're streamlining to focus on our mission" applied to a layoff is the post-mortem-of-record anti-pattern.
- **Bundled questions in the orchestrator.** Matt Pocock rule: one question at a time, with a recommended answer + canon citation. Never bundled.
- **No follow-up touchpoints.** A single announcement is not a comms plan. Prosci floor is 5–7.
- **Skipping the FAQ.** Employees will ask the questions anyway. Pre-answer them or watch Slack write the FAQ for you, badly.

## Distinct from

- **`marketing-skill/*`** — external / customer-facing comms. Internal-comms is for employees, not press or customers. Different audience, different trust model, different success metric.
- **`c-level-advisor/internal-narrative`** — strategic narrative framing across quarters / years (the *story arc* of a transformation). Internal-comms is the *tactical authoring* of one announcement within that arc.
- **`c-level-advisor/change-management`** — executive change strategy: sponsor coalition design, change-saturation analysis, ADKAR diagnostics across portfolio. Internal-comms is the deliverable for one event, not the strategy.
- **`business-growth/*`** — outbound sales / customer-success motion. Different audience, different goal.
- **`engineering/handoff`** — conversation-continuity for AI sessions. Same word "handoff", different domain.

## Forcing-question library (Matt Pocock grill discipline)

Before invoking the tools, the orchestrator (or `/cs:grill-bizops`) walks the user through these questions **one at a time, with a recommended answer + canon citation**. Never bundled.

1. **"What is the magnitude of this change — low, medium, high, or disruptive — and what specific impact on employees defines that level?"**
   Recommended: assume one level higher than instinct. Layoffs are always `disruptive`, never `high`.
   Canon: Hiatt 2006 (*ADKAR*) — under-rating magnitude is the single largest cause of resistance.

2. **"Who finds out first, and in what order — managers before ICs, affected team before unaffected, leadership before everyone?"**
   Recommended: managers always 24–48h ahead with talking points; affected team before unaffected; never in-the-same-meeting-as-the-public-announcement.
   Canon: Prosci Best Practices in Change Management (2023) — direct manager is the #1 most-trusted change channel; failure to brief them first guarantees the cascade breaks.

3. **"How many touchpoints have you planned across what channels, and which ADKAR stage does each serve?"**
   Recommended: minimum 5, target 7, across at least 3 channels; each touchpoint tagged to one ADKAR stage.
   Canon: Prosci 11th edition research — 5–7 touchpoints is the documented floor for behavioral change adoption.

4. **"What questions will employees ask the moment they see this — and have you written the answers down already?"**
   Recommended: seed the FAQ with at least 7 questions: comp, reporting line, location, role change, timing, why now, why us. Bias toward including the questions you wish people would not ask.
   Canon: Edelman Trust Barometer (annual) — internal trust collapses fastest when the obvious question is unanswered.

5. **"Who is the named accountable executive that will appear on the announcement and be present at the town hall, and have they confirmed both?"**
   Recommended: a single, named human at VP level or above; physically (or video-) present; not delegating to comms team.
   Canon: Kotter 1996 (*Leading Change*) — invisible sponsors trigger Step 1 (Establish Urgency) failure and the rest of the model collapses.

6. **"What are you NOT saying, and why?"**
   Recommended: surface the omissions explicitly to legal / sponsor. The unsaid will be inferred; better to know what's being inferred.
   Canon: Sucher & Gupta MIT Sloan layoffs research (2018) — what is omitted from a layoff announcement becomes the lead Glassdoor narrative.

7. **"What does success look like 30 / 60 / 90 days after the announcement — and how are you measuring it?"**
   Recommended: name 3 measurable signals (e.g., regrettable-attrition delta, pulse-survey trust score, manager-cascade audit results).
   Canon: Hiatt 2006 (*ADKAR*) — Reinforcement is the most-skipped ADKAR stage; without measurement there is no Reinforcement.
