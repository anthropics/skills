# Internal Comms Brief Template

A 20-minute fill-out. Copy this template, replace the bracketed values, save as `comms_brief.json` (the JSON skeleton at the bottom of this file), and pass to the three scripts:

```bash
python3 scripts/comms_template_filler.py     --input comms_brief.json --output markdown
python3 scripts/change_announcement_builder.py --input comms_brief.json --profile scaleup --output markdown
python3 scripts/comms_calendar_builder.py    --input comms_brief.json --output markdown
```

(Note: each script reads a slightly different subset of fields; the JSON below is the union of all three.)

---

## Section 1 — The change event (10 minutes)

**Change type** (one of `reorg | tool_rollout | policy_change | leadership_change | layoff | acquisition | product_launch_internal | benefit_change`):
> [e.g., reorg]

**Change summary** (one sentence — what is changing):
> [e.g., Merging the Platform and Infrastructure teams into a single Platform Engineering group reporting to the new VP of Platform Engineering.]

**Why this change** (one paragraph — the business reason; reference the signal, not the politics):
> [e.g., Two separate teams created a coordination tax on every cross-cutting infrastructure project. Cycle time for a typical cross-team initiative is currently 6+ weeks; the merged team has a target of 2 weeks.]

**What changes** (concrete deltas — reporting lines, roles, processes):
> [e.g., All Infrastructure engineers begin reporting to managers within the Platform org effective June 15. The on-call rotation merges into a single rotation. The two separate Slack channels merge into #platform-eng.]

**What stays the same** (load-bearing — employees infer everything changes if you don't say what doesn't):
> [e.g., Compensation, level, vacation balances, manager 1:1 cadence, and the existing OKRs through the end of Q2.]

**Effective date** (ISO 8601):
> [e.g., 2026-06-15]

**Who decided** (named human or named small group — never "the leadership team" alone):
> [e.g., VP Engineering Sarah Lee, with the support of the CTO and the engineering leadership team.]

**Change magnitude** (one of `low | medium | high | disruptive` — assume one level higher than instinct):
> [e.g., high]

**Audience segments** (list — at least 3 typical: managers, ICs, rest-of-company; for layoffs add affected/unaffected):
> [e.g., ["engineering managers", "engineering ICs", "rest of company"]]

**Audience size** (integer — total employees who will see this):
> [e.g., 320]

---

## Section 2 — Comms infrastructure (5 minutes)

**Channels available** (subset of `email, slack, allhands, manager_cascade, town_hall, intranet`):
> [e.g., ["email", "slack", "allhands", "manager_cascade", "town_hall", "intranet"]]

**Working days available** (integer — days between brief and effective date):
> [e.g., 21]

**Named sponsor executive** (the human who will sign the email AND appear at the town hall):
> [e.g., Sarah Lee, VP Engineering]

**Sponsor town-hall confirmed?** (yes/no — if no, stop and confirm before continuing):
> [yes]

---

## Section 3 — FAQ seed (5 minutes)

List 5–10 questions employees will ask, with a draft answer. Bias toward including the questions you wish they would not ask.

```
[
  {"q": "Will my compensation change?", "a": "No. Compensation is unchanged."},
  {"q": "Will my reporting line change?", "a": "Most ICs will report to the same manager. Engineers currently reporting to the two affected senior managers will be reassigned; affected individuals will be notified by 6/10."},
  {"q": "Is this a precursor to layoffs?", "a": "No. No headcount reductions are planned in connection with this re-org."},
  {"q": "Why now?", "a": "Cycle-time data over Q1 2026 made the coordination tax visible and quantifiable. Waiting another quarter would compound the problem."},
  {"q": "What about the on-call rotation?", "a": "The two rotations merge on 6/15. New rotation roster will be published 6/8. No engineer will be on-call more days per month than today."},
  {"q": "Who is the new VP?", "a": "Sarah Lee (currently VP Engineering) takes on VP Platform Engineering. The current VP Infrastructure transitions to a Distinguished Engineer role."},
  {"q": "What about my team's Q2 OKRs?", "a": "Existing OKRs remain through end of Q2; Q3 OKRs will be set by the new leadership team in late June."}
]
```

---

## Section 4 — Next steps and measurement

**Next steps** (what employees should do immediately after the announcement):
> [e.g., Managers: review the talking points doc by EOD 6/14. ICs: no action required; office hours 6/16 and 6/20 if you have questions.]

**Success criteria 30/60/90 days** (the measurement Reinforcement requires):
> [e.g., 30d: pulse-survey trust score steady or improved; 60d: cross-team cycle time on top-3 initiatives < 4 weeks; 90d: no regrettable attrition above baseline.]

---

## JSON skeleton (combined input — save as `comms_brief.json`)

```json
{
  "change_type": "reorg",
  "change_summary": "Merging Platform and Infrastructure into one group",
  "why_this_change": "Coordination tax on cross-cutting infra work; cycle time 6+ weeks",
  "what_changes": "Reporting lines, on-call rotation, Slack channels merge",
  "what_stays_the_same": "Compensation, level, vacation balances, manager 1:1 cadence, Q2 OKRs",
  "effective_date": "2026-06-15",
  "who_decided": "VP Engineering Sarah Lee with leadership team",
  "change_magnitude": "high",
  "audience_segments": ["engineering managers", "engineering ICs", "rest of company"],
  "channels": ["email", "slack", "allhands", "manager_cascade", "town_hall", "intranet"],
  "next_steps": "Manager talking points by EOD 6/14; office hours 6/16 and 6/20",
  "q_and_a_seed": [
    {"q": "Will my compensation change?", "a": "No."},
    {"q": "Will my reporting line change?", "a": "Most ICs same manager; some reassignments notified by 6/10."},
    {"q": "Is this a precursor to layoffs?", "a": "No."},
    {"q": "Why now?", "a": "Cycle-time data over Q1 2026 made the coordination tax quantifiable."},
    {"q": "What about on-call?", "a": "Rotations merge 6/15; no engineer more days per month than today."}
  ],
  "change_event": {
    "name": "Platform + Infra re-org",
    "magnitude": "high",
    "effective_date": "2026-06-15",
    "audience_size": 320
  },
  "channels_available": ["email", "slack", "allhands", "manager_cascade", "town_hall", "intranet"],
  "working_days_available": 21
}
```

---

## Pre-publication checklist (Matt Pocock discipline — answer ALL before sending)

- [ ] Magnitude is honest (one level higher than instinct, especially for layoffs).
- [ ] Sponsor confirmed for town hall + Q&A thread.
- [ ] Manager talking points written and shared with managers 24–48h ahead.
- [ ] FAQ seeded with at least 7 questions including the ones you wish weren't asked.
- [ ] Passive-voice accountability scrubbed from announcement.
- [ ] At least one synchronous channel scheduled (town hall / all-hands) for high or disruptive.
- [ ] At least 5 touchpoints in the calendar (Prosci floor).
- [ ] T+7 enablement and T+14 reinforcement touchpoints scheduled.
- [ ] Success criteria at 30/60/90 days are measurable.
- [ ] What's NOT being said is surfaced explicitly to sponsor / legal.
