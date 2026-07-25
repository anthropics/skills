# Internal-Comms Announcement Anti-Patterns

Eight specific anti-patterns drawn from Prosci research, MIT Sloan layoffs research, HBR transparent-leadership work, and three case studies of public failures. Each is a "do not send" signal when surfaced by the skill's validators.

---

## 1. Slack-only announcement of a layoff (or any disruptive change)

**Pattern:** The change is announced via a single Slack message in a company-wide channel. No synchronous channel (town hall, manager 1:1). No FAQ. No follow-up.

**Why it fails:** Disruptive changes require synchronous channels to demonstrate sponsor presence and to absorb the immediate emotional reaction. Asynchronous channels leave employees alone with the news, which compounds resistance and accelerates Glassdoor narrative formation.

**Canon:** Prosci (11th edition) — synchronous channels are required for high-magnitude changes; Bersin two-way-channel research; Sucher & Gupta MIT Sloan layoffs research (2018).

**Skill enforcement:** `comms_calendar_builder.py` warns when no synchronous channel (town_hall / allhands) is in the plan for a disruptive event.

---

## 2. Passive voice for accountability — "decisions have been made"

**Pattern:** The announcement uses agentless passive constructions: "decisions have been made", "it has been determined that", "the organization has decided".

**Why it fails:** Passive accountability is a Vulnerability-Based-Trust failure (Lencioni). Employees know decisions are made by humans; hiding which human signals fear of accountability and invites speculation about who is really behind the change.

**Canon:** Lencioni *The Advantage* (2012); Adam Grant on apology mechanics; classic Strunk & White discipline on active voice.

**Skill enforcement:** `change_announcement_builder.py` flags "decisions have been made" / "the decision has been made" as a WARN-level validation.

---

## 3. Magnitude downplay — "minor restructuring" for a 30% RIF

**Pattern:** A high or disruptive change is framed with low-magnitude language. The canonical example: Better.com's Vishal Garg layoff (Dec 2021) framed the 900-person cut as a "tough decision" without acknowledging the human magnitude, and conducted it over Zoom in 3 minutes.

**Why it fails:** Employees know the magnitude. The mismatch between announced framing and lived reality is the lead Glassdoor / press narrative for years afterward.

**Canon:** Sucher & Gupta MIT Sloan research; the Better.com / Vishal-Garg case; the Bishop Fox layoff-comms post-mortem.

**Skill enforcement:** `change_announcement_builder.py` rejects "minor update" / "small change" / "minor restructuring" framing when magnitude is `high`; rejects "exciting news" / "thrilled to" / "celebrate" framing when magnitude is `disruptive`.

---

## 4. Celebratory framing for a job cut

**Pattern:** The announcement uses "exciting news" / "thrilled to share" / "great opportunity" framing for a layoff, role-elimination, or office closure.

**Why it fails:** Tone-content collision is the highest-trust-cost framing error. Employees read it as either out-of-touch (leadership doesn't know what this means to people) or manipulative (leadership knows and is trying to bury it). Both readings are durable and shareable.

**Canon:** Sucher & Gupta MIT Sloan research; the Twitter / Musk layoff comms post-mortems (Nov 2022); IABC Code of Ethics on truthful communication.

**Skill enforcement:** `change_announcement_builder.py` rejects celebratory keyword set when magnitude is `disruptive`.

---

## 5. Leadership absent on day-of

**Pattern:** The announcement is sent by Internal Comms or HR but the named accountable executive is not present at the town hall, does not respond in the Q&A thread, and is not available to managers in the 24 hours after.

**Why it fails:** Kotter Step 1 (Establish Urgency) collapses when the sponsor is invisible. Employees correctly infer that leadership is not committed enough to the change to be visible on it.

**Canon:** Kotter *Leading Change* (1996); Prosci sponsor-active-and-visible research (the #1 contributor to change success in every Prosci study since 2003).

**Skill enforcement:** `comms_calendar_builder.py` assigns `sponsor_exec` as the owner of the T+0 announcement and the T+1 Q&A thread; if these are reassigned, the calendar comment surfaces the deviation.

---

## 6. No manager talking points (managers find out same time as ICs)

**Pattern:** Managers receive the announcement at the same moment as their direct reports, with no pre-brief, no FAQ, no script.

**Why it fails:** Direct manager is the #1 most-trusted channel (Edelman, Bersin). A manager who cannot answer a basic question from a report at announcement time signals "leadership does not trust me with this" — which the report then transitively applies to the announcement itself.

**Canon:** Prosci Best Practices in Change Management; Edelman Trust Barometer (manager-trust finding, every year since 2018); Welch & Jackson 2007.

**Skill enforcement:** `comms_calendar_builder.py` schedules a T-3 manager_cascade pre-brief by default and warns if it is missing.

---

## 7. No follow-up touchpoints

**Pattern:** One announcement, no T+7 enablement touchpoint, no T+14 check-in. The comms team considers the work done at T+0.

**Why it fails:** ADKAR Reinforcement is unstaffed; Bridges' "Beginnings" phase is unsupported. Employees infer the leadership team has moved on to the next priority, which signals the change was not important enough to sustain — which becomes a self-fulfilling prophecy.

**Canon:** Hiatt *ADKAR* (Reinforcement stage); Bridges *Managing Transitions* (Beginnings phase); Prosci 5–7 touchpoint floor research.

**Skill enforcement:** `comms_calendar_builder.py` includes T+7 (Ability) and T+14 (Reinforcement) touchpoints; warns if either is missing from a custom plan.

---

## 8. No FAQ for a disruptive change

**Pattern:** A high or disruptive change ships without a published FAQ. Employees ask the obvious questions in Slack; the answers are inconsistent across teams; the rumor cycle outpaces the official channel.

**Why it fails:** If you don't write the FAQ, Slack writes it for you. The questions are knowable in advance (comp, reporting line, location, role, timing, why now); pre-answering them is cheap; not pre-answering them is expensive in trust.

**Canon:** Heath & Heath *Switch* (Path-shaping); Edelman Trust Barometer (unanswered-question finding); HBR Adam Grant on radical candor in organizations.

**Skill enforcement:** `comms_template_filler.py` always produces an FAQ artifact with a 7-question seed; flagging would be added if the FAQ artifact is suppressed.

---

## Case-study sources

- **Better.com / Vishal Garg layoff** (Dec 2021) — 900-person Zoom layoff with insufficient pre-comm and celebratory framing; the comms is the lead narrative two years later. Multiple post-mortems published in HBR / Fortune.
- **Twitter / Musk layoffs** (Nov 2022) — email-only notification, managers uninformed, no FAQ, no follow-up. Used as the contemporary example of every anti-pattern compounding.
- **Yahoo work-from-home reversal** (Feb 2013, Marissa Mayer) — leaked memo, no manager cascade, magnitude downplayed. The reversal became the dominant story for the rest of the CEO tenure.
- **Bishop Fox layoff comms** — published post-mortem on doing layoff comms responsibly; cited as a contrast case showing how the same event with good comms produces a fundamentally different employee reaction.

## Sources at a glance

| # | Source | Type | Used in |
|---|---|---|---|
| 1 | Prosci 11th edition | Practitioner research | Synchronous-channel rule |
| 2 | Sucher & Gupta (MIT Sloan, 2018) | Academic research | Magnitude-downplay rejection |
| 3 | Lencioni *The Advantage* (2012) | Practitioner book | Passive-voice flag |
| 4 | Adam Grant (HBR, multiple) | Practitioner / academic | Apology + radical-candor mechanics |
| 5 | Better.com / Vishal Garg case (2021) | Case study | Magnitude + celebratory-framing tests |
| 6 | Bishop Fox layoff post-mortem | Case study (contrast) | What "good" looks like |
| 7 | Yahoo WFH-reversal case (2013) | Case study | Manager-cascade failure |
| 8 | Twitter / Musk layoffs case (2022) | Case study | Multi-pattern compound failure |
