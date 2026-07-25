---
name: meeting-analyzer
description: Analyzes meeting transcripts and recordings to surface behavioral patterns, communication anti-patterns, and actionable coaching feedback. Use this skill whenever the user uploads or points to meeting transcripts (.txt, .md, .vtt, .srt, .docx), asks about their communication habits, wants feedback on how they run meetings, requests speaking ratio analysis, mentions filler words or conflict avoidance, or wants to compare their communication across time periods. Also trigger when users mention tools like Granola, Otter, Fireflies, or Zoom transcripts. Even if the user just says "look at my meetings" or "how do I come across in meetings" — use this skill.
---

# Meeting Insights Analyzer

> Originally contributed by [maximcoding](https://github.com/maximcoding) — enhanced and integrated by the claude-skills team.

Transform meeting transcripts into concrete, evidence-backed feedback on communication patterns, leadership behaviors, and interpersonal dynamics.

## Core Workflow

### 1. Ingest & Inventory

Scan the target directory for transcript files (`.txt`, `.md`, `.vtt`, `.srt`, `.docx`, `.json`).

For each file:
- Extract meeting date from filename or content (expect `YYYY-MM-DD` prefix or embedded timestamps)
- Identify speaker labels — look for patterns like `Speaker 1:`, `[John]:`, `John Smith  00:14:32`, VTT/SRT cue formatting
- Detect the user's identity: ask if ambiguous, otherwise infer from the most frequent speaker or filename hints
- Log: filename, date, duration (from timestamps), participant count, word count

Print a brief inventory table so the user confirms scope before heavy analysis begins.

### 2. Normalize Transcripts

Different tools produce wildly different formats. Normalize everything into a common internal structure before analysis:

```
{ speaker: string, timestamp_sec: number | null, text: string }[]
```

Handling per format:
- **VTT/SRT**: Parse cue timestamps + text. Speaker labels may be inline (`<v Speaker>`) or prefixed.
- **Plain text**: Look for `Name:` or `[Name]` prefixes per line. If no speaker labels exist, warn the user that per-speaker analysis is limited.
- **Markdown**: Strip formatting, then treat as plain text.
- **DOCX**: Extract text content, then treat as plain text.
- **JSON**: Expect an array of objects with `speaker`/`text` fields (common Otter/Fireflies export).

If timestamps are missing, degrade gracefully — skip timing-dependent metrics (speaking pace, pause analysis) but still run text-based analysis.

### 3. Analyze

Run all applicable analysis modules below. Each module is independent — skip any that don't apply (e.g., skip speaking ratios if there are no speaker labels).

---

#### Module: Speaking Dynamics

Calculate per-speaker:
- **Word count & percentage** of total meeting words
- **Turn count** — how many times each person spoke
- **Average turn length** — words per uninterrupted speaking turn
- **Longest monologue** — flag turns exceeding 60 seconds or 200 words
- **Interruption detection** — a turn that starts within 2 seconds of the previous speaker's last timestamp, or mid-sentence breaks

Produce a per-meeting summary and a cross-meeting average if multiple transcripts exist.

Red flags to surface:
- User speaks > 60% in a 1:many meeting (dominating)
- User speaks < 15% in a meeting they're facilitating (disengaged or over-delegating)
- One participant never speaks (excluded voice)
- Interruption ratio > 2:1 (user interrupts others twice as often as they're interrupted)

---

#### Module: Conflict & Directness

Scan the user's speech for hedging and avoidance markers:

**Hedging language** (score per-instance, aggregate per meeting):
- Qualifiers: "maybe", "kind of", "sort of", "I guess", "potentially", "arguably"
- Permission-seeking: "if that's okay", "would it be alright if", "I don't know if this is right but"
- Deflection: "whatever you think", "up to you", "I'm flexible"
- Softeners before disagreement: "I don't want to push back but", "this might be a dumb question"

**Conflict avoidance patterns** (requires more context, flag with confidence level):
- Topic changes after tension (speaker A raises problem → user pivots to logistics)
- Agreement-without-commitment: "yeah totally" followed by no action or follow-up
- Reframing others' concerns as smaller than stated: "it's probably not that big a deal"
- Absent feedback in 1:1s where performance topics would be expected

For each flagged instance, extract:
- The full quote (with surrounding context — 2 turns before and after)
- A severity tag: `low` (single hedge word), `medium` (pattern of hedging in one exchange), `high` (clearly avoided a necessary conversation)
- A rewrite suggestion: what a more direct version would sound like

---

#### Module: Filler Words & Verbal Habits

Count occurrences of: "um", "uh", "like" (non-comparative), "you know", "actually", "basically", "literally", "right?" (tag question), "so yeah", "I mean"

Report:
- Total count per meeting
- Rate per 100 words spoken (normalizes across meeting lengths)
- Breakdown by filler type
- Contextual spikes — do fillers increase in specific situations? (e.g., when responding to a senior stakeholder, when giving negative feedback, when asked a question cold)

Only flag this as an issue if the rate exceeds ~3 per 100 words. Below that, it's normal speech.

---

#### Module: Question Quality & Listening

Classify the user's questions:
- **Closed** (yes/no): "Did you finish the report?"
- **Leading** (answer embedded): "Don't you think we should ship sooner?"
- **Open genuine**: "What's blocking you on this?"
- **Clarifying** (references prior speaker): "When you said X, did you mean Y?"
- **Building** (extends another's idea): "That's interesting — what if we also Z?"

Good listening indicators:
- Clarifying and building questions (shows active processing)
- Paraphrasing: "So what I'm hearing is..."
- Referencing a point someone made earlier in the meeting
- Asking quieter participants for input

Poor listening indicators:
- Asking a question that was already answered
- Restating own point without acknowledging the response
- Responding to a question with an unrelated topic

Report the ratio of open/clarifying/building vs. closed/leading questions.

---

#### Module: Facilitation & Decision-Making

Only apply when the user is the meeting organizer or facilitator.

Evaluate:
- **Agenda adherence**: Did the meeting follow a structure or drift?
- **Time management**: How long did each topic take vs. expected?
- **Inclusion**: Did the facilitator actively draw in quiet participants?
- **Decision clarity**: Were decisions explicitly stated? ("So we're going with option B — Sarah owns the follow-up by Friday.")
- **Action items**: Were they assigned with owners and deadlines, or left vague?
- **Parking lot discipline**: Were off-topic items acknowledged and deferred, or did they derail?

---

#### Module: Sentiment & Energy

Track the emotional arc of the user's language across the meeting:
- **Positive markers**: enthusiastic agreement, encouragement, humor, praise
- **Negative markers**: frustration, dismissiveness, sarcasm, curt responses
- **Neutral/flat**: low-energy responses, monosyllabic answers

Flag energy drops — moments where the user's engagement visibly decreases (shorter turns, less substantive responses). These often correlate with discomfort, boredom, or avoidance.

---

### 4. Output the Report

Structure the final output as a single cohesive report. Use this skeleton — omit any section where data was insufficient:

```markdown
# Meeting Insights Report

**Period**: [earliest date] – [latest date]
**Meetings analyzed**: [count]
**Total transcript words**: [count]
**Your speaking share (avg)**: [X%]

---

## Top 3 Findings

[Rank by impact. Each finding gets 2-3 sentences + one concrete example with a direct quote and timestamp.]

## Detailed Analysis

### Speaking Dynamics
[Stats table + narrative interpretation + flagged red flags]

### Directness & Conflict Patterns
[Flagged instances grouped by pattern type, with quotes and rewrites]

### Verbal Habits
[Filler word stats, contextual spikes, only if rate > 3/100 words]

### Listening & Questions
[Question type breakdown, listening indicators, specific examples]

### Facilitation
[Only if applicable — agenda, decisions, action items]

### Energy & Sentiment
[Arc summary, flagged drops]

## Strengths
[3 specific things the user does well, with evidence]

## Growth Opportunities
[3 ranked by impact, each with: what to change, why it matters, a concrete "try this next time" action]

## Comparison to Previous Period
[Only if prior analysis exists — delta on key metrics]
```

### 5. Follow-Up Options

After delivering the report, offer:
- Deep dive into any specific meeting or pattern
- A 1-page "communication cheat sheet" with the user's top 3 habits to change
- Tracking setup — save current metrics as a baseline for future comparison
- Export as markdown or structured JSON for use in performance reviews

---

## Edge Cases

- **No speaker labels**: Warn the user upfront. Run text-level analysis (filler words, question types on the full transcript) but skip per-speaker metrics. Suggest re-exporting with speaker diarization enabled.
- **Very short meetings** (< 5 minutes or < 500 words): Analyze but caveat that patterns from short meetings may not be representative.
- **Non-English transcripts**: The filler word and hedging dictionaries are English-centric. For other languages, note the limitation and focus on structural analysis (speaking ratios, turn-taking, question counts).
- **Single meeting vs. corpus**: If only one transcript, skip trend/comparison language. Focus findings on that meeting alone.
- **User not identified**: If you can't determine which speaker is the user after scanning, ask before proceeding. Don't guess.

## Transcript Source Tips

Include this section in output only if the user seems unsure about how to get transcripts:

- **Zoom**: Settings → Recording → enable "Audio transcript". Download `.vtt` from cloud recordings.
- **Google Meet**: Auto-transcription saves to Google Docs in the calendar event's Drive folder.
- **Granola**: Exports to markdown. Best speaker label quality of consumer tools.
- **Otter.ai**: Export as `.txt` or `.json` from the web dashboard.
- **Fireflies.ai**: Export as `.docx` or `.json` — both work.
- **Microsoft Teams**: Transcripts appear in the meeting chat. Download as `.vtt`.

Recommend `YYYY-MM-DD - Meeting Name.ext` naming convention for easy chronological analysis.

---

## Anti-Patterns

| Anti-Pattern | Why It Fails | Better Approach |
|---|---|---|
| Analyzing without speaker labels | Per-person metrics impossible — results are generic word clouds | Ask user to re-export with speaker identification enabled |
| Running all modules on a 5-minute standup | Overkill — filler word and conflict analysis need 20+ min meetings | Auto-detect meeting length and skip irrelevant modules |
| Presenting raw metrics without context | "You said 'um' 47 times" is demoralizing without benchmarks | Always compare to norms and show trajectory over time |
| Analyzing a single meeting in isolation | One meeting is a snapshot, not a pattern — conclusions are unreliable | Require 3+ meetings minimum for trend-based coaching |
| Treating speaking time equality as the goal | A facilitator SHOULD talk less; a presenter SHOULD talk more | Weight speaking ratios by meeting type and role |
| Flagging every hedge word as negative | "I think" and "maybe" are appropriate in brainstorming | Distinguish between decision meetings (hedges are bad) and ideation (hedges are fine) |

---

## Related Skills

| Skill | Relationship |
|-------|-------------|
| `project-management/senior-pm` | Broader PM scope — use for project planning, risk, stakeholders |
| `project-management/scrum-master` | Agile ceremonies — pairs with meeting-analyzer for retro quality |
| `project-management/confluence-expert` | Store meeting analysis outputs as Confluence pages |
| `c-level-advisor/executive-mentor` | Executive communication coaching — complementary perspective |