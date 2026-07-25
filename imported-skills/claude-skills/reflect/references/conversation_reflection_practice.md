# Conversation Reflection Practice — Schön's Discipline Applied

This reference answers exactly one decision: **what theoretical foundation grounds the reflect skill's discipline of re-reading the full conversation, running structured analysis, and ending with a directional recommendation?**

## The Core Frame

Donald Schön's *The Reflective Practitioner* (1983) distinguished two modes:

- **Reflection-in-action** — adjusting while doing (most everyday reflection)
- **Reflection-on-action** — stepping back to examine, after the fact

The reflect skill operationalizes **reflection-on-action** in mid-conversation. It pauses the in-flight task, re-reads what's been done, runs structured analysis, and emerges with a corrected direction.

This is harder than reflection-in-action because it requires:

1. **Breaking flow** — most users want to continue executing, not pause
2. **Re-reading from origin** — not just recent turns
3. **Honest output** — even when the user implicitly wants validation

## Why Re-Read Full Conversation (Not Just Recent)

The most common failure of casual reflection is **recency-bias reflection** — re-reading only the last 3-5 turns. This produces a summary, not a reflection.

True reflection requires re-reading from the **original goal**, because:

- The framing at turn 1 sets what counts as "on track"
- Drift is invisible from inside the drift (you don't notice you've moved until you compare to where you started)
- Recent context is often tactical; original context is strategic

Schön emphasized this in his discussion of "professional reflection" — the discipline is going back to the implicit framing that shaped the work, not just the recent moves.

## The 5-Dimension Framework Origin

The reflect skill's 5 dimensions (Macro, Gap, Reflective, Bias, Contextual) are an operationalization of several reflective-practice traditions:

| Dimension | Tradition |
|---|---|
| **Macro Perspective** | Schön's "frame analysis" — what frame is being used? Does it still serve? |
| **Gap Analysis** | Argyris & Schön's "double-loop learning" — what assumptions haven't been examined? |
| **Reflective Inquiry** | Kolb's experiential learning cycle — what new framing might serve better? |
| **Bias Check** | Kahneman/Tversky cognitive bias canon — what systematic errors might apply? |
| **Contextual Alignment** | Polanyi's tacit knowledge — what context is implicit and ignored? |

This synthesis isn't novel — it's what practiced reflection-on-action looks like. The skill's value is making it operational + repeatable.

## Reflection-in-Action vs Reflection-on-Action

| Mode | When | Purpose | The reflect skill |
|---|---|---|---|
| Reflection-in-action | While doing | Adjust mid-action | Not this — that's just normal Claude behavior |
| Reflection-on-action | After/pause | Re-examine direction | **This** — the skill is invoked explicitly to pause |

The skill's "stop directive" (halt the current thread) enforces this distinction. Continuing detail work while "reflecting on the side" collapses both modes and defeats the purpose.

## Why Closing Recommendation Is Mandatory

A reflection that ends with "consider your options" or "think about this more" has failed. Schön emphasized that reflection should produce **action-oriented insight** — the practitioner emerges with a clear next move, not more deliberation.

The Continue / Pivot / Pause structure forces this:

- **Continue** — explicit endorsement, with reasoning
- **Pivot to {X}** — explicit redirect, with target
- **Pause for {Q}** — explicit blocker, with question

Without one of these, the reflection produced introspection without resolution. That's a useful private activity but not a useful skill output.

## When NOT to Reflect

Reflection has costs:

- **Time** — full reflection takes attention
- **Flow disruption** — pausing breaks momentum
- **Risk of over-reflecting** — endless analysis without execution

The skill should NOT trigger:

- **On every implicit signal** — 10+ detail turns alone isn't enough; the user should be the one to choose
- **In short conversations** — no real context to reassess
- **As a default response** — "let me reflect first" should not become a stalling tactic

The skill is most valuable when used **sparingly and intentionally** — once or twice per substantial task, at strategic moments.

## The Honest-Output Discipline Connection

Reflective practice traditions emphasize **integrity** — the reflection produces what's actually there, not what the practitioner wants to find. Schön explicitly contrasted "espoused theory" (what we say we believe) with "theory-in-use" (what we actually do).

The reflect skill's honest-output discipline (no manufactured problems, no vague reassurance) is the same integrity principle. If the path is genuinely solid, the honest reflection says so with specific evidence. If the path has drifted, the honest reflection says so with specific evidence. The discipline doesn't distort findings to match expectations.

See [`honest_output_discipline.md`](honest_output_discipline.md) for the operational form.

## Operational Patterns

### Pattern 1: Quick reflection (good case)

Conversation is 8 turns in. User says "step back." Skill:

1. Halts current thread
2. Re-reads from turn 1
3. Runs 5-dimension analysis
4. Finds path is solid
5. Validates with specific reasoning + Continue

Total time: < 1 minute. Output: ~200-300 words.

### Pattern 2: Mid-drift reflection

Conversation is 15 turns in. User says "are we missing something?" Skill:

1. Halts current thread
2. Re-reads from turn 1
3. 5-dimension analysis surfaces sunk-cost bias + drift from original goal
4. Critiques with specific evidence
5. Recommends Pivot to specific direction

Total time: ~2 minutes. Output: ~400-600 words.

### Pattern 3: Thin-context reflection

User says "reflect" at turn 3 of a fresh conversation. Skill:

1. Halts
2. Re-reads — finds limited context
3. Asks Q1 (clarifying — what to reassess)
4. After answer, runs focused analysis
5. Recommendation per their focus

Total time: ~1-2 minutes (with user response). Output: shorter, focused.

## Anti-Patterns from Reflective Practice Literature

### "Endless reflection without action"

Kolb warned about getting stuck in the reflection phase of his learning cycle. Reflection without action becomes navel-gazing. The skill's mandatory closing recommendation prevents this.

### "Reflection as confirmation"

Argyris noted that practitioners often use reflection to confirm what they already believed. The bias check (Dimension 4) is specifically designed to counter this.

### "Reflection as performance"

Schön observed that some reflection is performed for audience rather than substance — "see, I'm being reflective!" The honest-output discipline rejects this.

### "Reflection on recent turns only"

Recency-bias reflection. Produces summary, not insight. The "re-read from original goal" requirement counters this.

## Citations (7 sources)

1. **Donald Schön, *The Reflective Practitioner* (Basic Books, 1983).** Foundational text. Source for the reflection-in-action vs reflection-on-action distinction, frame analysis, and the discipline of re-examining implicit frames.

2. **Schön, *Educating the Reflective Practitioner* (Jossey-Bass, 1987).** Schön's follow-up — operationalizes reflection-on-action for professional education. Source for the "halt and re-examine" discipline.

3. **Chris Argyris & Donald Schön, *Theory in Practice* (Jossey-Bass, 1974).** Source for the espoused-theory vs theory-in-use distinction that grounds the honest-output discipline. Argyris's "double-loop learning" is the foundation for the gap-analysis dimension.

4. **David Kolb, *Experiential Learning* (Prentice-Hall, 1984).** Source for the four-stage learning cycle (Concrete Experience → Reflective Observation → Abstract Conceptualization → Active Experimentation). The reflect skill operationalizes the second stage in conversation form.

5. **Michael Polanyi, *The Tacit Dimension* (Doubleday, 1966).** Source for the implicit-context-matters principle that grounds the Contextual Alignment dimension. Polanyi's "we know more than we can tell" justifies examining unstated context.

6. **Kahneman & Tversky cognitive bias canon (1972-onwards).** Source for the bias-check dimension. See `cognitive_bias_canon.md` for the full 5-bias treatment.

7. **Bret Victor, "Inventing on Principle" (talk, 2012) + "Up and Down the Ladder of Abstraction" (essay).** Source for the discipline of making thinking visible. Reflection outputs that cite specific conversation evidence make the reflector's reasoning visible; vague outputs hide it.
