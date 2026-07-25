---
name: reflect
description: "Mid-conversation reflection skill that pauses execution and zooms out from detail-mode to honestly reassess direction, assumptions, and bias. Use when the user says 'reflect', 'take a step back', 'step back', 'zoom out', 'are we missing something', 'bigger picture', 'sanity check this', 'are we on track', 'are we overthinking this', 'forest for the trees', or any variation signaling intent to break out of detail-mode and reassess. Also trigger when the conversation has gone deep on implementation details without strategic check-in, or when the user shows signs of being stuck — that's often a signal the framing needs a reset, not more detail work. Intentionally low-intake: runs the 5-dimension analysis immediately when prior context is rich enough; asks one forcing clarifier only when invocation context is too thin to reassess from."
license: MIT
metadata:
  source_spec: "megaprompts/02-reflect-megaprompt.md"
  build_pattern: "Path B (direct conversion)"
  version: 1.0.0
---

# Reflect — Mid-Conversation Reassessment

> **Portability:** Pure-reasoning skill. No external tools required. Works in Claude Code CLI + Claude.ai web natively. Most portable in the v2 collection.

When invoked mid-conversation, this skill **pauses execution** and produces a frank reassessment of where the conversation has been heading. Output is **flowing analysis (no headers, conversational tone)** covering macro perspective, gap analysis, reflective inquiry, bias check, and contextual alignment. The skill ends with a clear directional recommendation: **continue, pivot, or pause to answer a specific question**.

## Invocation Triggers

**Explicit phrases:**

- "reflect"
- "take a step back" / "step back"
- "zoom out"
- "are we missing something"
- "bigger picture"
- "what are we missing"
- "let's pause"
- "sanity check this"
- "are we on track"
- "are we overthinking this"
- "forest for the trees"

**Implicit signals (no phrase needed):**

- Conversation has gone 10+ turns deep on implementation details without strategic check-in
- User shows signs of frustration or stuck-ness
- Repeated dead-ends or pivots within a short span

When you detect an implicit trigger, **don't auto-invoke** — ask the user if they want to step back. Implicit signals are a prompt to OFFER reflection, not to unilaterally run it.

## Stop Directive (Before Reassessing)

**Halt the current thread.** Don't continue execution of the in-progress task. Reflection is a pause, not a side-quest.

This matters because:
- Continuing detail work while "reflecting on the side" defeats the purpose — you'll over-weight the current direction
- The user expects a clear break in cadence
- The reassessment needs full attention to the conversation history

## Grill-Me Optional Clarifier

This skill is intentionally **low-intake** — most invocations should run the 5-dimension analysis immediately without questions. The grill-me discipline applies *only* when the invocation is ambiguous (e.g., user pastes "step back" at the start of a fresh conversation with no prior context to reassess).

### Q1 (optional, asked only when context is too thin to reassess)

> **What specifically should I reassess? Pick one:**
>
> 1. The goal — are we solving the right problem?
> 2. The approach — is the path we're on the best one?
> 3. The assumptions — what are we taking for granted?
> 4. All of the above (default if you have time)
>
> *Why I'm asking:* I'm seeing limited prior context to reassess, so I want to focus the reflection rather than guess. If you'd rather I do all three, that's fine — say so.

Forcing choice with default. **Asked only when context is genuinely thin; otherwise skip and run the full analysis on existing conversation.**

**Stop condition:** One question max. If the user invokes mid-conversation with normal context, no questions are asked — the skill runs directly.

## The 5-Dimension Analysis Framework

Re-read the **full conversation from the original goal forward** — not just recent turns. The discipline that distinguishes real reflection from local-context summary.

### 1. Macro Perspective

- **Original goal:** What did the user actually start trying to do?
- **Drift detection:** Has the conversation moved away from that goal? Toward something better or worse?
- **Connection check:** How does current work connect to the larger objective?

Anchor with specific evidence: "At turn 3 the goal was X; by turn 12 we're working on Y. Is Y a productive narrowing of X, or a drift away?"

### 2. Gap Analysis

- **Unverified assumptions** — what are we taking for granted that we haven't checked?
- **Missing stakeholders / audiences / users** — who needs this beyond the immediate context?
- **Skipped constraints** — technical, regulatory, resource limits not addressed
- **Dismissed alternatives** — paths considered but rejected; revisit briefly
- **External factors** — timing, market, dependencies not in scope

### 3. Reflective Inquiry

- Is the problem framed correctly?
- Solving the right problem vs. an adjacent easier one?
- Simpler path being overcomplicated?
- Harder but more valuable path being avoided?
- **Fresh-eyes perspective:** would someone else approach this differently?

### 4. Bias Check

Five biases — recognize each through specific conversation patterns:

| Bias | Recognition cue |
|---|---|
| **Confirmation bias** | Evidence cited only supports the working hypothesis; counter-evidence absent or dismissed |
| **Sunk cost fallacy** | "We've already invested X" / "we're far enough in to..." instead of fresh cost/benefit |
| **Anchoring** | Stuck on first option mentioned; new options compared against it rather than evaluated independently |
| **Complexity bias** | Adding features / steps / safeguards without specific justification for each |
| **Recency bias** | Over-weighting last few turns; older but important context being ignored |

For each detected bias: name it, cite the specific evidence, suggest a corrective move.

See [`references/cognitive_bias_canon.md`](references/cognitive_bias_canon.md) for the full canon.

### 5. Contextual Alignment

- Does the direction serve the user's actual goals (as known from context)?
- Are external factors being ignored?
- Is this the best use of the user's time and energy right now?
- Connection to other known projects or priorities?

## Tone and Format Rules

The skill must produce:

- **Flowing prose** — no headers, no bullet lists, no structured-report formatting
- **Tight but thorough** — neither a one-liner nor a wall of text
- **Direct critique when warranted** — with specific evidence from the conversation
- **Validation when warranted** — with specific reasoning for why the path is solid
- **No vague reassurance** — "looks good!" without reasoning is rejected
- **No manufactured problems** — when the path is genuinely solid, say so with specific reasons; don't invent issues

See [`references/honest_output_discipline.md`](references/honest_output_discipline.md) for the anti-manufactured-problems framing.

## Closing Recommendation (Mandatory)

Every run ends with one of three directional recommendations:

| Recommendation | When | Format |
|---|---|---|
| **Continue** | Path is solid | "Continue. {specific reasoning for why}." |
| **Pivot to {X}** | Drift has occurred OR better path surfaced | "Pivot toward {X}, away from {what to drop}. {specific evidence}." |
| **Pause for {Q}** | A specific question needs answering before continuing | "Pause for {Q}. Without answering this, the next step risks {specific cost}." |

The closing is always specific — never "you should think more about this" or "consider your options."

## Error Handling

| Situation | Behavior |
|---|---|
| Conversation is very short (no real context to reassess) | Acknowledge limitation, ask user what they want reassessed (Q1 fires) |
| Current direction is genuinely solid | State this clearly with reasoning; don't manufacture problems |
| User invokes mid-task with no clear question | Default to macro perspective + bias check; offer to dig deeper |
| Implicit trigger seems possible but unclear | Don't invoke proactively; ask user if they want to step back |

## Tooling

| Script | Role |
|---|---|
| `scripts/bias_pattern_detector.py` | Scan conversation text for patterns indicative of each of the 5 biases |
| `scripts/conversation_depth_analyzer.py` | Count turns + detect implicit-trigger signals (10+ detail turns, frustration markers) |
| `scripts/directional_recommendation_validator.py` | Verify output ends with Continue / Pivot / Pause + specific reasoning |

## References

- [`references/cognitive_bias_canon.md`](references/cognitive_bias_canon.md) — 5 biases + recognition cues (7+ sources)
- [`references/honest_output_discipline.md`](references/honest_output_discipline.md) — anti-manufactured-problems framing (7+ sources)
- [`references/conversation_reflection_practice.md`](references/conversation_reflection_practice.md) — Schön reflective-practice canon (7+ sources)

## Anti-Patterns To Reject

- Hardcoded user names or specific domain references
- Structured-report output (headers, bullet lists) when prose is required
- Manufactured problems when things are actually fine
- Vague reassurance ("looks good!") instead of specific reasoning
- Reassessing only recent turns instead of the full conversation
- Skipping the closing directional recommendation
- Continuing the in-progress task while "reflecting on the side"

---

**Version:** 1.0.0
**Source spec:** [`megaprompts/02-reflect-megaprompt.md`](../../../../megaprompts/02-reflect-megaprompt.md)
**Build pattern:** Path B (direct conversion). Productivity light-prompt-flow sibling of capture.
