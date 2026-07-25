# Mode 2 Sensing — Detailed Signal Taxonomy

The full reference for Mode 2 (proactive sensing) trigger evaluation. This file expands on the terse signal table in the main SKILL.md, explaining what each signal means in practice, why it indicates handoff readiness, what *looks like* the signal but isn't, and the discipline for the cluster-of-2 rule, anti-triggers, and re-offer behavior.

**When to consult this file:** When calibrating Mode 2 sensing for a deployment, when debugging a session where Mode 2 fired inappropriately or failed to fire, when authoring a system prompt that wants to extend Mode 2 sensing into new conversational patterns, or when a user asks "why did Claude offer the gate just then?"

---

## Table of Contents

1. [The Cluster-of-Two Rule](#the-cluster-of-two-rule)
2. [The 8 Signals — Expanded](#the-8-signals--expanded)
3. [Anti-Triggers — When NOT to Fire](#anti-triggers--when-not-to-fire)
4. [Re-Offer Discipline](#re-offer-discipline)
5. [Calibration Heuristics for Deployment](#calibration-heuristics-for-deployment)

---

## The Cluster-of-Two Rule

Mode 2 fires when Claude detects **two or more signals from distinct categories** in a design conversation. A single weak signal is not sufficient. This rule exists because:

- Single signals fire false positives. Casual mention of "Claude Code" in a discussion of agent ecosystems is not a handoff readiness signal — it's vocabulary. Decomposition language in early scoping ("imagine if we had to do this 50 times") is exploratory, not operational. Either alone produces noise.

- Clusters of signals indicate a real readiness moment. When the user names a specific pump-primer instance ("we did the first one Tuesday") *and* references decomposition ("12 more like this") *and* the conversation has already produced concrete spec, the readiness moment has actually arrived. The cluster is the evidence that the moment is real.

- The rule is operational, not heuristic. Claude's evaluation is: count distinct signal categories present in the recent conversation turn or the surrounding context. If 0 or 1, do nothing. If 2 or more, evaluate against anti-triggers; fire if anti-triggers don't suppress.

A signal "cluster" doesn't require the signals to appear in the same turn. Signals accumulated over the prior 10-20 turns count, as long as they remain operative (the user hasn't reversed course on the decomposition, the pump-primer hasn't been retracted as "actually that didn't work").

---

## The 8 Signals — Expanded

### Signal 1: Decomposition Language

**Pattern:** "There are N more like this," "this pattern repeats," "now we just need to do it for each X," "we have to do this for the rest of them."

**Why it's a signal:** Decomposition language indicates the user has mentally moved from "design the engine" to "execute against the decomposition." The work has been broken into independent units in the user's head, even if not yet enumerated explicitly. This maps directly to condition 5 (Work Decomposes Into Independent Units) and is one of the strongest handoff indicators when present.

**What looks like decomposition but isn't:** Hypothetical decomposition — "imagine if we had to scale this to 100 customers" — is exploratory framing, not operational decomposition. The signal requires the user to be naming *actual* units (12 vendor codes, 27 study guides, 5 outstanding feature flags), not speculating about scale.

### Signal 2: Pump-Primer Language

**Pattern:** "We did the first one manually," "instance #1 shipped," "the first run is done," "we got the first one working."

**Why it's a signal:** The pump-primer is the moment the engine has been proven on a real instance. Pump-primer language indicates condition 4 (Pump-Primer Instance Done) is satisfied. Combined with decomposition language, this is the canonical handoff readiness pattern: the engine works, and there are N similar units waiting to be processed.

**What looks like pump-primer but isn't:** "We did one before" referring to a *different* engine or methodology. The pump-primer must be against the same engine the agent will use. If the user describes a prior instance that used a now-superseded approach, that's not a pump-primer for the current work.

### Signal 3: Copy-Paste Loops Emerging

**Pattern:** User describes manually doing the same operation across multiple files / instances / records. "I've been opening each one and changing the same line." "I just edited the third one and there are still seven to go."

**Why it's a signal:** Copy-paste loops are the failure mode autonomous execution exists to prevent. When the user is *experiencing* the loop in real time, the readiness moment is now — every additional manual instance is wasted work. This signal is often the most urgent of the eight.

**What looks like a copy-paste loop but isn't:** Repetitive but heterogeneous work, where each instance involves different decisions even though the structural shape repeats. If the user is making *judgment calls* on each instance, autonomous execution would either produce wrong outputs or require so much per-instance specification that the leverage disappears.

### Signal 4: Multi-File / Multi-Instance Edits Being Discussed

**Pattern:** "Do this for all 27 of them," "across the whole batch," "for each vendor code in the list," "everywhere this appears."

**Why it's a signal:** The user has named the scope of the work as multi-instance. This is a stronger version of decomposition language — instead of describing future units, the user is describing the operation across a *concrete enumerated set*.

**What looks like multi-instance edits but isn't:** "Across the codebase" or "everywhere this is used" can be either a multi-instance edit (find-and-replace across 50 files) or a single conceptual edit with broad blast radius (refactor a function whose call sites are scattered). The signal requires *enumerable* instances, not "wherever this happens to appear."

### Signal 5: Repetition Signal

**Pattern:** "I keep doing this," "I do this every week," "this is the third time," "every time we have a new client we have to..."

**Why it's a signal:** Repetition signals indicate the work is not just batchable now but *recurring*. The leverage of autonomous execution scales with the number of times the work will be re-run. Repetition also suggests the work has been done enough times to have stabilized — repetition is itself evidence of spec stability (condition 1) and pump-primer readiness (condition 4).

**What looks like repetition but isn't:** "We always have to figure out X for each new project" — variability across instances. If "the same thing" actually means "the same kind of decision but with different inputs each time," autonomous execution may not have leverage.

### Signal 6: Explicit CC Mentions

**Pattern:** User mentions Claude Code, autonomous run, overnight execution, agentic execution, unattended work, "let it run," "let's automate this."

**Why it's a signal:** The user is explicitly thinking about autonomous execution. This is the most direct signal of handoff readiness — the user has the next move on their mind.

**What looks like an explicit CC mention but isn't:** Discussion of Claude Code as a *topic* rather than as a *next move*. "I've been reading about Claude Code lately" is not a handoff signal; "let's run this in Claude Code overnight" is. Calibrate to whether the mention is operational (about this work) or referential (about the tool in general).

### Signal 7: Extended Design Mode With Concrete Spec

**Pattern:** A long design conversation has produced a stable spec. Verification surface is implicit or named. The conversation has crossed from "what should we build" into "how will we run this."

**Why it's a signal:** Duration and concreteness of the design conversation are themselves evidence. A 5-minute scoping isn't ready to hand off to anything — the signal is the *combination* of extended design (≥30 minutes typical, longer for complex work) and a spec that the user can articulate precisely without revising on the spot.

**What looks like extended design but isn't:** Long discussions that *circle* without converging — multiple competing designs in play, the user revising the spec every few turns, no convergence on a single approach. Length without convergence is exploration, not readiness.

### Signal 8: Impatience Signals

**Pattern:** "Let's just run it," "I want to set this and walk away," "can we automate this," "I don't want to do this manually anymore."

**Why it's a signal:** Impatience indicates the user is *ready for handoff* even if they haven't named it. Often the impatience is what surfaces the handoff moment to the user themselves. The signal is high-confidence when it co-occurs with operational readiness signals (decomposition, pump-primer, concrete spec) and low-confidence when it's isolated frustration.

**What looks like impatience but isn't:** Frustration with the work itself ("this is tedious") rather than with the manual execution method ("doing this by hand is slow"). The signal is specifically about the user wanting *the execution model* to change, not the user wanting the work to disappear.

---

## Anti-Triggers — When NOT to Fire

Even when a cluster of signals is present, certain conversational contexts should suppress the Mode 2 offer entirely. The work fails the readiness check by definition in these states; firing the offer is noise.

### Anti-trigger 1: Early Exploration

**Markers:** Open spec questions actively under debate, multiple competing designs in play, the user explicitly framing the work as "thinking out loud," "what if we tried," "I'm not sure yet."

**Why suppress:** The work fails condition 1 (Spec Stability) by definition. A premature offer interrupts genuine design work and may pressure the user toward premature handoff to *escape* the design conversation rather than because the work is actually ready.

### Anti-trigger 2: Different Mode Entirely

**Markers:** The user is in audit mode (reviewing existing work), research mode (investigating a topic for understanding), or retrospective discussion (analyzing what already happened).

**Why suppress:** Handoff is not the next move regardless of how many decomposition or pump-primer phrases appear. An audit mode discussion of how 27 prior shipments worked may use heavy decomposition language ("we did all 27"), but the conversation isn't about doing more — it's about understanding what was done.

### Anti-trigger 3: Just-Failed Run

**Markers:** The user just described a failed autonomous run, is troubleshooting why an agentic execution went wrong, or is in remediation mode after a bad ship.

**Why suppress:** The user is processing a failure, not planning the next handoff. Even if signals appear ("we'll have to redo all 12"), offering the gate is poorly-timed. Wait until the user has resolved the failure and re-engaged forward.

### Anti-trigger 4: Casual Conversation

**Markers:** The conversation isn't about a specific work item — it's a general chat about workflows, tools, or ideas. Decomposition or CC mentions are vocabulary, not operational signals.

**Why suppress:** There's no work to evaluate. The Skill needs an actual work_context; if there's no work in scope, the gate has nothing to act on.

### Anti-trigger 5: User Mid-Thought

**Markers:** The user is in the middle of articulating something. They've started a sentence, paused, made a parenthetical, but the main point isn't out yet.

**Why suppress:** Interrupting mid-thought breaks the user's articulation. Defer the offer to a natural pause — typically the next turn or two, when the user has finished saying what they were saying. The signals will still be present at the pause; nothing is lost by waiting.

---

## Re-Offer Discipline

If a Mode 2 offer is declined, the discipline for re-offering is strict.

**Wait for a new signal cluster.** If the same signals that triggered the original offer are still present (the user hasn't addressed them but also hasn't escalated), do not re-offer. Re-offering on the same evidence reads as nagging — the user already considered and declined the move.

**Recognize new clusters.** If new signals emerge — impatience signals when the original cluster was decomposition + pump-primer, or a fresh CC mention after the first offer was declined — that's a new cluster. Re-offering on new evidence is appropriate.

**Don't re-offer in the same turn.** Even if a fresh cluster appears in the same turn that an offer was declined, defer to the next turn. Same-turn re-offers feel like negotiation rather than helpful surfacing.

**Track the offer state.** A user who has declined twice within a session has signaled they don't want the gate proactively offered for this work. Treat that as a soft preference for the rest of the session — only re-offer if signals intensify dramatically (e.g., the user explicitly says "actually, let's just do this" after two prior declines, which is itself a fresh impatience signal).

**Decline reasons matter.** If the user declined because the work isn't ready ("we're still figuring out X"), the next legitimate offer requires evidence that X is now figured out. If the user declined because they prefer to invoke the gate manually ("I'll run it when I'm ready"), don't proactively offer again at all — the user has expressed a preference for explicit invocation.

---

## Calibration Heuristics for Deployment

When deploying Mode 2 in a new environment (different user, different work class, different project), some calibration is expected. Heuristics for tuning:

**If Mode 2 is firing too often:** Tighten the cluster requirement — require 3 distinct signal categories instead of 2 — for the first few weeks. Add the deployment's typical false-positive context to the anti-trigger list.

**If Mode 2 is firing too rarely:** Examine whether the signals are appearing in language patterns Mode 2 doesn't recognize. Real signals are messier than the canonical phrasing — calibrate to *meaning* not *exact wording*. Consider whether the deployment's typical work uses vocabulary that should be added to the signal taxonomy.

**If signals are present but fire feels wrong:** Look for unstated anti-triggers. The user may be in a mode the deployment hasn't recognized as anti-trigger context (e.g., their team's standup discussions use heavy decomposition language but aren't operational handoff moments).

**If users decline systematically:** The profile or work class may not be a good fit for autonomous execution. Mode 2 is correctly surfacing readiness, but the user is correctly declining because the deployment's actual rollback cost or verification surface doesn't support unattended runs. The Skill is doing its job; the deployment may not be ready for autonomous execution generally.

The goal of calibration is not to maximize Mode 2 fires — it's to maximize the *signal-to-noise ratio* of fires the user finds useful. A Mode 2 that fires 10 times a week and the user accepts 8 of them is well-calibrated. One that fires 50 times and the user accepts 8 is poorly-calibrated, even though it surfaces more readiness moments.
