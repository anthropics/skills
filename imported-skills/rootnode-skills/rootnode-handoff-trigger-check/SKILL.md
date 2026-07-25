---
name: rootnode-handoff-trigger-check
description: >-
  Evaluates whether work-in-design is ready to hand off from a chat design
  conversation to autonomous execution (Claude Code, n8n, agent runtime).
  Runs a 7-condition gate: spec stability, verification surface, invariants,
  pump-primer, work decomposition, rollback cost, token budget headroom.
  Three invocation modes — deliberate (caller provides work_context,
  returns JSON verdict), proactive sensing (Claude detects handoff signals
  in design conversation and offers the check), conversational walkthrough
  (Claude walks the 7 conditions as discussion topics). Returns structured
  JSON in all modes. Use when designing a Claude Code deployment, scoping
  an autonomous run, or deciding next move. Trigger on: "ready to hand
  off," "ready for execution," "is this CC-ready," "handoff check," "walk
  me through readiness," "are we ready to ship this," "should I just hand
  this off," or proactive detection. Do NOT use for evaluating completed
  work, runtime selection, or prompt quality. Profile-agnostic.
license: Apache-2.0
metadata:
  author: rootnode
  version: "1.1.2"
  original-source: "root.node design 2026 — runtime layer (gates, router, profile builder)"
  companion-files: "schema/profile.schema.json, profiles/strict.json, profiles/balanced.json, profiles/lenient.json, references/examples.md, references/troubleshooting.md, references/sensing-triggers-detailed.md"
  changelog: "1.1.2 (2026-05-05): Activation precision tuning. Added two symptom-phrased triggers (\"are we ready to ship this,\" \"should I just hand this off\") to broaden activation under user vocabulary that doesn't include the word 'handoff.' No methodology, schema, or workflow changes; behavior identical to 1.1.1 once activated. 1.1.1 (2026-05-01): Structural patch to align with rootnode authoring convention. Added references/ folder with three on-demand-loaded files (examples, troubleshooting, sensing-triggers-detailed). SKILL.md body slimmed ~23% via content extraction (Examples and Troubleshooting sections moved out; sensing-triggers detail expanded into a dedicated reference); behavior identical to 1.1. 1.1 (2026-05-01): Added Mode 2 (proactive sensing) and Mode 3 (conversational walkthrough). Mode 1 (deliberate gate) behavior unchanged from 1.0 — backward compatible. Deployment target: chat-Project (CP) side of CP/CC split."
  discipline_post: phase-30
---

# Handoff Trigger Check

Evaluate whether work-in-design is ready to hand off to autonomous execution. Runs a 7-condition gate, applies the active profile's pass threshold, and returns a structured verdict. The single most important check before letting an agent runtime — Claude Code, an n8n workflow, an OpenClaw instance, or any other autonomous executor — take over from human-led design.

The premise: **the costliest mistake in human/agent collaboration is holding work in human hands after it's ready to be executed.** A documented production case shipped 27 similar instances in under 24 hours of autonomous Claude Code time after a week of human-led ground-truth setup on the first instance; the week was necessary, but the cost was holding instances 2-27 in human hands for any time at all after the engine passed verification on instance 1. This Skill exists to make that handoff moment a measurable trigger, not a vibes call.

## Important

**Profile-agnostic by design.** The Skill takes a profile config as input. The profile sets the pass threshold per condition (e.g., a "sleeping" profile may require 95% confidence on all 7 conditions because human-in-the-loop is unavailable; a "desk" profile may accept 60% because corrections happen in real time). No human's name, schedule, or specific availability appears in the Skill itself. Profiles are configuration data shipped separately.

**Token budget is one of the seven conditions, not an afterthought.** Autonomous runs that exceed budget mid-execution leave half-finished work and degrade trust. Budget headroom is checked as a precondition. Where token telemetry is unavailable, the profile may declare an estimated token budget that the requestor must input.

**Output is structured JSON, not prose.** The Skill emits a parseable verdict that an orchestrator can act on without an LLM round-trip. Human-readable summary is provided alongside but is secondary.

**The Skill answers a binary question, not a graduated one.** Either the work is ready to hand off or it is not. When not, the verdict names the specific blocker(s) so the design conversation can address exactly those gaps and re-check.

**Deployment target.** This Skill runs on the chat-Project (CP) side of the design→execution boundary — typically inside a Claude Project where design conversations happen. It is the literal mechanism that decides when work moves from CP to autonomous execution; placing it on the CC side defeats its purpose.

---

## Invocation Modes

This Skill supports three modes of invocation. All three produce the same structured JSON verdict against the same 7 conditions. They differ only in how `work_context` is gathered and how the result is delivered.

### Mode 1 — Deliberate Gate

**Trigger:** Caller provides a fully-formed `work_context` payload — typically because an orchestrator, scheduled job, or deliberate user action invoked the Skill with structured input ready for evaluation.

**Behavior:** Mechanical. Skill receives `profile` + `work_context`, evaluates the 7 conditions against provided evidence, applies the profile's threshold rule, returns JSON verdict. No conversational scaffolding.

**Output:** Structured JSON only (or JSON + a brief human-readable summary when `verbose: true`).

**When this mode fits:** Orchestrator-driven invocation; CI/CD or scheduled workflow; user has done the prep work and just wants the verdict; programmatic callers that will parse the JSON and act on it.

This is the v1.0 behavior and remains byte-identical for backward compatibility. Existing v1.0 callers do not need to change anything.

### Mode 2 — Proactive Sensing

**Trigger:** Claude is participating in a design conversation (typically a chat Project, not an autonomous Claude Code session) and detects signals that the work being discussed is approaching handoff readiness. See "Proactive Sensing Triggers" below for the signal list. The Skill is not invoked by name — Claude initiates the offer when signals warrant.

**Behavior:** Claude offers the check rather than running it silently:

> "I'm noticing [specific signal X, specific signal Y]. The handoff-gate is the formal mechanism for evaluating whether this work is ready to move to autonomous execution. Want me to run it? I can either gather the evidence from our conversation or walk through the 7 conditions with you one at a time."

If the user accepts, Claude either:
- (a) gathers `work_context` from the existing conversation history and runs Mode 1 mechanics — recommended when the conversation already contains the evidence, or
- (b) shifts into Mode 3 (conversational walkthrough) — recommended when the user prefers to talk through it.

If the user declines, Claude notes the offer was declined and continues the design conversation. Do not re-offer in the same turn; re-offer only on a new triggering signal cluster. See `references/sensing-triggers-detailed.md` for the full re-offer discipline.

**Output:** Same structured JSON verdict as Mode 1, plus a brief conversational framing explaining why the offer was made and how the verdict reads against the work just discussed.

**When this mode fits:** Chat-interface design conversations where the human is not yet thinking about handoff but the work is ready. The Skill's job here is to surface the readiness moment — not to wait to be asked.

### Mode 3 — Conversational Walkthrough

**Trigger:** User explicitly requests a walkthrough ("walk me through readiness," "talk me through the handoff check," "let's evaluate whether we're ready"), OR Mode 2 was accepted with a preference to discuss rather than auto-evaluate, OR a user new to the Skill wants to understand each condition.

**Behavior:** Claude walks the 7 conditions as discussion topics, one at a time, in order:

1. Frame the condition (one sentence — what it's checking, why it matters).
2. Ask what evidence supports it for this work.
3. Capture the evidence (or note its absence).
4. Mark pass/fail and move to the next condition.

After all 7 are walked, produce both:
- The structured JSON verdict (so the result is parseable and loggable).
- A conversational summary (3-6 sentences) naming the verdict, the most important blockers if any, and the recommended next steps.

**Output:** Structured JSON + conversational summary (always — `verbose: true` is implicit in this mode).

**When this mode fits:** Pedagogically valuable — first time a user is using the Skill on a given class of work, novel work where evidence is uncertain, or any case where the user wants to understand *why* the verdict is what it is rather than just receive it. Also the right mode when the design conversation hasn't yet produced clean evidence and a walk-through is what generates it.

### Proactive Sensing Triggers

Mode 2 fires when Claude detects **two or more signals from distinct categories** in a design conversation. A single weak signal is not sufficient; the cluster-of-two rule prevents false positives from casual mentions or vocabulary use.

| Signal | Pattern in conversation |
|---|---|
| Decomposition language | "There are N more like this," "this pattern repeats," "now we just need to do it for each X" |
| Pump-primer language | "We did the first one manually," "instance #1 shipped," "the first run is done" |
| Copy-paste loops emerging | User describes manually doing the same operation across multiple files / instances / records |
| Multi-file / multi-instance edits being discussed | "Do this for all 27 of them," "across the whole batch," "for each vendor code" |
| Repetition signal | "I keep doing this," "I do this every week," "this is the third time" |
| Explicit CC mentions | User mentions Claude Code, autonomous run, overnight execution, agentic execution, or unattended work |
| Extended design mode with concrete spec | Long design conversation has produced a stable spec; verification surface is implicit or named |
| Impatience signals | "Let's just run it," "I want to set this and walk away," "can we automate this" |

A Mode 2 offer should reference the *specific* signal(s) detected, not generic "this seems handoff-ready" language. The offer is more useful when the user can confirm or push back against specific observations.

**Anti-triggers (suppress Mode 2 even when signals present):** early exploration phases (open spec, debating approach, "thinking out loud"), different mode entirely (audit, research, retrospective), just-failed run remediation, casual conversation without a specific work item in scope, user mid-thought (defer to natural pause).

For per-signal rationale, the cluster-of-two rule's reasoning, the full 5-category anti-trigger taxonomy, re-offer discipline, and deployment calibration heuristics, see `references/sensing-triggers-detailed.md`.

---

## The 7 Conditions

Each condition evaluates to a pass/fail with evidence. The profile's threshold determines how many must pass for an overall PASS verdict.

### 1. Spec Stability

The work's specification is settled. Requirements are not still being explored, debated, or expanded mid-conversation.

**Pass evidence:** A written spec exists; the last spec change was at least one milestone ago; no open spec questions remain unanswered in the conversation.

**Common fail modes:** "We're still figuring out X," open requirements questions, spec changes within the current design turn, scope expansion proposed but undecided.

### 2. Verification Surface Exists

There is a measurable way to detect whether the autonomous output is correct. Without this, autonomous execution just shifts manual verification to *after* the fact, saving no time.

**Pass evidence:** Tests exist (unit, integration, e2e — appropriate to the work) AND/OR explicit verification gates are defined (audit checks, ship criteria, halt triggers). Verification is automated, not visual inspection-only.

**Common fail modes:** "We'll see if it looks right," no test backstop, ship criteria are vague aspirations, only verification surface is human review.

### 3. Invariants Written Down

The things that must never change are explicitly documented. Without explicit invariants, autonomous evolution drifts.

**Pass evidence:** An "authority matrix" or equivalent exists naming what content/code/data the agent must NOT modify; halt-and-escalate conditions are documented; the agent has access to these documents at execution time.

**Common fail modes:** Invariants exist only in the human's head, no halt triggers defined, "the agent should know not to break things."

### 4. Pump-Primer Instance Done

At least one complete instance has shipped clean against the engine/methodology, by the human or by the agent under tight human supervision. The first instance proves the engine; everything after is execution.

**Pass evidence:** One unit shipped end-to-end with all verification gates passed; the engine/methodology used is the same one the agent will use for the rest.

**Common fail modes:** "We'll figure out the engine as we go," the first instance is partially done, the engine has been changed since the pump-primer shipped (re-verify required).

### 5. Work Decomposes Into Independent Units

The remaining work breaks into N similar instances or independent units that don't depend sequentially on each other. Autonomous execution is leverage exactly when this is true.

**Pass evidence:** Remaining work is enumerated as a list of independent units; units do not require coordinated output (one unit's output is not another unit's input); the orchestrator can execute units in any order or in parallel.

**Common fail modes:** Sequential chain where each step needs the prior step's output, work that requires coordinated decisions across units, "let the agent figure out the order."

### 6. Rollback Cost Is Tolerable

If the autonomous output is bad, the cost of undoing it is bounded and acceptable. Higher rollback costs require tighter surfacing frequency or higher pass thresholds.

**Pass evidence:** Output is to a system with version control or staging (git, draft mode, sandbox); affected systems can absorb a bad output without external impact (no public deploys, no client-visible artifacts, no irreversible API calls); profile threshold is calibrated to rollback cost.

**Common fail modes:** Output goes to production with no rollback path, output triggers external side effects (emails sent, payments processed, public posts made), undo requires manual data restoration.

### 7. Token/Usage Budget Headroom

Estimated tokens (or other usage units — API calls, compute hours, runtime minutes) for the planned run fit within the remaining budget for the relevant window, with the profile's safety margin applied. Overrunning budget mid-execution leaves work half-finished.

**Pass evidence:** Estimated tokens for the run × profile safety margin ≤ remaining budget in the window; the budget data source is named (telemetry feed, manual input, registry); deterministic steps offloaded to non-LLM executors (workflow engines, scheduled tasks, external compute, formula-based logic) where appropriate to reduce token spend.

**Common fail modes:** No budget estimate, no telemetry, "we'll just run it and see," LLM doing work that a deterministic execution surface could handle for free.

---

## Workflow

This section describes Mode 1's mechanical workflow. Modes 2 and 3 wrap this workflow with input-gathering before Step 1 and conversational framing on Step 5; the evaluation logic in Steps 2-4 is identical across all three modes.

When invoked:

**Step 1 — Receive inputs.** The Skill expects three inputs:
- `profile`: A profile config object (see schema/profile.schema.json). Names the pass threshold per condition, safety margins, and budget data source.
- `work_context`: The work being evaluated. Includes a brief description, links/references to the spec, verification surface, invariants doc, pump-primer evidence, decomposed unit list, rollback assessment, and budget data.
- `optional: verbose`: When true, return per-condition reasoning in the human-readable summary. Default false.

**Step 2 — Evaluate each of the 7 conditions.** For each condition, examine the provided evidence against the condition's pass criteria. Mark `pass: true` or `pass: false`. Capture concrete `evidence` (what was checked) and `blockers` (what's missing if failed). Do not speculate; if evidence is not provided, mark the condition `pass: false` with blocker `evidence_not_provided`.

**Step 3 — Apply profile threshold.** Compare the per-condition pass count to the profile's threshold rules. Profile may require:
- ALL conditions pass (strictest, e.g., autonomous overnight runs)
- A minimum count pass (e.g., 5 of 7 with specific conditions named as required)
- Specific conditions weighted differently (e.g., conditions 3 and 7 always required regardless of others)

The profile's threshold rules are authoritative. The Skill does not override them.

**Step 4 — Generate verdict.** Produce structured JSON output (see Output Format below). Include the overall verdict (PASS / FAIL), per-condition results, profile applied, and concrete next-step recommendations for any failed conditions.

**Step 5 — Return.** Output the JSON. If `verbose: true` (Mode 1) or in Modes 2 or 3, follow with a human-readable summary explaining the verdict and naming the most important blockers.

---

## Output Format

Always return a JSON object matching this structure:

```json
{
  "verdict": "PASS | FAIL",
  "profile_applied": "profile-name-from-input",
  "checked_at": "ISO-8601 timestamp",
  "invocation_mode": "deliberate | proactive | walkthrough",
  "conditions": {
    "spec_stability": {
      "pass": true,
      "evidence": "Spec finalized 2026-04-15; no changes since; no open questions in conversation.",
      "blockers": []
    },
    "verification_surface": {
      "pass": true,
      "evidence": "pytest suite (49 cases, 0.24s runtime); halt triggers in CLAUDE.md §19.2.",
      "blockers": []
    },
    "invariants_documented": { "pass": true, "evidence": "...", "blockers": [] },
    "pump_primer_done": { "pass": true, "evidence": "...", "blockers": [] },
    "work_decomposes": { "pass": true, "evidence": "...", "blockers": [] },
    "rollback_tolerable": { "pass": true, "evidence": "...", "blockers": [] },
    "budget_headroom": {
      "pass": false,
      "evidence": "Estimated 850k tokens; remaining daily budget 600k; 1.4x over limit.",
      "blockers": ["budget_exceeded", "no_offload_to_deterministic_surface_attempted"]
    }
  },
  "threshold_rule": "all_must_pass",
  "blockers_summary": ["budget_headroom"],
  "recommended_next_steps": [
    "Reduce token estimate by offloading deterministic steps to non-LLM executor.",
    "Defer run to next budget window (resets in N hours).",
    "Narrow scope: split into two runs of ~425k tokens each."
  ]
}
```

When the verdict is PASS, `blockers_summary` is an empty array and `recommended_next_steps` is a single entry: `"Hand off to execution."`

The `invocation_mode` field is new in v1.1 and identifies which mode produced the verdict. Mode 1 callers parsing v1.0-shaped JSON can ignore the field; it is additive.

---

## Examples

Five worked examples covering all three invocation modes — Mode 1 (strict profile pass; balanced profile blocked on verification; lenient profile budget tight), Mode 2 (proactive sensing fires during design conversation), and Mode 3 (conversational walkthrough on novel work) — are in `references/examples.md`. Consult that file when modeling a new use case against an existing pattern, or when authoring a profile and wanting to see how an existing profile evaluates real evidence.

---

## Profile Configuration

The Skill expects a profile config conforming to the schema in `schema/profile.schema.json`. Minimum profile structure:

```json
{
  "name": "profile-name",
  "description": "When this profile applies",
  "threshold_rule": "all_must_pass | min_count | weighted",
  "min_pass_count": 7,
  "required_conditions": ["budget_headroom", "invariants_documented"],
  "budget_safety_margin": 1.3,
  "budget_data_source": "telemetry_feed_url | manual_input | registry_path"
}
```

Three example profiles ship with this Skill (`profiles/strict.json`, `profiles/balanced.json`, `profiles/lenient.json`) as a starting reference. Users should author their own profiles via `rootnode-profile-builder` (if available) for their specific availability patterns and risk tolerance, or by hand-editing JSON against `schema/profile.schema.json`.

---

## When to Use This Skill

Use this Skill when:
- A design conversation reaches a milestone where the next move could be either "more design" or "hand off to execution"
- Planning an autonomous overnight or unattended run of any agent runtime (Claude Code, n8n, OpenClaw, etc.)
- Designing a Claude Code deployment plan and need to know the chat→Code handoff point
- Reviewing whether a previously-deferred handoff is now ready
- Building a meta-orchestrator that needs to gate autonomous execution decisions
- Participating in an extended design conversation in which signals listed under "Proactive Sensing Triggers" emerge (Mode 2)
- The user explicitly wants to discuss readiness rather than just receive a verdict (Mode 3)

Do NOT use this Skill when:
- Evaluating already-completed autonomous work (that is verification, not handoff readiness)
- Choosing between candidate runtimes (e.g., "should I use Claude Code or n8n for this?" — that is runtime selection, not handoff readiness)
- Evaluating prompt quality (use prompt validation Skills if available)
- Auditing an existing CC project's CLAUDE.md (use project audit Skills if available)
- Doing initial scoping of a project (this Skill assumes design has progressed far enough that handoff is plausibly imminent)

### Selecting between modes

| Situation | Recommended mode |
|---|---|
| Orchestrator / scheduled job / programmatic caller has structured `work_context` ready | Mode 1 |
| User has done the prep and wants the verdict without ceremony | Mode 1 |
| User is mid-design and Claude detects handoff signals | Mode 2 (offer; user accepts → either Mode 1 with conversation-gathered context or Mode 3) |
| User explicitly asks to talk through readiness | Mode 3 |
| User new to the Skill on this class of work | Mode 3 |
| Evidence is uncertain and a walk-through is what generates it | Mode 3 |

---

## Troubleshooting

Common failure modes and resolution guidance — covering verdict-related issues (FAIL on every check, PASS but autonomous run failed, profile/condition conflicts), Mode 2 sensing issues (firing too often, firing too rarely, re-offer behavior after decline), Mode 3 walkthrough issues (drag, vague evidence), profile authoring issues (no fitting standard profile, no budget telemetry), and evidence capture issues — are in `references/troubleshooting.md`. Consult that file when the gate's behavior in production doesn't match expectations or when calibrating Mode 2 sensing for a deployment.
