# Worked Examples

Five end-to-end examples of the handoff-gate in action across all three invocation modes. Use this when you need to see how `work_context` translates to a verdict in practice, or when modeling a new use case against an existing pattern.

**When to consult this file:** When the SKILL.md "Examples" section's stub points here for the full conversational scaffolding, when authoring a profile or test case and you want to see how an existing profile evaluates real evidence, or when a user asks "show me what this looks like in practice."

---

## Table of Contents

1. [Example 1 — Mode 1 — Strict profile, all 7 pass](#example-1--mode-1--strict-profile-all-7-pass)
2. [Example 2 — Mode 1 — Balanced profile, blocked on verification surface](#example-2--mode-1--balanced-profile-blocked-on-verification-surface)
3. [Example 3 — Mode 1 — Lenient profile, budget tight](#example-3--mode-1--lenient-profile-budget-tight)
4. [Example 4 — Mode 2 — Proactive sensing fires during a design conversation](#example-4--mode-2--proactive-sensing-fires-during-a-design-conversation)
5. [Example 5 — Mode 3 — Conversational walkthrough on novel work](#example-5--mode-3--conversational-walkthrough-on-novel-work)

---

## Example 1 — Mode 1 — Strict profile, all 7 pass

A canonical "ready to hand off" case. Used by orchestrators that have built up `work_context` from prior workflow steps and now need a parseable go/no-go verdict.

**Input:**

- **Profile:** `strict` (threshold: all 7 must pass; safety margin 1.3x on budget)
- **Work context:** Ship 5 remaining instances of pattern X. Spec finalized last week, pytest suite green (62 cases), invariants in `CLAUDE.md` authority matrix, instance #1 shipped clean Tuesday, remaining 5 are independent, output goes to git branch (revert trivially), token estimate 320k against 800k remaining daily budget.

**Output:**

```json
{
  "verdict": "PASS",
  "profile_applied": "strict",
  "invocation_mode": "deliberate",
  "conditions": {
    "spec_stability":        { "pass": true, "evidence": "Spec finalized 2026-04-22; no changes since.", "blockers": [] },
    "verification_surface":  { "pass": true, "evidence": "pytest suite (62 cases, all green).", "blockers": [] },
    "invariants_documented": { "pass": true, "evidence": "CLAUDE.md authority matrix intact.", "blockers": [] },
    "pump_primer_done":      { "pass": true, "evidence": "Instance #1 shipped Tuesday with all gates clean.", "blockers": [] },
    "work_decomposes":       { "pass": true, "evidence": "5 remaining units, no inter-dependencies.", "blockers": [] },
    "rollback_tolerable":    { "pass": true, "evidence": "Output to git branch; trivial revert.", "blockers": [] },
    "budget_headroom":       { "pass": true, "evidence": "320k × 1.3 safety = 416k; 800k remaining; headroom 1.92x.", "blockers": [] }
  },
  "threshold_rule": "all_must_pass",
  "blockers_summary": [],
  "recommended_next_steps": ["Hand off to execution."]
}
```

The orchestrator parses `verdict: "PASS"` and triggers the autonomous run. No human round-trip needed.

---

## Example 2 — Mode 1 — Balanced profile, blocked on verification surface

A common "almost ready, but the verification gap is doing the work" case. The Skill catches the gap that the user might have rationalized past in a vibes-based handoff decision.

**Input:**

- **Profile:** `balanced` (threshold: 6 of 7, conditions 3 and 7 required)
- **Work context:** Build feature Y. Spec stable. No automated tests; planned verification is human review of the output. Invariants documented. No pump-primer yet — this is the first instance. Work is one unit, not decomposable. Output to staging branch. Token estimate fits budget.

**Output:**

```json
{
  "verdict": "FAIL",
  "profile_applied": "balanced",
  "invocation_mode": "deliberate",
  "conditions": {
    "spec_stability":        { "pass": true, "evidence": "Spec stable.", "blockers": [] },
    "verification_surface":  { "pass": false, "evidence": "Human review only.", "blockers": ["no_automated_verification"] },
    "invariants_documented": { "pass": true, "evidence": "Invariants documented.", "blockers": [] },
    "pump_primer_done":      { "pass": false, "evidence": "First instance.", "blockers": ["no_pump_primer"] },
    "work_decomposes":       { "pass": false, "evidence": "Single unit.", "blockers": ["work_is_atomic"] },
    "rollback_tolerable":    { "pass": true, "evidence": "Staging branch.", "blockers": [] },
    "budget_headroom":       { "pass": true, "evidence": "Within budget.", "blockers": [] }
  },
  "threshold_rule": "min_count: 6 of 7, required: [3, 7]",
  "blockers_summary": ["verification_surface", "pump_primer_done", "work_decomposes"],
  "recommended_next_steps": [
    "Define an automated verification check before handoff (test, audit script, or output validator).",
    "Complete the first instance under human supervision; use it as the pump-primer for any future instances.",
    "If this is genuinely a one-off (no future instances), reconsider whether autonomous handoff adds value vs. real-time pairing."
  ]
}
```

Required conditions 3 (invariants) and 7 (budget) both pass, but the overall 6-of-7 threshold fails (only 4 pass). The Skill names exactly which gaps to address before re-checking.

---

## Example 3 — Mode 1 — Lenient profile, budget tight

A near-miss that's still a fail. Demonstrates that token budget is treated as a hard precondition, not a soft preference, even on lenient profiles.

**Input:**

- **Profile:** `lenient` (threshold: 5 of 7; safety margin 1.1x on budget — corrections available in real time)
- **Work context:** Refactor module Z. Spec stable. Tests exist. Invariants documented. Module already partially refactored in similar pattern (counts as pump-primer). Files are independent. Rollback via git. Token estimate 580k against 600k remaining; with 1.1x safety margin = 638k > 600k budget.

**Output:**

```json
{
  "verdict": "FAIL",
  "profile_applied": "lenient",
  "invocation_mode": "deliberate",
  "conditions": {
    "spec_stability":        { "pass": true, "evidence": "Spec stable.", "blockers": [] },
    "verification_surface":  { "pass": true, "evidence": "Tests exist.", "blockers": [] },
    "invariants_documented": { "pass": true, "evidence": "Invariants documented.", "blockers": [] },
    "pump_primer_done":      { "pass": true, "evidence": "Prior partial refactor in same pattern.", "blockers": [] },
    "work_decomposes":       { "pass": true, "evidence": "Files independent.", "blockers": [] },
    "rollback_tolerable":    { "pass": true, "evidence": "Git rollback.", "blockers": [] },
    "budget_headroom":       { "pass": false, "evidence": "580k × 1.1 = 638k; 600k remaining; over by 38k.", "blockers": ["budget_exceeded_after_safety_margin"] }
  },
  "threshold_rule": "min_count: 5 of 7, required: [7]",
  "blockers_summary": ["budget_headroom"],
  "recommended_next_steps": [
    "Defer run by ~3 hours until budget window refresh.",
    "OR proceed at risk: 6 of 7 conditions pass, but condition 7 is explicitly required by 'lenient' profile threshold.",
    "OR offload one independent file's refactor to a deterministic transform if pattern is mechanical."
  ]
}
```

Six of seven pass, but condition 7 is explicitly required by the profile's threshold rule. The Skill returns FAIL even though the lenient profile's `min_count` of 5 is exceeded — because `required_conditions` overrides count thresholds when a required condition fails.

---

## Example 4 — Mode 2 — Proactive sensing fires during a design conversation

A design conversation reaches handoff readiness without the user explicitly asking. Mode 2 surfaces the readiness moment rather than waiting to be invoked.

**Conversational context:** User and Claude have spent ~40 minutes in a Project design session scoping a vendor-code data cleanup. Spec is settled, the verification surface is named (existing validation suite), invariants are documented (no schema changes). User just said: "and we need to do this for the other 12 vendor codes too."

**Signals detected:** Decomposition language ("12 more like this") + extended design mode with concrete spec + pump-primer language (the first cleanup is described as already done). Three concurrent signals — well above the cluster-of-2 threshold.

**Claude offers:**

> I'm noticing the conversation has just named 12 more vendor codes that need the same treatment, and the first one is already done. The handoff-gate Skill is the formal mechanism for evaluating whether this is ready to hand off to autonomous Claude Code. Want me to run it now? I can gather the evidence from our conversation, or walk through the 7 conditions with you one at a time.

**User:** "Yes — gather it from the conversation."

**Claude gathers `work_context` from the session, runs Mode 1 mechanics, returns:**

```json
{
  "verdict": "PASS",
  "profile_applied": "balanced",
  "invocation_mode": "proactive",
  "conditions": {
    "spec_stability":        { "pass": true, "evidence": "Cleanup spec stable since beginning of session.", "blockers": [] },
    "verification_surface":  { "pass": true, "evidence": "Existing validation suite (named in conversation 12 turns ago).", "blockers": [] },
    "invariants_documented": { "pass": true, "evidence": "No schema changes — invariant respected by design.", "blockers": [] },
    "pump_primer_done":      { "pass": true, "evidence": "First vendor code cleanup completed, named in conversation.", "blockers": [] },
    "work_decomposes":       { "pass": true, "evidence": "12 vendor codes are independent units.", "blockers": [] },
    "rollback_tolerable":    { "pass": true, "evidence": "Git branch with staging review.", "blockers": [] },
    "budget_headroom":       { "pass": true, "evidence": "Estimated 12 × 30k = 360k; 800k remaining; headroom 2.2x.", "blockers": [] }
  },
  "threshold_rule": "min_count: 6 of 7",
  "blockers_summary": [],
  "recommended_next_steps": ["Hand off to execution."]
}
```

**Plus framing:**

> All 7 pass against the balanced profile. The 12 vendor codes are independent, the validation suite catches the failure modes we discussed, and the rollback path is the existing git branch. Recommended next step: hand off to Claude Code with the work plan we just built.

The Mode 2 offer surfaced the readiness moment before the user thought to ask. The verdict is the same as Mode 1 would produce; the difference is that without Mode 2, the work would have lingered in design until the user remembered to invoke the gate manually.

---

## Example 5 — Mode 3 — Conversational walkthrough on novel work

User explicitly requests a walkthrough — typically because the work is unfamiliar enough that they want to understand each condition before receiving the verdict.

**Conversational context:** User is rebuilding a habit-tracker app and wants to evaluate handoff readiness explicitly.

**User:** "Let's walk through whether the tracker rebuild is ready to hand off."

**Claude:**

> Sure. There are 7 conditions. I'll walk them one at a time. First — **Spec Stability.** Is the spec for the rebuild settled, or are there still open requirements questions?

**User:** "Spec is settled — we agreed the schema last week and the prompt cards are locked."

**Claude:**

> Good. Marking spec_stability as PASS. Next — **Verification Surface.** Is there a measurable way to detect whether the autonomous output is correct?

**User:** "I'd just look at it."

**Claude:**

> That's a fail on this condition — visual review only doesn't catch silent regressions. Marking it FAIL with blocker `no_automated_verification`. Continuing — **Invariants Written Down.** Are there things that must NOT change documented somewhere the agent can read?

**User:** "Yes, the schema is locked and I have an authority section in CLAUDE.md."

**Claude:**

> PASS on invariants_documented. Fourth — **Pump-Primer Instance Done.** Has at least one tracker been shipped clean against the new engine?

**User:** "Not yet — I was going to start fresh with the agent."

**Claude:**

> That's a FAIL on pump_primer_done. The first instance is what proves the engine; without it, the agent is debugging the engine and producing output simultaneously, which goes badly. Continuing — **Work Decomposes.** Are the remaining trackers independent of each other?

[walkthrough continues through conditions 5, 6, 7]

**After all 7:**

```json
{
  "verdict": "FAIL",
  "profile_applied": "strict",
  "invocation_mode": "walkthrough",
  "conditions": {
    "spec_stability":        { "pass": true, "evidence": "Schema agreed last week, prompt cards locked.", "blockers": [] },
    "verification_surface":  { "pass": false, "evidence": "Visual review only.", "blockers": ["no_automated_verification"] },
    "invariants_documented": { "pass": true, "evidence": "Schema locked; authority section in CLAUDE.md.", "blockers": [] },
    "pump_primer_done":      { "pass": false, "evidence": "Planned to start fresh with agent.", "blockers": ["no_pump_primer"] },
    "work_decomposes":       { "pass": true, "evidence": "Trackers independent.", "blockers": [] },
    "rollback_tolerable":    { "pass": true, "evidence": "Git rollback available.", "blockers": [] },
    "budget_headroom":       { "pass": true, "evidence": "Estimate 200k against 700k remaining.", "blockers": [] }
  },
  "threshold_rule": "all_must_pass",
  "blockers_summary": ["pump_primer_done", "verification_surface"],
  "recommended_next_steps": [
    "Ship one tracker manually end-to-end as the pump-primer.",
    "Add a JSON-shape check the orchestrator can use as the verification gate.",
    "Re-run this check once the two land — the other five conditions are already passing."
  ]
}
```

**Plus conversational summary:**

> The verdict is FAIL on the strict profile. Two conditions are blocking: pump-primer hasn't shipped (you described this as "I'd just start fresh"), and verification surface is informal (visual review only). Recommended next steps: ship one tracker manually end-to-end as the pump-primer; add a JSON-shape check the orchestrator can use as the verification gate. Once those two land, re-run this check — the other five conditions are already passing.

The walkthrough generated the evidence as it went. By the end, the user has both a JSON verdict (parseable, loggable) and a clear understanding of *why* the verdict reads the way it does. That understanding is what Mode 3 buys over Mode 1.
