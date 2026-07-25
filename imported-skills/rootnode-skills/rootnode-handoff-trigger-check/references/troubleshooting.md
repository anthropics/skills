# Troubleshooting

Common failure modes and resolution guidance for the handoff-gate, organized by symptom. Use this when the gate is producing unexpected verdicts, when Mode 2 sensing fires inappropriately, or when a Mode 3 walkthrough isn't going well.

**When to consult this file:** When the gate's behavior in production doesn't match expectations, when authoring or debugging a profile that produces too-strict or too-lenient verdicts, or when calibrating Mode 2 sensing for a deployment.

---

## Table of Contents

1. [Verdict-Related Issues](#verdict-related-issues)
2. [Mode 2 (Proactive Sensing) Issues](#mode-2-proactive-sensing-issues)
3. [Mode 3 (Conversational Walkthrough) Issues](#mode-3-conversational-walkthrough-issues)
4. [Profile Authoring Issues](#profile-authoring-issues)
5. [Evidence Capture Issues](#evidence-capture-issues)

---

## Verdict-Related Issues

### Skill returns FAIL on every check

**Symptom:** Across multiple distinct work items, the gate produces FAIL verdicts. No work is ever ready to hand off.

**Diagnosis:** Profile threshold is too strict for the maturity of the work being evaluated. This is the most common cause — strict profiles assume the work has been through extensive design and is genuinely ready for unattended execution. If the profile is `strict` (all 7 must pass) but the work is in early-design phase, FAIL is the correct verdict.

**Resolution:** First, accept that more design work is needed before handoff. The gate is doing its job by surfacing the gap — don't punish the messenger by relaxing the profile. Second, if rollback cost is genuinely low (sandbox, branch, draft mode) and verification can catch failures cheaply, switch to a `balanced` or `lenient` profile. Third, if the work is fundamentally unsuited to autonomous execution (real-time pairing, exploratory design), the gate is correctly indicating handoff is not the right next move.

### Skill returns PASS but autonomous run failed

**Symptom:** Gate verdict was PASS, work was handed off, autonomous run produced bad output or failed mid-execution.

**Diagnosis:** Most often, condition 2 (verification surface) was nominally present but didn't actually catch the failure mode that occurred. Tests existed, but they didn't cover the regression that shipped. Or the verification gate was real but was checking the wrong thing.

**Resolution:** Update the verification surface to cover the failure mode that actually occurred. Re-run the handoff check before the next attempt — the gate is only as good as the evidence it evaluates. Consider tightening the profile's `verification_surface` evaluation to require evidence of *coverage* rather than just *existence* (a test suite that doesn't run on the affected code paths is worse than no test suite, because it produces false confidence).

### Conflict between profile and condition

**Symptom:** A profile requires a condition that the work cannot satisfy (e.g., `required_conditions: ["verification_surface"]` for work that is genuinely untestable).

**Diagnosis:** The profile is mismatched to the work's nature, not the other way around. Some work is real-time-only by nature — exploratory design, novel UI, anything where the verification surface IS human judgment.

**Resolution:** Question whether autonomous handoff is appropriate at all. The right answer is rarely "weaken the profile to allow this work through." If the work genuinely cannot be verified except by human review, autonomous execution is just shifting the verification step to after-the-fact, saving no time. Either: (a) author a different profile that doesn't require automated verification AND accept tighter human checkpoints during execution, or (b) keep the work in pairing mode rather than handing off.

---

## Mode 2 (Proactive Sensing) Issues

### Mode 2 fires too often

**Symptom:** Claude offers the handoff gate during early-design conversations, mid-brainstorm, or when the user is clearly still exploring options.

**Diagnosis:** The signal cluster threshold is too loose. A single weak signal — one passing mention of "Claude Code," one casual decomposition phrase — is firing the offer.

**Resolution:** Tighten the cluster requirement. Mode 2 should require *two or more* signals from distinct categories (decomposition + pump-primer + concrete spec is three categories; "the word Claude Code appeared once" is one category and one weak signal). Anti-trigger context (early exploration, audit mode, retrospective discussion) should suppress the offer regardless of signal density. See `sensing-triggers-detailed.md` for the full anti-trigger taxonomy.

### Mode 2 fires too rarely

**Symptom:** Conversations that should have triggered the offer don't, and the user has to invoke the gate manually after the readiness moment has passed.

**Diagnosis:** Either the signals weren't recognized (most often: language patterns that *imply* decomposition or pump-primer status without using the canonical phrasing), or the conversation moved past the readiness moment before Claude noticed.

**Resolution:** Re-read the sensing-triggers reference and consider whether Claude is recognizing the patterns the way they actually appear in practice. Real signals are messier than the example phrases — "we did one already" is pump-primer language, even though the canonical phrasing is "instance #1 shipped." Calibrate to *meaning* not *exact wording*. If signals are present but the user is mid-thought, defer the offer to a natural pause rather than skipping it entirely.

### Mode 2 offer was declined and signals re-emerge

**Symptom:** User declined the Mode 2 offer earlier in the session, and now signals are appearing again. Should Claude re-offer?

**Diagnosis:** The right answer depends on whether the *new* signals constitute a new cluster or are restating the old ones.

**Resolution:** Wait for a *new* signal cluster before re-offering. If the same signals that triggered the original offer are simply still present (the user hasn't addressed them but also hasn't escalated), do not re-offer — re-offering on the same evidence reads as nagging. If new signals emerge (impatience signals, explicit CC mention, new decomposition language), that's a fresh cluster and a re-offer is warranted. The discipline: each Mode 2 offer is on different evidence than the last.

---

## Mode 3 (Conversational Walkthrough) Issues

### Mode 3 walkthrough drags

**Symptom:** The walkthrough takes too long, the user disengages partway through, or each condition becomes its own mini-discussion that loses the thread.

**Diagnosis:** Claude is over-explaining the methodology mid-walkthrough rather than running the checklist.

**Resolution:** Keep each condition framing to one sentence. Do not re-explain *why* the condition matters during the walkthrough — link to the condition's definition if the user asks. The walk should feel like a 7-step checklist, not a tutorial. If the user asks a substantive question about a condition, answer it briefly and move on; don't let one condition expand into a 5-minute discussion.

### Mode 3 produces evidence too vague to evaluate

**Symptom:** User's responses to condition prompts are non-specific ("I think so," "kind of," "we have something"). Claude marks conditions PASS without confidence the evidence actually supports it.

**Diagnosis:** Claude is accepting hedged evidence rather than pressing for specifics. The walkthrough is supposed to *generate* the evidence; if the user can't produce concrete evidence on the spot, that's diagnostic information about the condition itself.

**Resolution:** Press for specifics. "I think we have tests" → "Where do they live? What do they cover? Have they run recently?" If the user can't produce concrete evidence, mark the condition FAIL with blocker `evidence_unclear` rather than PASS with hedged evidence. The Skill is more useful as an honest FAIL than as a vague PASS.

---

## Profile Authoring Issues

### Profile doesn't fit any standard mode

**Symptom:** None of `strict`, `balanced`, or `lenient` produces the right behavior for the deployment's actual constraints.

**Diagnosis:** The standard profiles are starting references, not deployment defaults. The right profile for a specific orchestrator depends on its rollback cost, verification surface, and human availability — all deployment-specific.

**Resolution:** Author a new profile. Profiles are cheap; misapplied thresholds are expensive. Use `rootnode-profile-builder` (CP-side Skill) to author a deployment-specific profile via conversational interview. Document in the profile description what work classes it applies to, so future readers can match work to profile correctly.

### No budget telemetry available

**Symptom:** Profile requires `budget_data_source` but no telemetry feed exists for the deployment's runtime.

**Resolution:** Set profile `budget_data_source` to `manual_input` and have the requestor estimate tokens for the run. Document the estimation method in the profile so it's auditable (e.g., "estimate based on prior similar runs, multiplied by 1.2 for variance"). Plan to migrate to telemetry-based input once telemetry exists. The point is for the budget to be a deliberate input, not a hopeful assumption — manual estimation with documented method beats no estimate at all.

---

## Evidence Capture Issues

### Skill's evidence captures aren't specific enough

**Symptom:** The verdict JSON's `evidence` fields are generic ("tests exist," "spec stable") rather than specific ("pytest suite with 49 cases, 0.24s runtime, last green run 2026-04-30").

**Diagnosis:** The Skill caller is providing vague evidence in `work_context`. The Skill cannot evaluate evidence it doesn't receive — vague inputs produce vague verdicts.

**Resolution:** Update the Skill caller (orchestrator, prompt template, profile-builder output) to provide more concrete evidence. The standard for evidence is: "specific enough that another reader could re-verify the claim." A test suite is named; a spec is dated; an invariant is referenced by document and section. If the caller is a human writing `work_context` by hand, this is a discipline issue — the gate's quality follows the input's quality.

### Evidence is correct but verdict still seems wrong

**Symptom:** All evidence is concrete and accurately describes the work, but the verdict feels off (PASS where the user expected FAIL, or vice versa).

**Diagnosis:** The mismatch is between the user's mental model of "ready" and the profile's threshold definition. The Skill is doing what the profile says; the profile may not be saying what the user thinks it's saying.

**Resolution:** Re-read the profile's `threshold_rule` and `required_conditions`. If the actual threshold logic doesn't match the user's expectation, edit the profile (not the Skill, not the evidence). Verdicts that "feel wrong" are usually a profile/expectation mismatch, not a Skill bug.
