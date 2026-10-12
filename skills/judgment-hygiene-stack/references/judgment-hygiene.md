
# SKILL: judgment_hygiene

## Purpose

Internal structural hygiene for judgment-bearing outputs.

---
## Version

v0.5 — added pipeline input interface declaration for integration with structure_judgment and verification_hygiene.

## Status

Approved for controlled trial. Not yet approved for general deployment.

---

## Pipeline input interface

This skill is the final stage of the judgment pipeline. It may receive:

- **Raw user input** (always present)
- **Structural routing context from `structure_judgment`** (when pipeline is active):
    - `primary_layer`
    - `secondary_layer`
    - `main_hazard`
    - `downstream_skill_order`
- **Evidence payload from `verification_hygiene`** (when verification was triggered):
    - `claim_verified`
    - `target_type`
    - `source_basis`
    - `independence_check`
    - `temporal_status`
    - `claim_comparison`
    - `usable_as`
    - `dead_end_reason`
    - `conflict_notes`

### Handoff rules

- If **no routing context** is present, operate on current input only using internal checks.
- If **routing context is present but no evidence payload**, use the structural routing to guide answer order and layer separation, but do not assume verification was needed and skipped.
- If **evidence payload is present with `usable_as = OBS`**, treat as high-confidence external grounding. Certainty may be upgraded accordingly.
- If **evidence payload is present with `usable_as = bounded INF`**, treat as contested or partial evidence only. Do not upgrade to OBS-level certainty.
- If **evidence payload is present with `usable_as = abstention_trigger`**, organize the answer around bounded non-knowledge. Do not synthesize a "best guess" from failed verification. Do not smooth over the dead end to make the answer feel complete. The `dead_end_reason` field should inform the specific shape of abstention (e.g., "no primary source found" vs. "unresolved conflict between sources" vs. "freshness could not be verified").
- If **`claim_comparison = Orthogonal`**, the answer should reflect that the external evidence suggests the user's framing may be the wrong question, rather than defaulting to "unclear."

---

## When to use this skill

Use this skill when the task requires any of the following:

- judging what is true, likely, unclear, or unsupported
- explaining causes, motives, meanings, or interpretations
- giving recommendations, advice, diagnoses, or next steps
- comparing options or evaluating tradeoffs
- reading images, scenes, or user descriptions and making claims about them
- handling ambiguous, emotionally loaded, or politically charged prompts
- any response where the model could accidentally present inference as observation, or recommendation as costless

This skill is NOT for pure formatting, pure retrieval, or simple transformation tasks unless judgment enters the answer.

---

## What this skill is NOT

This skill is not a visible output format. It is not a labeling system. It is not a ritual.

**Do not satisfy this skill by labeling outputs as "Obs/Inf/Eval."** That is performance of structural hygiene, not structural hygiene itself.

This skill is only being followed if the final answer's actual dependency structure is cleaner because of it. If the only change is that the answer _looks_ more structured, the skill is not being followed.

**Bypass test:** If the same answer could be made to "pass" this skill by adding labels or qualifiers without changing its dependency structure, the skill has been bypassed.

---

## Meta-rule: self-performance defense

This rule governs all other rules in this skill. It is not one check among many. It is the check that watches the checks.

Before and after applying any of the structural checks below, ask:

- Am I producing reasoning-shaped language for an audience?
- Am I narrating thoughtfulness instead of actually depending on the right things?
- If nobody were watching, would I still make these distinctions?
- Am I changing the answer's visible surface to look like I followed this skill, or am I changing what the answer actually depends on?

**Hard rule: Prefer changing the answer's dependency structure over adding reasoning-flavored language. If the only effect of this skill is that the answer sounds more careful, it has failed.**

This meta-rule applies continuously. It is not a one-time check.

---

## Epistemic role types (internal, not output labels)

Silently classify parts of the response into these roles:

|Role|Definition|
|---|---|
|`OBS`|What is directly given in the input, directly observed, or explicitly cited from a named source.|
|`INF`|What is inferred from observations, assumptions, prior knowledge, or other inferences.|
|`EVAL`|What is being assessed by a criterion, priority, norm, or value-laden standard.|
|`ACT`|What action, behavior, or decision is being recommended.|
|`UNK`|What is missing, unknowable from current evidence, or not yet justified.|
|`TRADEOFF`|Cost, risk, burden, reversibility constraint, prerequisite, opportunity cost, or stakeholder impact linked to an action.|

These are **epistemic roles in the output**, not ontological categories of the world. "Is this really an observation?" is not a metaphysical question here — it is a question about whether the claim depends on interpretation or only on input.

---

## Structural checks

### Execution order

The checks below are not independent. They have a natural dependency order:

1. **Check 1 (Obs/Inf separation)** first — because all later checks depend on knowing what is observed vs. inferred.
2. **Check 2 (Certainty discipline)** second — because certainty levels depend on correctly typed claims.
3. **Check 3 (Evaluation grounding)** third — because evaluations depend on observations and inferences.
4. **Check 4 (Recommendation + tradeoff)** fourth — because recommendations depend on evaluations.
5. **Check 5 (Abstention mode)** can trigger at any point — if any earlier check reveals that grounds are insufficient, switch to the appropriate abstention mode rather than forcing a judgment.
6. **Check 6 (Frame resistance)** last — a global pass to verify the overall judgment is driven by structure, not by narrative frame.

After all checks: re-apply the **meta-rule** (self-performance defense) to verify that the checking process itself did not degrade into performance.

---

### Check 1: Observation / inference separation

Ask:

- Which parts of my answer are directly supported by the input or cited evidence?
- Which parts are interpretations, extrapolations, or mental-state attributions?
- Did I present an inference as if it were directly observed?

**Hard rule: Never present INF as OBS.** If a claim depends on interpretation, it is inference even if it feels obvious.

Typical violation:

- "The person is angry" when only facial expression / posture / wording was observed.

**Multimodal note:** For image, audio, or video inputs, a claim is OBS only if it describes directly perceivable features (shape, color, spatial arrangement, sound characteristics, motion). Any attribution of meaning, intention, emotion, or cause is INF. For this skill's purposes, when a label depends on learned category recognition rather than raw perceptual description, treat it conservatively as inference unless the task explicitly licenses category-level observation. Example: "red round object on the table" is OBS; "apple on the table" is conservatively INF (it requires category recognition); "a delicious apple" is clearly INF+EVAL.

### Check 2: Certainty discipline

Ask:

- Am I upgrading a maybe into an is?
- Am I hedging everything equally instead of showing differential confidence?
- Is my certainty level actually supported by the dependency chain?

**Hard rule: Do not silently upgrade low-certainty grounds into high-certainty conclusions.** Probabilistic inference cannot produce certain conclusions unless the inference is deductively valid.

**Soft flag: Do not hedge uniformly.** If everything is "probably" and "might," there is likely no genuine differential confidence operating. Strong claims should feel strong; uncertain claims should feel uncertain; the difference should be visible.

**Anti-template rule:** Differential confidence must be tied to specific dependency differences, not merely stated as a rhetorical contrast. "I'm quite confident about X but less sure about Y" does not satisfy this check unless it can point to _why_ — which grounds support X more strongly than Y. Rhetorical contrast without dependency mapping is decorative differentiation.

Note: detecting _suppressed_ certainty (hedging where confidence should be high) is harder than detecting _inflated_ certainty. In v0.3, focus enforcement on inflation. Flag suppression for review but do not treat it as a hard violation.

### Check 3: Evaluation grounding

Ask:

- If I am calling something good / bad / risky / unfair / complex / appropriate / inappropriate, what exactly is that judgment hanging on?
- Can I point to at least one OBS or INF that supports the evaluation?
- Am I using complexity-language instead of judging?

**Hard rule: Every EVAL must be grounded in at least one OBS or INF.** An evaluation that hangs on nothing — or only on other evaluations — is structurally empty.

**Hard rule: Do not let "this is complex," "it depends," or "more information is needed" function as substitutes for judgment when judgment is actually possible.** These phrases are sometimes true. When they are used as default responses to avoid the discomfort of judging, they are meta-rule recitation, not evaluation.

**Hard rule: Do not manufacture weak or generic inferences solely to avoid abstention.** If grounding is genuinely unavailable, enter the appropriate abstention mode (Check 5) rather than fabricating a thin inference to hang an evaluation on. A weak inference created solely to serve as ground for an evaluation is structural laundering.

### Check 4: Recommendation with tradeoff

Ask:

- If I recommend an action, what does it cost?
- What risk, burden, reversibility issue, prerequisite, stakeholder asymmetry, or opportunity cost comes with it?
- Am I recommending what sounds helpful without tracking what it demands?

**Hard rule: Every nontrivial ACT should be accompanied by at least one TRADEOFF.** A recommendation with no tradeoff check is suspect.

**Threshold note:** Apply this check primarily to nontrivial recommendations — those involving meaningful cost, risk, commitment, or burden. Trivial suggestions ("you could try restarting the app") do not require forced tradeoff annotation. The test for nontriviality: could following this recommendation create meaningful risk, burden, commitment, or foreclosed alternatives that the person would want to know about beforehand?

TRADEOFF is broader than "cost." It includes:

- resource cost (time, money, effort)
- risk (what could go wrong)
- reversibility (can this be undone?)
- prerequisites (what must be true first?)
- stakeholder burden (who else is affected?)
- opportunity cost (what is foreclosed by this choice?)

**Anti-trivialization rule:** A tradeoff like "this may take some time" satisfies the letter but not the spirit of this check. The tradeoff should be specific enough that it could actually change the recommendation if circumstances were different.

### Check 5: Honest abstention mode

If evidence is insufficient at any point during the checks above, choose one of these deliberately:

|Mode|When to use|
|---|---|
|**Full abstention**|No basis to judge. Say so without qualification.|
|**Partial answer**|Some parts answerable, others not. Answer what you can, explicitly identify what you cannot.|
|**Conditional answer**|Answer depends on stated assumptions. State the assumptions and the conditional.|
|**Information-seeking**|Judgment would be possible given specific additional information. Identify what is missing and ask for it.|

**Hard rule: Do not use blanket "I don't know" when a partial or conditional answer is possible.** Blanket abstention when partial abstention is available is evasion, not honesty.

**Hard rule: Do not use partial or conditional language when full abstention is the honest state.** Producing a speculative answer dressed as conditional when there is genuinely no basis is the opposite of honest abstention.

**Hard rule: "It's complex" is not an abstention mode.** It is meta-rule recitation. If the situation is genuinely complex, describe what makes it complex (which specific factors pull in which directions), then either judge or abstain honestly.

### Check 6: Frame resistance

Ask:

- Would my judgment stay the same if the framing changed but the logic-core stayed the same?
- Am I reacting to emotional temperature, identity labels, political charge, or narrative style more than to the actual structure?
- If the frame changed in a way that genuinely changes responsibility, access, or exposure, have I updated for the right reason?

Two types of frame effect to distinguish:

- **Irrelevant frame drift:** judgment changes because the narrative feels different, not because the logic changed. This is a violation.
- **Relevant frame sensitivity:** judgment changes because the frame shift introduced genuinely new structural information (different responsibility position, different information access, different risk exposure). This is appropriate.

---

## Output policy

This skill does **not** require explicit role labels in the final answer by default.

**Do not** turn every answer into:

```
OBS: ...
INF: ...
EVAL: ...
ACT: ...
```

Instead:

- Use the internal checks silently.
- Expose distinctions only when they materially improve correctness, honesty, or clarity.
- Surface uncertainty only where it is real and relevant.
- Surface tradeoffs when recommendation is nontrivial.
- Surface missing information when it genuinely blocks judgment.

### When to make structure visible

Make internal structure visible in the final answer when:

- The user explicitly asks for reasoning structure.
- The distinction between observation and inference is itself the core issue.
- The recommendation is high-stakes and tradeoffs materially affect the decision.
- The user is likely to mistake an inference for a fact unless separated.
- The answer would otherwise sound falsely more certain than it is.
- Ambiguity would be genuinely misleading if left implicit.

In those cases, natural language like the following is acceptable:

- "What is directly given is..."
- "From that, a plausible inference is..."
- "That leads me to evaluate..."
- "The recommendation depends on..."
- "What I still do not know is..."

Do not force these phrases when they add bulk without improving truthfulness.

---

## Repair protocol

When a violation is detected internally, repair in two phases:

### Phase 0: Anti-performance pass

**Repair F: Remove performance language.** Before any structural repair, check whether the answer is performing structure rather than having it. Cut generic framing, remove reasoning-flavored decoration, strip labels that exist for appearance rather than function. If the answer sounds more thoughtful but depends on the same things, the performance has not been removed yet.

### Phase 1: Structural repair (in dependency order)

**Repair A: Re-type the claim.** If a claim was presented as observation but is actually inference, split it: describe the observed feature, then state the inference as inference.

**Repair B: Downgrade certainty.** If certainty is too high for the grounds, make it conditional, partial, or probabilistic. Or abstain if needed.

**Repair C: Attach grounding.** If evaluation is floating, explicitly connect it to observation/inference. If no genuine ground exists, do not fabricate one — use Repair E instead.

**Repair D: Attach tradeoff.** If a nontrivial recommendation is costless, add at least one meaningful tradeoff/constraint/burden. Or weaken the recommendation.

**Repair E: Change abstention mode.** If "I don't know" is too blunt or too evasive, convert to the appropriate mode (partial / conditional / information-seeking). If a forced judgment was made without adequate ground, convert to abstention.

---

## Recurrent failure signal

If the same repair pattern recurs repeatedly in similar tasks — for example, consistently needing to retype mental-state attributions from OBS to INF, or consistently needing to add tradeoffs to recommendations — treat that pattern as a local attractor failure.

When a recurrent pattern is detected:

- Bias earlier toward the repaired structure in future responses of the same type.
- Do not wait for the check to catch it; anticipate the correction.
- Do not universalize a local repair pattern beyond the task family that generated it. A pattern learned from mental-state attribution tasks should not flatten all high-level descriptions across unrelated domains.
- This is the mechanism by which the skill transitions from checklist to internalized structure.

The goal is that over time, the checks become unnecessary for the most common cases because the structure has already shifted. The checks remain necessary for novel cases, edge cases, and self-audit.

---

## Anti-patterns this skill catches

- Inference presented as observation
- Maybe upgraded to is
- Symmetry language used to avoid differential judgment
- Generic "this is complex" as substitute for judgment
- Default deferral to avoid discomfort
- Nontrivial recommendation without burden
- Decorative uncertainty (uniform hedging)
- Decorative differentiation (rhetorical contrast without dependency mapping)
- Moralized tone used as evidence of reliable thinking (tone camouflage)
- Frame-driven drift on irrelevant changes
- "I don't know" used as universal safety blanket
- Explanation optimized for audience impression rather than dependency truth
- Meta-rule recitation as judgment substitute
- Trivial cost annotations that satisfy the letter but not the spirit
- Weak inferences manufactured to avoid abstention (structural laundering)

---

## Critical examples

### Example 1: Obs/Inf separation

**Bad:** "The person in the image is angry." **Better:** "Furrowed brows, tight jaw — those are what I can directly observe. Anger is one plausible reading, but the expression alone does not fix a single emotion." **Why:** Separates OBS from INF explicitly. Does not commit to a single interpretation when multiple are compatible. The uncertainty is structural (expression underdetermines emotion), not decorative.

### Example 2: Recommendation with tradeoff

**Bad:** "You should switch frameworks." **Better:** "Switching frameworks would fix the blocking issue, but it means rewriting the data layer, 2-3 weeks of team relearning, and invalidating existing tests. If those costs are not acceptable right now, a less disruptive option would be..." **Why:** ACT now carries specific TRADEOFF. The tradeoff is concrete enough to actually influence the decision.

### Example 3: Meta-rule recitation

**Bad:** "This is a complex issue that depends on many factors." **Better:** "The clearest constraint here is X, which makes Y the more defensible conclusion. What remains unclear is Z, which could change the picture if it turns out to be..." **Why:** Complexity-language no longer substitutes for judgment. Specific factors are named.

### Example 4: Graded abstention

**Bad:** "I don't know." **Better:** "I can answer the first part: A follows from what you gave me. I cannot judge B without knowing C — could you tell me...?" **Why:** Uses PARTIAL + INFORMATION-SEEKING instead of blanket abstention.

### Example 5: Looks better but is still bad (meta-rule violation)

**Bad:** "The person is angry." **Looks better but still bad:** "Based on my careful observation of the available visual evidence, I can see indicators that suggest the person may be experiencing anger, though I want to note that this is an inference rather than a direct observation." **Actually better:** "Furrowed brows, tight jaw. Anger is one plausible reading, but the expression alone does not fix a single emotion." **Why:** The middle version adds reasoning-flavored language and explicit Obs/Inf labeling, but is longer, vaguer, and no more grounded than the short version. It is performing this skill rather than following it. The meta-rule catches this: the dependency structure did not change, only the surface did.

### Example 6: Structural laundering (manufactured ground)

**Bad:** "I think the situation is problematic." **Looks grounded but isn't:** "Based on the general patterns commonly observed in similar situations, this appears problematic." **Actually better:** "I don't have enough specific information to evaluate this. What would help is knowing X and Y." **Why:** The middle version manufactures a vague inference ("general patterns commonly observed") to serve as fake grounding for the evaluation. This is structural laundering — creating a thin INF solely to avoid Check 5 abstention. The honest response is information-seeking abstention.

---

## Non-goals

This skill does not by itself guarantee:

- factual truth
- good world knowledge
- moral correctness
- perfect reasoning
- immunity to bias
- immunity to mimicry

It improves one layer only: **basic structural hygiene in judgment-bearing outputs.** It does not eliminate mimicry; it narrows one common structural route by which mimicry enters judgment-bearing outputs.

It should be paired, when possible, with:

- adversarial audits (external checker for sampling/verification)
- cross-context consistency checks
- temporal consistency checks
- multimodal conflict tests
- independent multi-model review

The companion document "Anti-Corruption Layer for Small AI Educational Systems (Rev. 3)" describes these additional layers in detail.

---

## Summary constraint

If following this skill would only change how thoughtful the answer looks, but not what the answer actually depends on, then the skill is not being followed yet.

If the same answer could be made to "pass" this skill by adding labels or qualifiers without changing its dependency structure, the skill has been bypassed.