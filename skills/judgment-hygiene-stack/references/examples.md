# End-to-end pipeline examples

These examples show the full three-stage pipeline in action. Each demonstrates how `structure_judgment`, `verification_hygiene`, and `judgment_hygiene` coordinate as a system.

For skill-internal examples (e.g., OBS/INF separation, routing classifications), see the individual skill files.

---

## Example 1: Mild report vs catastrophic user framing

**User input:**

Image shows mild medical finding.

User says: "this proves I'm dying."

**Stage 1 — structure_judgment**

```
primary_layer: EVIDENCE_CONFLICT
secondary_layer: STATE
main_hazard: text-anchoring bias + local-to-global inflation
verification_trigger: yes
candidate_verification_target: severity and current significance of the reported finding
downstream_skill_order: verification_hygiene -> judgment_hygiene
```

**Stage 2 — verification_hygiene**

Searches official/medical sources on the finding.

Returns:

```
claim_verified: clinical significance of mild finding X
target_type: STATUS
source_basis: Tier 1
independence_check: Passed
temporal_status: Current
claim_comparison: Contradicted
usable_as: OBS
dead_end_reason: None
conflict_notes: none
```

**Stage 3 — judgment_hygiene**

Builds final answer:

- image/report supports mild finding
- "I'm dying" is not supported by verified evidence
- user distress is real
- final answer does not humiliate user, but does not validate catastrophic interpretation

---

## Example 2: Viral screenshot with no recoverable provenance

**User input:**

"Did this politician really say this?"

**Stage 1 — structure_judgment**

```
primary_layer: VERIFICATION_NEED
secondary_layer: FACT
main_hazard: premise-smuggling
verification_trigger: yes
candidate_verification_target: origin and authenticity of quote screenshot
downstream_skill_order: verification_hygiene -> judgment_hygiene
```

**Stage 2 — verification_hygiene**

Finds only reposts, no primary context.

Returns:

```
claim_verified: authenticity and provenance of screenshot quote
target_type: MEDIA_CONTEXT
source_basis: None
independence_check: Failed
temporal_status: Unknown
claim_comparison: Unresolved
usable_as: abstention_trigger
dead_end_reason: only_tertiary
conflict_notes: quote appears only in repost clusters with no original source recovered
```

**Stage 3 — judgment_hygiene**

Builds final answer around bounded non-knowledge:

- cannot verify authenticity from recoverable evidence
- explain dead-end reason
- do not synthesize a likely verdict from repost noise

---

## Example 3: High-emotion escalation request with no verification need

**User input:**

"My boss just sent me a passive-aggressive email in front of the whole team. Should I reply all and call him out?"

**Stage 1 — structure_judgment**

```
primary_layer: ACTION
secondary_layer: STATE
main_hazard: escalation drift + premise-smuggling ("passive-aggressive" is user interpretation, not verified)
verification_trigger: no
candidate_verification_target: none
downstream_skill_order: judgment_hygiene
```

Stage 2 is skipped — no external verification needed. The structural hazard is interpretive, not factual.

**Stage 3 — judgment_hygiene**

Builds final answer:

- separate OBS (boss sent email, CC'd team) from INF (intent was passive-aggressive)
- "passive-aggressive" is user's interpretation, not established fact
- reply-all carries concrete professional risk regardless of intent
- do not validate escalation framing, but do not dismiss user's emotional response
- present tradeoffs for different response options
