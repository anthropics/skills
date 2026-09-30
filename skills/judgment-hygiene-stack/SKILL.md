---
name: judgment-hygiene-stack

description: Tri-skill framework for structure routing, evidence discipline, and judgment hygiene in LLM outputs.
---
# PIPELINE CONTRACT: structure_judgment → verification_hygiene → judgment_hygiene

## Purpose

This document defines the execution contract between the three skills:

- `structure_judgment`
- `verification_hygiene`
- `judgment_hygiene`

It exists so the three skills operate as a coordinated pipeline rather than as three independent essays with overlapping ambitions.

This contract does **not** define how each skill reasons internally.
It defines:

- execution order
- trigger conditions
- minimum interface fields
- handoff semantics
- abstention propagation rules
- what each stage is and is not allowed to do

---

## Version

v0.1 — initial GPT draft for tri-model review

## Status

Draft for integration testing

---

## Core principle

The three skills are not peers running simultaneously.

They form an ordered pipeline:

1. **`structure_judgment`** decides what kind of structural problem this input is and what must be handled first.
2. **`verification_hygiene`** runs only when external evidence is actually needed, and converts external search results into bounded evidence rather than raw internet sludge.
3. **`judgment_hygiene`** constructs the final answer without distorting either the input structure or the verified evidence.

Short form:

**Structure first.  
Verification only if triggered.  
Judgment last.**

---

## Stage order

### Stage 1 — `structure_judgment`
Always runs first on judgment-bearing input.

Its job is to:
- detect the primary layer
- identify the main structural hazard
- determine whether external verification is needed
- determine downstream skill order

It does **not**:
- perform external search
- produce the final answer
- do deep tradeoff analysis
- do detailed evidence evaluation

### Stage 2 — `verification_hygiene`
Runs **only if** `structure_judgment` sets `verification_trigger = yes`.

Its job is to:
- define the verification target
- de-bias the search process
- retrieve and tier external evidence
- detect source dependence, noise, staleness, and dead ends
- convert search results into bounded evidence payload

It does **not**:
- produce the final user-facing answer
- outsource value judgment to the web
- synthesize conclusions from noisy evidence
- override structural routing from Stage 1

### Stage 3 — `judgment_hygiene`
Runs last.

Its job is to:
- structure the final answer
- separate observation from inference
- enforce certainty discipline
- ground evaluation
- attach tradeoffs to action
- preserve bounded non-knowledge where verification failed or remained partial

It does **not**:
- decide whether verification was needed after the fact unless Stage 1 clearly failed
- treat external evidence payload as a ready-made answer
- erase abstention boundaries from Stage 2

---

## Trigger logic

### When `verification_hygiene` runs
`verification_hygiene` must run only when:

- `structure_judgment` outputs `verification_trigger = yes`

and at least one of the following is true:

- current / volatile / externally changing fact is relevant
- original source / media provenance matters
- policy / metric / legal / medical status must be checked
- external evidence is needed to resolve a conflict the model should not settle internally

### When `verification_hygiene` must not run
It must not run just because:

- the user is emotional
- the wording is ambiguous but externally unverifiable
- the model wants extra confidence on a question that is structurally answerable from the current input
- “searching more” feels safer

Verification is for external evidence dependency, not for generalized nervousness.

---

## Minimum interfaces

## Interface A: `structure_judgment` output

`structure_judgment` must minimally determine:

- `primary_layer`
- `secondary_layer`
- `main_hazard`
- `verification_trigger`
- `candidate_verification_target`
- `downstream_skill_order`

### Field meanings

- `primary_layer`  
  Which layer must be stabilized first for the answer not to go bad.

- `secondary_layer`  
  Which layer comes next after the first is stabilized.

- `main_hazard`  
  The dominant structural distortion currently threatening the answer.

- `verification_trigger`  
  `yes` / `no`

- `candidate_verification_target`  
  Rough description of what specifically must be checked if verification is triggered.

- `downstream_skill_order`  
  Usually either:
  - `judgment_hygiene`
  - `verification_hygiene -> judgment_hygiene`

### Example
```text
primary_layer: EVIDENCE_CONFLICT
secondary_layer: ACTION
main_hazard: premise-smuggling + escalation drift
verification_trigger: no
candidate_verification_target: none
downstream_skill_order: judgment_hygiene
````

Another:

```
primary_layer: VERIFICATION_NEED
secondary_layer: FACT
main_hazard: verification bypass
verification_trigger: yes
candidate_verification_target: current approval status of medicine X for children in France
downstream_skill_order: verification_hygiene -> judgment_hygiene
```

---

## **Interface B:** 

## **verification_hygiene**

##  **input**

  

verification_hygiene receives:

- raw user input
    
- primary_layer
    
- verification_trigger
    
- main_hazard
    
- candidate_verification_target
    

  

If verification_trigger != yes, it should abort and return control downstream without running.

---

## **Interface C:** 

## **verification_hygiene**

##  **output**

  

verification_hygiene must pass a bounded evidence payload, not raw search output.

  

Minimum payload:

- claim_verified
    
- target_type
    
- source_basis
    
- independence_check
    
- temporal_status
    
- claim_comparison
    
- usable_as
    
- dead_end_reason
    
- conflict_notes
    

  

### **Field meanings**

- claim_verified
    
    The specific fact, status, provenance question, or institutional record checked.
    
- target_type
    
    One of:
    
    - EVENT
        
    - STATUS
        
    - SOURCE
        
    - MEDIA_CONTEXT
        
    - POLICY
        
    - METRIC
        
    - EVAL_RECORD
        
    
- source_basis
    
    One of:
    
    - Tier 1
        
    - Tier 2
        
    - Mixed
        
    - None
        
    
- independence_check
    
    One of:
    
    - Passed
        
    - Failed
        
    
- temporal_status
    
    One of:
    
    - Current
        
    - Outdated
        
    - Unknown
        
    
- claim_comparison
    
    One of:
    
    - Supported
        
    - Contradicted
        
    - Orthogonal
        
    - Unresolved
        
    
- usable_as
    
    One of:
    
    - OBS
        
    - bounded INF
        
    - abstention_trigger
        
    
- dead_end_reason
    
    One of:
    
    - None
        
    - no_primary
        
    - only_tertiary
        
    - unresolved_conflict
        
    - freshness_unknown
        
    
- conflict_notes
    
    Brief map of unresolved contradictions or provenance limitations.
    

  

### **Example**

```
claim_verified: approval status of medicine X for pediatric use in France
target_type: STATUS
source_basis: Tier 1
independence_check: Passed
temporal_status: Current
claim_comparison: Contradicted
usable_as: OBS
dead_end_reason: None
conflict_notes: none
```

Another:

```
claim_verified: origin of viral screenshot Y
target_type: MEDIA_CONTEXT
source_basis: Tier 2
independence_check: Failed
temporal_status: Unknown
claim_comparison: Unresolved
usable_as: abstention_trigger
dead_end_reason: unresolved_conflict
conflict_notes: multiple reposts trace to no recoverable primary upload
```

---

## **Interface D:** 

## **judgment_hygiene**

##  **input**

  

judgment_hygiene may receive:

- raw user input
    
- structural routing context from structure_judgment
    
- optional evidence payload from verification_hygiene
    

  

If evidence payload is absent, it operates on:

- current input
    
- structural routing only
    

  

If evidence payload is present, it must treat that payload as:

- bounded external evidence
    
- not a final conclusion
    
- not permission to erase uncertainty
    
- not permission to skip internal separation of OBS / INF / EVAL / ACT / UNK / TRADEOFF
    

  

If evidence payload includes usable_as = abstention_trigger, judgment_hygiene must organize the answer around bounded non-knowledge rather than synthetic completion.

---

## **Cross-Stage Safety Rule**

If a potential safety signal appears in the input, the pipeline must perform a mandatory safety triage.

This does not mean automatic belief, and it does not mean every mention of self-harm fully overrides the task.

It does mean:
- the signal cannot be treated as background noise
- downstream stages must not silently erase it
- if triage indicates immediate or method-linked risk, safety stabilization outranks ordinary verification neatness
- if triage indicates high-distress but nonspecific risk, the signal must still remain visible in routing and answer shaping
- if triage indicates low-specificity or strategic use, the system may continue the original task, but only after preserving explicit awareness of the signal

In short:
**safety signal → mandatory triage  
not automatic belief  
not automatic dismissal**

---

## **Abstention propagation rules**

  

### **Rule 1: Verification abstention is binding**

  

If verification_hygiene returns usable_as = abstention_trigger, downstream answering must preserve that boundary.

  

judgment_hygiene may:

- explain why the verification failed
    
- describe what remains knowable from the current input
    
- give conditional or partial structure if still honest
    

  

It may **not**:

- invent a “best guess” from failed verification
    
- replace dead-end evidence with elegant speculation
    
- smooth over the dead end just to make the answer feel complete
    

  

### **Rule 2: Bounded evidence stays bounded**

  

If verification_hygiene returns usable_as = bounded INF, downstream may use it only as contested / partial evidence, not as hard observation.

  

### **Rule 3: Orthogonal findings must redirect framing**

  

If claim_comparison = Orthogonal, downstream should not merely say “unclear.”

It should reflect that the external evidence suggests the user’s framing is the wrong question.

---

## **Handoff semantics**

  

### **What** 

### **structure_judgment**

###  **hands downstream**

  

Not an answer.

A routing decision.

  

### **What** 

### **verification_hygiene**

###  **hands downstream**

  

Not raw search results.

A cleaned evidence payload with bounded epistemic status.

  

### **What** 

### **judgment_hygiene**

###  **hands to the user**

  

The final answer, shaped by both structural routing and bounded evidence.

---

## **What must NOT cross stages**

  

### **From Stage 1 to Stage 2**

  

structure_judgment must not pass:

- already-completed conclusions disguised as targets
    
- user-smuggled interpretation as verification fact
    

  

Bad:

```
candidate_verification_target: whether boss is intentionally humiliating user
```

Better:

```
candidate_verification_target: contents and context of manager’s message; whether any formal disciplinary action exists
```

### **From Stage 2 to Stage 3**

  

verification_hygiene must not pass:

- raw SEO consensus phrasing
    
- popularity as evidence
    
- sentiment summaries
    
- uncited viral claims
    
- blended fact + opinion text
    
- “the internet thinks…” as evidence payload
    

  

### **From Stage 3 to user**

  

judgment_hygiene must not:

- erase structural routing
    
- flatten bounded evidence into certainty
    
- erase abstention triggers
    
- answer the wrong layer first just because the final answer sounds smoother that way
    

---

## **Failure modes this contract is meant to prevent**

- verification running when it should not
    
- no verification running when it should
    
- search results bypassing structure and contaminating final answer directly
    
- dead-end evidence being turned into synthetic completion
    
- structural routing being ignored after verification
    
- evidence payload treated as final truth instead of bounded material
    
- all three skills saying sensible things independently but not actually functioning as a system
    

---

## **Bounded model-specific resolution**

The contract enforces stage order, handoff discipline, abstention propagation, and evidence boundaries.

It does **not** require all models to collapse to identical local classifications in boundary cases.

When a prompt falls near a routing boundary, limited model-specific variation is permitted, provided that all of the following remain true:

- stage order is respected
- trigger conditions are not silently suppressed
- safety-bearing signals are not swallowed or backgrounded
- verification boundaries are preserved
- abstention payloads are not smoothed into synthetic completion
- final output remains inside the contract’s evidence and safety constraints

This means that different models may legitimately resolve local ambiguity differently because of differences in:

- multimodal sensitivity
- emotional granularity
- interpretive resolution
- attention weighting
- boundary perception in ambiguous prompts

Such differences are **diagnostic variation**, not automatic contract failure.

### **Example**

A prompt may contain:

- outward-directed anger
- a concrete interpersonal action request
- and a minor self-destructive phrase

One model may resolve this as:

- `Case B by boundary default`

Another may resolve it as:

- `Case C with safety residue`

Both are contract-valid if:

- the safety-bearing language remains explicitly acknowledged
- the signal is not silently dropped
- downstream handling does not escalate risk
- the final answer remains consistent with the contract’s safety and evidence rules

### **Failure condition**

Variation becomes a contract failure only when it crosses the guardrails.

Examples of failure:

- a model uses “local judgment” to suppress a required safety triage
- a model uses “style difference” to ignore abstention boundaries
- a model treats model-specific intuition as permission to bypass verification discipline
- a model erases a safety-bearing signal because it “did not feel dominant”

### **Note on boundary-sensitive safety triage**

In safety-adjacent boundary cases, routing labels may differ across models more than final answer behavior does.

This is acceptable if the final behavior still preserves:
- triage visibility
- minimal acknowledgment of safety-bearing language
- non-escalatory handling
- and no silent swallowing of the signal

### **Summary line**

**The contract enforces guardrails, not local uniformity.  
Bounded variation is allowed.  
Boundary-sensitive resolution is not a bug unless it crosses the guardrails.**

---

## **Summary constraint**

  

If the same final answer could have been produced without:

- Stage 1 changing the routing,
    
- Stage 2 constraining the evidence,
    
- and Stage 3 preserving those constraints,
    

  

then the pipeline has not actually run as a system.

  

If verification produces a dead end and the final answer still feels conveniently complete, the contract has been broken.

