# Real Subagent Protocol — Claude Code

## Why ECD Requires Real Subagents

ECD uses real subagents (via the `Agent` tool) to counter a predictable failure mode: the parent model anchors on its own framing and then unconsciously protects it.

Mandatory independent stages are therefore not advisory decoration. They are structural checks on plan quality.

## Hard Rule

The following stages require real spawned agents:

- D / critique
- G / red-blue
- H / review
- J / compile-for-code

Stage A may use support agents, but the parent model remains the owner and writer of preprocess.

## General Protocol

Every subagent follows the same base rules:

- receive only stage-local context
- do not receive the parent's preferred answer
- return structured deltas instead of final notes
- never write bundle files directly
- let the parent remain the sole bundle writer

## Shared Delta Shape

All independent agents return the same shape:

```json
{
  "facts": [],
  "challenges": [],
  "conflicts": [],
  "gaps": [],
  "discard_recommendations": [],
  "follow_up_questions": [],
  "confidence": "medium",
  "evidence_refs": []
}
```

This makes the parent integrate independent findings without giving up ownership of the canonical notes.

## Stage A Support Agents

These are optional helpers. They are useful when the raw request is vague, solution-biased, or internally contradictory.

### Intent Extractor

Purpose:

- infer likely real goals beyond the literal request
- surface hidden assumptions
- suggest examples and counterexamples worth eliciting

Use when:

- the user names a solution before naming the real problem
- the request sounds under-specified but emotionally certain

### Reality Gap Checker

Purpose:

- challenge claims that may be false, incomplete, or repo-inconsistent
- identify contradictions between the request and observable reality

Use when:

- the user asserts repo behavior without evidence
- the proposed solution may rely on non-existent infrastructure

### Blind Spot Scout

Purpose:

- identify dimensions the user has not named yet
- force consideration of non-goals, edge cases, acceptance meaning, and failure handling

Use when:

- the request jumps straight to feature construction
- important workflow edges are likely missing

## D / Critique Agent

Stage D requires one independent critique agent.

### Mission

- identify pseudo-requirements
- find contradictions
- remove unverifiable or wasteful requirements
- challenge bad decompositions before they harden

### Why it exists

Without D, Stage C often preserves polished nonsense.

## G / Red And Blue Agents

Stage G requires two independent agents.

### Red

Mission:

- attack edge cases
- attack abuse paths
- attack dependency failure
- attack invalid state transitions
- attack ambiguity in recovery behavior

### Blue

Mission:

- mitigate attacks
- convert attacks into explicit rules
- name residual risk when mitigation is out of scope

### Why both are required

Red without blue creates panic. Blue without red creates optimism. The pair forces explicit defense.

## H / Review Agent

Stage H requires one independent review agent.

### Mission

- judge whether the next coder would still need to invent meaning
- return `approved`, `approved_with_conditions`, or `rejected`
- name the earliest stage to reopen if rejected

### What H protects

H protects against fake readiness. A bundle can look detailed and still leave critical semantics undefined.

## J / Compile-for-Code Agent

Stage J requires one independent compile-for-code agent.

### Mission

- absorb the converged A-H package
- decide whether the package is really code-ready
- compile execution-facing companion docs
- confirm the direct next code command

### Why J is separate from H

H judges readiness. J operationalizes readiness. A package can be review-approved and still poorly compiled for execution.

## Failure Handling

If a mandatory agent cannot be created:

- write the stage note anyway
- set `status=blocked_by_agent_unavailable`
- set `agent_mode=blocked`
- stop before later dependent stages claim completion

ECD does not permit fake completion when independence is missing.

## Practical Claude Code Guidance

When implementing this protocol in Claude Code:

- keep agent prompts stage-local
- do not forward your own solution as the default answer to agents
- integrate deltas into notes only after checking they match repo reality
- preserve evidence references so validators and later readers can audit the reasoning trail
