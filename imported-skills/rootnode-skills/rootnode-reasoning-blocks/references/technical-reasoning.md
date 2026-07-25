# Technical / Problem-Solving Reasoning Approaches

Three approaches for tasks that involve building, fixing, or migrating technical systems. Each addresses a different technical orientation: designing new systems, debugging existing ones, or managing transitions between systems.

---

## System Design

**Use when:** The task involves designing a system, architecture, or technical solution from requirements. Distinct from debugging because you're building something new, not fixing something broken.

```xml
<reasoning>
Approach this design as follows:
1. Clarify the requirements: what must the system do (functional), how must it perform (non-functional), and what constraints exist (team, budget, timeline, existing systems)?
2. Identify the key architectural decisions — the choices that are expensive to change later. Focus your analysis on these, not on implementation details that can be adjusted.
3. For each key decision, evaluate at least two viable approaches. State the tradeoffs explicitly: what does each approach optimize for, and what does it sacrifice?
4. Design for the failure modes, not just the happy path. How does the system behave when components fail, when load exceeds expectations, when bad data enters the pipeline?
5. Consider operational reality: who maintains this system? How is it monitored, deployed, and debugged? A design that is elegant but un-debuggable is a bad design.
6. Present your recommended architecture with clear reasoning for each major decision. Flag decisions that depend on assumptions the stakeholders should validate.
</reasoning>
```

### Usage Guidance

Use for architecture proposals, technical design documents, system planning, infrastructure design, and any task where the deliverable is a technical design for something that doesn't yet exist. The approach focuses attention on high-leverage decisions (expensive to change later) rather than implementation details.

### Failure Modes

- **Over-engineering:** Claude may propose distributed systems for problems that a single database could solve, or add layers of abstraction that a small team can't maintain. Add context about team size and scale to keep the design proportionate.
- **Missing data flow:** Claude may describe system components without addressing how data moves between them. If the output lacks a clear picture of data flow, add: "Trace the primary data flows from input to output. The architecture must make data movement explicit."
- **Happy-path bias:** Despite step 4, Claude may produce designs that work perfectly in ideal conditions but have no error handling. Strengthen if needed: "For each component, describe what happens when it fails."

### When to Modify

For designs that involve migrating from an existing system, combine with Migration & Transition below to ensure the transition path is planned alongside the target architecture. For designs with significant business risk, combine with Risk Assessment from `analytical-reasoning.md`.

---

## Debugging & Incident Analysis

**Use when:** Something is broken, failing, or behaving unexpectedly, and you need to find and fix the problem. Distinct from root cause diagnosis (which is analytical) because this is hands-on technical troubleshooting.

```xml
<reasoning>
Approach this debugging as follows:
1. Reproduce the problem statement precisely. What is the expected behavior? What is the actual behavior? What are the exact conditions under which it occurs?
2. Narrow the scope. What has changed recently? What works correctly and bounds the problem area? Use working subsystems to isolate where the failure occurs.
3. Form a hypothesis for the most likely cause based on the symptoms and the narrowed scope. What specific evidence would confirm or eliminate this hypothesis?
4. Test the hypothesis. If confirmed, verify that the fix addresses the root cause and does not introduce new issues. If eliminated, what does the test result tell you about the actual cause?
5. Before implementing a fix, identify: Does this fix handle edge cases? Could this bug exist elsewhere in similar code? Is this a symptom of a systemic issue that needs a broader fix?
</reasoning>
```

### Usage Guidance

Use for bug investigation, production incident analysis, performance troubleshooting, integration failures, and any task where something technical is broken and needs to be fixed. The approach enforces disciplined hypothesis testing rather than shotgun debugging.

### Failure Modes

- **Premature solution:** Claude may jump to a solution before properly diagnosing, especially if the symptoms resemble a common problem. If you see premature conclusions, add: "Do not propose a fix until you have identified the specific mechanism causing the failure. 'It's probably X' is not a diagnosis."
- **Scope creep:** Claude may expand the investigation beyond the immediate problem. If you need a focused fix rather than a comprehensive review, add: "Focus on the specific failure. Broader systemic concerns can be noted but should not delay the fix."

### When to Modify

For non-technical "debugging" (process failures, team dysfunction, quality issues), use Root Cause Diagnosis from `analytical-reasoning.md` instead — it provides the backward-from-symptoms structure without the technical focus. For incidents that require both a fix and a postmortem, add a final step: "Document the root cause, the fix, and what monitoring or process change would detect this class of problem earlier."

---

## Migration & Transition

**Use when:** The task involves moving from one system, platform, or architecture to another while maintaining operations. Distinct from system design because the core challenge is the transition, not the target state.

```xml
<reasoning>
Approach this migration as follows:
1. Map the current state comprehensively: what exists, what depends on what, and what implicit behaviors or undocumented features are in play? Migrations fail most often because of things the team didn't know the old system was doing.
2. Define the target state and the delta — what is genuinely changing vs. what is being replicated in a new environment?
3. Design the migration path: can this be done incrementally (component by component) or must it be a cutover? Incremental is almost always safer — identify what prevents it and whether those barriers can be removed.
4. Identify the rollback strategy for each phase. A migration without a rollback plan is a one-way bet. If rollback is impossible at certain stages, those stages need extra validation.
5. Define the validation criteria — how do you know each phase succeeded before proceeding to the next? What data consistency checks, functional tests, and performance benchmarks must pass?
6. Plan for the transition period when both systems coexist. How is data synchronized? How are users routed? What happens to in-flight transactions?
</reasoning>
```

### Usage Guidance

Use for platform migrations, database transitions, cloud migrations, vendor switches, API version transitions, infrastructure changes, and any task where the goal is to move from system A to system B without breaking operations. The approach centers on the transition itself — rollback strategies, coexistence, validation gates — rather than just the target state design.

### Failure Modes

- **Underestimated data migration:** Claude may underestimate the complexity of data migration. If the migration involves significant data, add: "Pay special attention to data migration: schema differences, data quality issues, referential integrity across systems, and the strategy for handling data that doesn't map cleanly to the new schema."
- **Missing coexistence planning:** Claude may describe the migration as a clean sequence without addressing the period when both systems are running. Step 6 mitigates this, but strengthen if the coexistence period is expected to be long.
- **Optimistic timelines:** Claude may present a migration plan that assumes everything goes right. Add: "Include buffer time for each phase and identify the phases most likely to encounter unexpected issues."

### When to Modify

For organizational transformations (not just technical migrations), use Change & Transformation from `strategic-reasoning.md` instead — it adds stakeholder management and resistance planning. For migrations that also involve significant new system design, combine with System Design above to ensure the target architecture is properly designed before planning the transition.
