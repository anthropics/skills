# Cross-Layer Alignment Check — Detection Specifications

Eight failure modes that occur at the interfaces between layers. Many are only detectable when both Project and global layers are visible simultaneously. For each detected failure mode, produce: layers involved, specific conflicting content, severity, symptom, cause, fix, expected impact.

## Severity Classification

- **Critical:** Causes observable output degradation in every conversation. Fix immediately.
- **Major:** Causes intermittent problems or wastes significant context budget. Fix soon.
- **Minor:** Suboptimal but not causing observable harm. Fix when convenient.

---

## Failure Mode 1: Redundant Layering

**Layers:** L1 (Preferences) + L6 (Project CI)
**Detection:** Same behavioral instruction appears in both User Preferences and a Project's Custom Instructions, possibly in different wording.
**Symptom:** Wasted context budget. In some cases, Claude processes the instruction twice, leading to over-application (e.g., double emphasis on conciseness produces unnaturally terse output).
**Severity:** Major (context waste) or Critical (if over-application distorts output).
**Fix:** Determine which layer owns the instruction. If universal → keep in Preferences, remove from CI. If project-specific → keep in CI, remove from Preferences. If both claim it, Preferences wins for universal behaviors, CI wins for domain-specific behaviors.

## Failure Mode 2: Silent Override

**Layers:** L2 (Style) + L1 (Preferences) or L6 (Project CI)
**Detection:** An active Style specifies formatting, tone, or structural choices that contradict Preferences or CI instructions. The Style wins in Claude's processing, but the user may not realize the CI instruction is being overridden.
**Symptom:** CI instructions not reflected in output despite being correctly written. User repeatedly adjusts CI without improvement because the root cause is the Style, not the CI.
**Severity:** Critical (if it defeats Project-critical formatting) or Major (if it affects tone/style only).
**Fix:** Identify the specific Style attribute causing the override. Either adjust the Style, adjust the CI to work with the Style, or disable the Style for the affected Project if the conflict is fundamental.

## Failure Mode 3: Skill/Project Collision

**Layers:** L4 (Skills) + L6 (Project CI) or L7 (Knowledge Files)
**Detection:** A Skill's instructions conflict with or duplicate a Project's CI or knowledge file content. The Skill may enforce a methodology that contradicts the Project's approach, or a Skill may trigger on tasks that the Project's CI already handles with domain-specific instructions.
**Symptom:** Inconsistent output depending on whether the Skill activates. Or Claude follows the Skill's generic methodology instead of the Project's specialized instructions.
**Severity:** Major (inconsistency) or Minor (redundancy without conflict).
**Fix:** If the Skill is redundant with the Project's built-in instructions, disable the Skill for that Project context. If the Skill provides additional value, adjust the Project CI to work with (not against) the Skill's methodology. If the Skill overtriggers in the Project's domain, check whether the Skill description needs a negative trigger.

## Failure Mode 4: Connector/Instruction Mismatch

**Layers:** L5 (Connectors) + L6 (Project CI)
**Detection:** Project CI references tools, APIs, or external services that are not configured as MCP Connectors. Or Connectors are configured for services the Project CI never references.
**Symptom:** CI instructs Claude to use a tool that isn't available, causing silent failure or workaround behavior. Or configured Connectors add context overhead for tools the Project doesn't use.
**Severity:** Major (missing required Connector) or Minor (unused Connector adding overhead).
**Fix:** For missing Connectors: configure the required Connector, or remove the tool reference from CI. For unused Connectors: evaluate whether the Connector serves other Projects. If not, consider removing it.

## Failure Mode 5: Memory/Preference Confusion

**Layers:** L3 (Global Memory) or L8 (Project Memory) + L1 (Preferences)
**Detection:** A behavioral pattern has stabilized in Memory (appears consistently across conversations, user hasn't contradicted it) but hasn't been codified into Preferences or CI. Memory is doing the job of Preferences or CI — a context-inefficient pattern.
**Symptom:** The behavior works as long as Memory persists, but is fragile — Memory updates, deletions, or resets can break the pattern. The user may not realize a valued behavior depends on a Memory entry rather than a stable instruction.
**Severity:** Minor (works but fragile) to Major (if the behavior is critical to output quality).
**Fix:** Codify the stabilized pattern into the appropriate layer. Universal behaviors → Preferences. Project-specific behaviors → CI. Then clean the Memory entry (it's now redundant with the codified instruction).

## Failure Mode 6: Style/CI Tension

**Layers:** L2 (Style) + L6 (Project CI)
**Detection:** Active Style formatting preferences (e.g., "use bullet points," "be casual") conflict with Project CI output standards (e.g., "write in prose paragraphs," "maintain formal tone").
**Symptom:** Output formatting is inconsistent or doesn't match the CI's output standards. The Style may win on some formatting decisions while the CI wins on others, producing a hybrid that satisfies neither.
**Severity:** Major (if output formatting is critical to the Project's deliverables) or Minor (if the tension is cosmetic).
**Fix:** Evaluate whether the Style should apply to this Project. If the Project has specific output requirements, those should override Style preferences. Consider whether the Project needs its own output formatting section that explicitly addresses the Style interaction.

## Failure Mode 7: Cross-Project Duplication

**Layers:** L6 across multiple Projects
**Detection:** The same instruction appears in the Custom Instructions of 3+ Projects, in identical or near-identical wording. This indicates a universal behavior that should live in Preferences (L1) rather than being duplicated across Projects.
**Symptom:** Maintenance burden — updating the instruction requires editing multiple Projects. Risk of drift as Projects are updated independently.
**Severity:** Minor (redundancy) to Major (if the duplicated instructions have drifted and now contradict each other across Projects).
**Fix:** Promote the duplicated instruction to User Preferences. Apply the Universality Test: "Would this instruction improve output in a Project I haven't built yet?" If yes, promote. Remove from individual Project CIs after promoting. If the instruction varies slightly per Project, extract the universal core to Preferences and keep the per-Project variations in CIs.
**Requires:** CIs from 3+ Projects to detect.

## Failure Mode 8: Context Waste from Global Layers

**Layers:** L1-L5 combined
**Detection:** The total context contribution from global layers is disproportionate to the value they deliver. This could be verbose Preferences, multiple active Styles, cluttered Global Memory, many installed Skills with broad descriptions, or numerous Connectors — all consuming context budget before any Project content is processed.
**Symptom:** Less context budget available for Project content (CI, knowledge files, conversation history). May manifest as knowledge file content being truncated or conversation memory being shorter than expected.
**Severity:** Major (if it measurably reduces available Project context) or Minor (if global overhead is moderate).
**Fix:** Audit each global layer for efficiency. Compress Preferences. Clean Global Memory of stale entries. Evaluate whether all installed Skills and Connectors are actively used. The goal is not to minimize global layers — they provide real value — but to ensure each element earns its context budget.
