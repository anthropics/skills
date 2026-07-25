# Cross-Layer Alignment Check — Failure Mode Specifications

Sweep all eight failure modes against the user's provided layers. For each detected instance, produce a finding using the template at the bottom of this file.

---

## Failure Mode 1: Redundant Layering

**Layers involved:** User Preferences (Layer 1) + Project Custom Instructions (Layer 6)
**Severity:** Major (context waste, potential inconsistency if one copy is updated and the other is not)

**Detection method:** Compare each Preferences instruction against each provided Project CI. Look for semantic duplication — the exact same behavioral directive phrased differently counts as redundancy. Also check for near-duplicates where Preferences states a general rule and CI states a more specific version of the same rule.

**Resolution:** Determine the correct home. If the instruction is universally applicable → keep in Preferences, remove from CI. If it is project-specific → keep in CI, remove from Preferences. If Preferences has the general form and CI has a specialized form → keep the specialized form in CI and verify the general form in Preferences doesn't conflict.

**Information required:** User Preferences + at least one Project CI.

---

## Failure Mode 2: Silent Override

**Layers involved:** Styles (Layer 2) + User Preferences (Layer 1), or Styles (Layer 2) + Project CI (Layer 6)
**Severity:** Critical (user experiences unexpected behavior without understanding the source)

**Detection method:** Identify cases where a Style directive contradicts a Preference or CI instruction. Styles have high precedence in formatting and tone — they can silently override explicit behavioral directives in other layers. Common patterns: a Style that enforces brevity overriding a Preference for thorough explanations; a Style that enforces casual tone overriding a CI requirement for formal output.

**Resolution:** Make the conflict explicit. If the Style is intentional → update the Preference or CI to acknowledge the Style's influence. If the override is unintentional → adjust the Style or deactivate it for the affected context.

**Information required:** Active Style descriptions + User Preferences or Project CI.

---

## Failure Mode 3: Skill/Project Collision

**Layers involved:** Skills (Layer 4) + Project CI (Layer 6) or Project knowledge files (Layer 7)
**Severity:** Critical (conflicting instructions produce unpredictable output)

**Detection method:** Compare each installed Skill's description and known behavioral directives against Project CI instructions. Look for contradictory directives — a Skill that enforces a specific output format while a CI requires a different format; a Skill that enforces a workflow step that conflicts with a CI's process definition.

**Resolution:** Determine which instruction should govern. If the Skill is general-purpose and the CI is project-specific → the CI should take precedence; adjust the Skill's description with a negative trigger for that Project's domain. If the collision indicates a misconfiguration → disable the Skill in the affected Project or adjust the CI.

**Information required:** Installed Skills list (with descriptions) + at least one Project CI.

---

## Failure Mode 4: Connector/Instruction Mismatch

**Layers involved:** MCP Connectors (Layer 5) + Project CI (Layer 6)
**Severity:** Critical (CI references tools that don't exist, producing failed calls or confusion)

**Detection method:** Scan each Project CI for references to external tools, APIs, or integrations. Cross-reference against the list of configured MCP Connectors. Flag any tool reference in CI that lacks a corresponding connector, and any configured connector that no CI references.

**Resolution:** For missing connectors → either configure the connector or remove the CI reference. For orphan connectors → evaluate whether the connector serves ad-hoc use outside Projects. If not, recommend removal to reduce context overhead.

**Information required:** Configured MCP Connectors list + at least one Project CI.

---

## Failure Mode 5: Memory/Preference Confusion

**Layers involved:** Global Memory (Layer 3) or Project Memory (Layer 8) + User Preferences (Layer 1)
**Severity:** Major (behavioral patterns captured as memories instead of explicit instructions are fragile and may be lost or inconsistently applied)

**Detection method:** Scan Memory entries for behavioral directives — instructions about how Claude should behave rather than factual context about the user. Behavioral patterns in Memory ("user prefers concise responses," "user wants code examples in Python") indicate the user has trained Claude through interaction rather than explicit configuration. These should be evaluated for codification.

**Resolution:** Apply the Stability Test from `evolutionary-pathways.md`. If the pattern is stable and universal → codify as a Preferences instruction. If stable but project-specific → codify as a CI instruction. If recent or uncertain → leave in Memory and flag for future review.

**Information required:** Global Memory summary + User Preferences.

---

## Failure Mode 6: Style/CI Tension

**Layers involved:** Styles (Layer 2) + Project CI (Layer 6)
**Severity:** Varies (Minor if tension is cosmetic, Major if it affects deliverable quality)

**Detection method:** Compare Style formatting directives against Project CI output requirements. Common tensions: Style enforcing markdown formatting while CI requires plain text output; Style enforcing a word count range while CI requires comprehensive documentation; Style's tone conflicting with a Project's audience requirements.

**Resolution:** If the Style should apply globally except in specific Projects → note this as a known limitation the user should manage per-Project. If the tension affects output quality → recommend adjusting CI output instructions to explicitly override the Style for that Project, or recommend a Project-specific Style.

**Information required:** Active Style descriptions + at least one Project CI with output requirements.

---

## Failure Mode 7: Cross-Project Duplication

**Layers involved:** Project CI (Layer 6) across multiple Projects
**Severity:** Major (context waste, maintenance burden — updating the instruction requires changing every Project)

**Detection method:** Compare CI instructions across all provided Projects. Look for identical or semantically equivalent instructions appearing in 3+ Projects. Common candidates: formatting preferences, communication style directives, role definitions, quality standards, evidence requirements.

**Resolution:** Duplicated instructions are Promotion candidates. Apply the Universality Test: if the instruction improves every context → promote to Preferences. If it improves most but not all → promote to Preferences with a specificity caveat, or keep in CIs and accept the duplication cost.

**Information required:** Custom Instructions from 3+ Projects.

---

## Failure Mode 8: Context Waste from Global Layers

**Layers involved:** All global layers combined (Layers 1-5)
**Severity:** Minor (cumulative overhead, not a single-point failure)

**Detection method:** Estimate the total token footprint of all global layer content. Compare against value delivered. Global layers that consume significant context but provide minimal behavioral guidance represent waste. Check: Are Preferences verbose where they could be concise? Are there orphan Skills or connectors adding description overhead? Is Global Memory bloated with stale entries?

**Resolution:** Compress Preferences (see `preference-principles.md`). Remove orphan Skills and connectors. Clean stale Memory entries. The goal is not minimal context but proportional context — every token of global configuration should earn its presence.

**Information required:** Visibility into at least 3 of the 5 global layers.

---

## Finding Template

For each detected failure mode instance, produce:

```
**[Failure Mode Name]** — Severity: [Critical/Major/Minor]
Layers: [which layers are in conflict]
Evidence: [quote the specific conflicting content from each layer]
Symptom: [what the user experiences]
Cause: [why the conflict exists]
Fix: [specific change to make in each affected layer]
Expected impact: [what improves after the fix]
```
