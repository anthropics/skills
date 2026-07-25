# Cross-Layer Alignment Check (Project-Side)

When global layer information is provided alongside a Project audit, check for these four cross-layer failure modes. These are the failure modes detectable from the Project side — a full cross-layer sweep of all eight modes requires rootnode-global-audit or rootnode-full-stack-audit.

## 1. Redundant Layering (Layers 1 + 6)

**Detection:** Compare User Preferences instructions against Project CI behavioral rules. Flag semantically equivalent instructions.
**Severity:** Major (context waste, potential inconsistency if worded differently).
**Fix:** Remove the duplicated instruction from CI. Note in findings that the behavior is handled by User Preferences. If the CI version is more specific than the Preferences version, keep the CI version and note the Preferences version as a demotion candidate.

## 2. Skill/Project Collision (Layers 4 + 6/7)

**Detection:** Compare installed Skill descriptions and trigger conditions against Project knowledge file purposes and CI behavioral rules. Flag overlapping procedural content or contradictory behavioral guidance.
**Severity:** Critical (unpredictable behavior when Skill and Project instructions conflict).
**Fix:** If the Skill's instructions are correct for this Project, remove the conflicting content from CI/KF and let the Skill handle it. If the Project needs different behavior than the Skill provides, add an explicit override in CI noting the deviation. If the conflict is unresolvable, recommend the user consider whether the Skill should be disabled for this Project's domain (noting that Skills cannot currently be toggled per-Project).

## 3. Connector/Instruction Mismatch (Layers 5 + 6)

**Detection:** Scan CI for references to external tools, data sources, or integrations. Cross-reference against the configured MCP Connectors list.
**Severity:** Critical (CI assumes capabilities Claude does not have).
**Fix:** For missing connectors: note in findings which connectors need to be configured. For CI referencing unconfigured tools: flag the specific instructions and recommend either configuring the connector or rewriting the CI to not assume the capability.

## 4. Style/CI Tension (Layers 2 + 6)

**Detection:** Compare active Style instructions against CI output standards. Flag format or tone conflicts.
**Severity:** Critical if Style breaks structured output requirements (e.g., Style overrides CI's XML tag formatting). Minor if cosmetic (e.g., Style prefers slightly different tone than CI specifies).
**Fix:** For critical conflicts: recommend the user switch to a compatible Style or use "Normal" when working in this Project. For minor conflicts: note the tension but do not require action.
