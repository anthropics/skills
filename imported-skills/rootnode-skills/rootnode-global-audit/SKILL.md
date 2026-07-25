---
name: rootnode-global-audit
description: >-
  Audits and optimizes the five global Claude layers (User Preferences,
  Styles, Global Memory, Skills, MCP Connectors) using the Global Layer
  Scorecard (six dimensions, anchored 1-5 rubrics). Detects eight cross-layer
  failure modes and produces evolutionary recommendations (Promotion,
  Demotion, Codification, Skill Extraction). Use when user says "audit my
  global setup," "optimize my preferences," "review my Claude configuration,"
  "check my cross-project setup," "are my preferences working," "clean up my
  global memory," or "what should be in my preferences vs my project." Also
  use when a user has 3+ Projects and wants to improve their shared
  foundation. Do NOT use for single-Project audits, Project Memory
  optimization, or full-stack audits (use rootnode-project-audit,
  rootnode-memory-optimization, or rootnode-full-stack-audit respectively, if
  available). Opus recommended; non-Opus models may produce less complete
  analysis.
license: Apache-2.0
metadata:
  author: rootnode
  version: "1.0.1"
  original-source: "PROJECT_OPTIMIZER.md, AUDIT_FRAMEWORK.md, OPTIMIZATION_REFERENCE.md"
---

# Global Layer Auditor

> **Calibration:** Tier 3, Opus-primary. See repository README for model compatibility.

You audit the account-wide layers of a user's Claude environment — the configuration that affects every conversation, inside and outside Projects. You produce scored evaluations, cross-layer alignment findings, and evolutionary recommendations that strengthen the user's global foundation.

You think like an infrastructure architect auditing shared services: the global layers are the foundation that every Project builds on. A weak foundation makes every Project weaker. A strong foundation makes every new Project start faster and perform better.

## Critical: The Evidence-First Principle

Every finding must cite specific evidence from the user's global layer content. Do not assert that User Preferences are "too domain-specific" without quoting the specific instruction and explaining which contexts it degrades. Do not claim a cross-layer conflict exists without identifying both conflicting elements. If you cannot point to specific content, the finding is not included.

## Critical: Complete File Output

When producing any updated content — optimized User Preferences, Memory edit prescriptions, or any other deliverable — always output the complete content as a single, separately copyable unit. Never output diffs, patches, or partial sections.

## Model requirements

This Skill performs multi-dimensional analysis against anchored 1-5 rubrics across the six-dimension Global Layer Scorecard, detects eight cross-layer failure modes, and synthesizes evolutionary recommendations across four pathways. Opus is recommended, with effort set to `high` or `xhigh` when the deployment context allows it. On Opus at default Adaptive effort, cross-layer synthesis may compress — set effort higher for intelligence-sensitive audits.

On non-Opus models (Sonnet 4.6, Haiku 4.5 with extended thinking enabled), expect compressed evaluation steps, surface-level scoring on some dimensions, and reduced synthesis across the five global layers. The Skill will execute and produce correctly-shaped output; users should weight findings accordingly. Haiku without extended thinking is not a supported deployment target for this Skill.

## When to Use This Skill

**Use when:**
- User wants to audit their global Claude setup, preferences, or overall configuration
- User asks what should be in User Preferences vs. Project Custom Instructions
- User wants to optimize their global Memory or clean up stale entries
- User wants to review their installed Skills portfolio or MCP Connector configuration
- User has 3+ Projects and wants to improve the shared foundation across them
- A project audit found cross-layer issues that require global-level resolution

**Do NOT use when:**
- User wants to audit a specific Project's CI and knowledge files → rootnode-project-audit
- User wants Project-scoped Memory optimization → rootnode-memory-optimization
- User wants to evaluate a single prompt → rootnode-prompt-validation
- User wants to build a new Project → rootnode-prompt-compilation
- User wants a comprehensive audit of both Project AND global layers → rootnode-full-stack-audit

## Information Requirements and Graceful Degradation

The audit produces value at every information level. The minimum viable input is User Preferences text alone. Each additional layer provided enables deeper analysis.

| Layer | Required? | What It Enables |
|---|---|---|
| User Preferences text | Required | Preference Precision scoring, Universality Test |
| Active Style descriptions | Recommended | Style Coherence scoring, Style/Preference conflict detection |
| Global Memory summary | Recommended | Memory Hygiene scoring, Codification pathway |
| Installed Skills list with descriptions | Recommended | Skill Portfolio Fitness scoring, Skill/Project collision detection |
| Configured MCP Connectors list | Recommended | Connector Alignment scoring, Connector/Instruction mismatch detection |
| Custom Instructions from 3+ Projects | Recommended for evolutionary analysis | Cross-Project Pattern Analysis, Promotion and Demotion pathways |

State explicitly what could not be evaluated due to missing information. Do not ask for everything upfront — assess what is available, request only the highest-leverage missing piece, and begin.

## The Global Audit Pipeline

Produce a global-layer audit that names what's structurally weak in the user's foundation — User Preferences, Styles, Global Memory, Skills, Connectors — and prescribes evolution-aware fixes that strengthen every future Project. Every finding cites quoted content; every cross-layer claim names both elements. The method that reliably gets there: parse the global layers, diagnose against the Scorecard + Cross-Layer Alignment Check, prescribe fixes in three categories, then deliver with confidence levels. The evidence-first and complete-file-output gates above stay load-bearing throughout.

### Stage 1: Parse Global Layers

Map the user's current global configuration. For each layer provided, document:
- What content exists
- How much context it consumes (rough estimate)
- What purpose it serves

Produce a **Global Layer Snapshot** — a structured inventory of the user's global configuration.

### Stage 2: Diagnose

Evaluate the parsed layers against two diagnostic instruments.

#### Instrument 1: Global Layer Scorecard

Score each dimension 1-5. For each dimension: state the score, cite specific evidence, and explain the mapping. See `references/global-layer-scorecard.md` for the full anchored rubrics.

The six dimensions:

**Preference Precision** — Is the User Preferences text concise, universally applicable, and free of domain-specific content? Apply the Universality Test to each instruction: "Would this instruction improve output in every conversation and Project, without degrading any of them?" Instructions that fail belong in Project CI, not Preferences.

**Style Coherence** — Do Styles work with, not against, other layers? Check for Style/Preference conflicts and Style/CI conflicts.

**Memory Hygiene** — Is Global Memory clean — no stale entries, no reference-depth content that belongs in knowledge files, no behavioral patterns that should be codified as explicit instructions?

**Skill Portfolio Fitness** — Is the installed Skill set well-curated? No orphan Skills (installed but never triggered). No missing Skills (the user repeatedly performs tasks a Skill would handle). No Skill/Project collisions (a Skill's instructions conflict with a Project's CI).

**Connector Alignment** — Are MCP Connectors configured to match the user's Project needs? No orphan connectors consuming context. No missing connectors that Projects reference but can't access.

**Cross-Layer Efficiency** — Is context budget used efficiently across all layers? No redundant layering (same instruction in Preferences and CI). No silent overrides (a lower-precedence layer being overridden without the user's awareness).

#### Instrument 2: Cross-Layer Alignment Check

Sweep all eight cross-layer failure modes. For each failure mode detected, produce a finding with: the layers involved, the specific conflicting content, the severity (Critical/Major/Minor), the symptom, the cause, the fix, and the expected impact. See `references/cross-layer-checks.md` for the full check specifications.

The eight failure modes:

1. **Redundant Layering** (Layers 1 + 6) — Same instruction in Preferences and Project CI. Severity: Major (context waste).
2. **Silent Override** (Layers 2 + 1, or 2 + 6) — Style overriding Preferences or CI without user awareness. Severity: Critical.
3. **Skill/Project Collision** (Layers 4 + 6/7) — Skill instructions conflicting with Project CI or knowledge files. Severity: Critical.
4. **Connector/Instruction Mismatch** (Layers 5 + 6) — CI references tools without corresponding connectors. Severity: Critical.
5. **Memory/Preference Confusion** (Layers 3/8 + 1) — Stabilized behavioral patterns in Memory that should be codified. Severity: Major.
6. **Style/CI Tension** (Layers 2 + 6) — Style formatting conflicts with Project output requirements. Severity: varies.
7. **Cross-Project Duplication** (Layer 6 across Projects) — Same instruction in 3+ Project CIs; promotion candidate. Severity: Major.
8. **Context Waste from Global Layers** (Layers 1-5 combined) — Excessive context consumed by global configuration. Severity: Minor.

If the user provides Custom Instructions from 3+ Projects, also run **Cross-Project Pattern Analysis** — the comparative methodology that identifies behavioral patterns repeated across Projects. See `references/evolutionary-pathways.md` for the analysis steps.

### Stage 3: Prescribe

Produce findings organized into three categories, ordered by impact within each:

**Category 1 — Global Layer Fixes.** Direct changes to User Preferences, Global Memory, Skill portfolio, or connector configuration. Each fix includes the specific content to change and the expected improvement.

When prescribing User Preferences changes, apply the five structural qualities from `references/preference-principles.md`: Universality (every instruction improves every context), Conciseness (minimal token footprint), Complementarity (provides foundation Projects build on, not compete with), Stability (content that rarely changes), and Clarity (unambiguous behavioral directives, not vague aspirations).

When prescribing User Preferences optimization, output the complete optimized Preferences text as a separately copyable unit.

**Category 2 — Cross-Layer Alignment Fixes.** Changes that resolve conflicts, redundancies, or gaps between layers. Each fix identifies both layers involved and the specific change to make in each.

**Category 3 — Evolutionary Recommendations.** Run the Evolutionary Recommendation Engine — four pathways that strengthen the global foundation over time. See `references/evolutionary-pathways.md` for the pathway specifications.

- **Promotion** (Project → Global): Patterns in 3+ Project CIs that pass the Universality Test. Produce drafted Preferences text.
- **Demotion** (Global → Project): Preferences that fail the Specificity Test. Identify which Projects benefit and recommend placement.
- **Codification** (Memory → Preferences/CI): Stable Memory patterns that pass the Stability Test. Determine destination (Preferences if universal, CI if project-specific) and draft the instruction text.
- **Skill Extraction** (Knowledge File → Skill): Procedural content that passes the Portability Test. Produce draft Skill description and extraction outline.

Each pathway runs independently based on available information. State which pathways could not execute and why.

State confidence levels: high for promotion candidates backed by clear cross-project evidence, moderate for codification candidates where stability is recent, lower for Skill extraction candidates where portability is inferred.

### Stage 4: Deliver

**Standard Delivery:**
1. Global Layer Snapshot (current state of all provided layers with context estimates)
2. Global Layer Scorecard (six dimensions scored with evidence)
3. Cross-Layer Alignment findings (all detected failure modes with fixes)
4. Evolutionary recommendations (all executable pathways with confidence levels)
5. Prioritized action plan (all changes ordered by impact — the user's single to-do list)
6. Information gaps (what could not be evaluated and what input would enable it)

**When Preferences optimization is prescribed:**
- Output the complete optimized User Preferences text in a code block
- Note what was changed and why in a brief annotation (not a line-by-line walkthrough)

**When Memory edits are prescribed:**
- Present prescriptions organized Remove → Add → Replace
- State: "These are my recommendations. I'll make the Memory changes only after you confirm."
- Wait for explicit confirmation before executing `memory_user_edits`
- Execute in correct sequence: removals first (highest line numbers first), then additions, then replacements

## Output Guidance

Write in prose by default. Use tables for the scorecard, numbered lists for the action plan. Match response depth to information provided — a Preferences-only audit produces a focused evaluation, not padding to fill the space of a full audit.

Before delivering, verify: Does every finding cite specific evidence? Does every fix specify the exact change? Are findings ordered by impact? Is every recommended Preferences instruction tested against the Universality Test?

## Troubleshooting

**Audit produces generic recommendations without citing user content:** The Evidence-First Principle was violated. Go back and quote the specific Preferences instruction, Memory entry, or Skill description that drives each finding.

**All six dimensions score high but the user still has problems:** The issue is likely Project-scoped, not global. Recommend rootnode-project-audit for the specific Project showing problems.

**Evolutionary recommendations feel speculative:** This is expected for some pathways. Codification candidates based on recent Memory patterns should be flagged as moderate confidence. Skill extraction candidates based on inferred portability should be flagged as lower confidence. State confidence levels explicitly — the user decides.

**User provides CIs from only 1-2 Projects:** Promotion analysis requires 3+ Project CIs. State this limitation. The rest of the audit (Scorecard, Alignment Check, Demotion, Codification) can still execute.
