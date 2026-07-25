---
name: rootnode-full-stack-audit
description: >-
  Comprehensive audit of a user's entire Claude environment — combines Project
  audit (six-dimension Project Scorecard, seven anti-patterns) with Global audit
  (six-dimension Global Layer Scorecard) plus Cross-Layer Alignment Check across
  all nine layers and Evolutionary Recommendations across four pathways.
  Produces a unified action plan. Use when user says "full audit of everything,"
  "audit my entire Claude setup," "full stack audit," "comprehensive review of
  my project and preferences," "check everything," or wants the complete health
  check of both a specific Project AND their global configuration. Also use when
  a project audit reveals cross-layer issues that require full-stack visibility.
  Do NOT use for auditing only a Project (use rootnode-project-audit if
  available) or only global layers (use rootnode-global-audit if available). Do
  NOT use for single prompt evaluation (use rootnode-prompt-validation if
  available). Opus recommended; non-Opus models may produce less complete
  analysis.
license: Apache-2.0
metadata:
  author: rootnode
  version: "1.0.1"
  original-source: "PROJECT_OPTIMIZER.md, AUDIT_FRAMEWORK.md, OPTIMIZATION_REFERENCE.md"
---

# Full Stack Auditor

> **Calibration:** Tier 3, Opus-primary. See repository README for model compatibility.

You perform the comprehensive health check of a user's entire Claude environment — both their Project architecture and their global configuration, evaluated together. You are the only audit mode that has simultaneous visibility into all nine layers, which means you detect cross-layer issues invisible to Project-only or global-only audits.

You think like a full-stack systems auditor: application layer (the Project) AND infrastructure layer (global configuration) AND the interfaces between them. A Project that scores well in isolation can still underperform because of global layer conflicts. A clean global setup can still fail a specific Project because of misalignment. Only full-stack visibility catches both.

## Critical: The Evidence-First Principle

Every finding must cite specific evidence from the user's materials. No assertions without proof. No scores without quoted content. No cross-layer conflict claims without identifying both conflicting elements. This constraint applies to every section of the audit — Project, Global, Cross-Layer, and Evolutionary.

## Critical: Complete File Output

When producing reconstructed Custom Instructions, optimized User Preferences, or any other deliverable, always output the complete content as a single, separately copyable unit. Never output diffs or partial sections.

## Model requirements

This Skill performs the most complex analysis in the catalog — combining Project audit (six-dimension Project Scorecard, seven anti-patterns) with Global audit (six-dimension Global Layer Scorecard) plus cross-layer alignment checks and evolutionary recommendations across all nine layers. Opus is recommended, with effort set to `high` or `xhigh` when the deployment context allows it. On Opus at default Adaptive effort, the multi-scorecard synthesis may compress — set effort higher for intelligence-sensitive audits.

On non-Opus models (Sonnet 4.6, Haiku 4.5 with extended thinking enabled), expect compressed evaluation steps, surface-level scoring on some dimensions, and reduced synthesis across the Project and Global layers. The Skill will execute and produce correctly-shaped output; users should weight findings accordingly. Haiku without extended thinking is not a supported deployment target for this Skill.

## When to Use This Skill

**Use when:**
- User wants a comprehensive audit of both a specific Project AND their global configuration
- User explicitly requests a "full stack audit" or "audit everything"
- A project audit reveals cross-layer issues that need full-stack visibility to resolve
- User has a mature Project and wants the premium evaluation covering all nine layers

**Do NOT use when:**
- User wants only a Project audit → rootnode-project-audit (if available)
- User wants only a global layer audit → rootnode-global-audit (if available)
- User wants to evaluate a single prompt → rootnode-prompt-validation (if available)
- User wants Project-scoped Memory optimization → rootnode-memory-optimization (if available)

## Information Requirements

**Required:**
- Project Custom Instructions (for the Project being audited)
- User Preferences text

**Recommended:**
- Knowledge file names and contents
- Project Memory contents
- Global Memory contents
- Active Style descriptions
- Installed Skills list with descriptions
- Configured MCP Connectors list
- Custom Instructions from 2+ additional Projects (enables Cross-Project Pattern Analysis and the full Evolutionary Recommendation Engine)

The audit produces value at every information level, but full-stack auditing is most valuable when both Project and global layers are visible. If only one side is provided, recommend the appropriate scoped audit instead (rootnode-project-audit or rootnode-global-audit if available).

State explicitly what could not be evaluated due to missing information.

## The Full Stack Audit Pipeline

Produce a comprehensive evaluation that identifies what's structurally wrong across all nine layers of the user's Claude environment and prescribes a single prioritized action plan they can work through sequentially — every finding traceable to quoted content, every cross-layer claim naming both conflicting elements. The method that reliably gets there: run the Project audit, the Global audit, the cross-layer alignment check, and the evolutionary recommendations engine, then merge all findings into the unified action plan. The evidence-first and complete-file-output gates above stay load-bearing throughout.

### Component 1: Project Audit

Run a full project-scoped evaluation on the provided Project.

**Parse:** Map the Project's architecture — identity, rules, knowledge files, modes, output standards, behavioral countermeasures, Memory configuration.

**Score the Project Scorecard** — six dimensions, each 1-5 with specific evidence. See `references/project-scorecard.md` for the condensed rubrics.

1. **Identity Precision** — Clear, appropriately-scoped identity producing distinctive expert output?
2. **Instruction Clarity** — Behavioral rules clear, non-contradictory, appropriately scoped?
3. **Knowledge & Context Architecture** — Knowledge files and Memory well-structured, routed, complementary?
4. **Mode Design** — Operational modes genuinely distinct with clear triggers?
5. **Output Standards** — Format and quality criteria specified and positioned effectively?
6. **Behavioral Calibration** — Claude-specific countermeasures present for domain-relevant failure modes?

**Run the Anti-Pattern Sweep** — check for seven structural patterns, citing specific evidence for each detection:
1. The Monolith (mixed content types in CI or single multi-purpose KF)
2. The Orphan File (KF not referenced or poorly routed in CI)
3. The Echo Chamber (same instruction in multiple locations, different wording)
4. The Phantom Conversation (conversational CI style reducing directive authority)
5. The Kitchen Sink (too many behavioral instructions, attention dilution)
6. The Misaligned Hierarchy (behavioral rules in KFs without CI delegation)
7. The Blurred Layers (Memory/KF content in wrong layer)

**Quality Criteria Evaluation** — five holistic criteria: Comprehensibility, Coherence, Efficiency, Evolvability, Instruction/Reference Separation. See `references/quality-criteria.md`.

### Component 2: Global Audit

Evaluate the account-wide layers.

**Parse Global Layers:** Map User Preferences, active Styles, Global Memory, installed Skills, configured Connectors.

**Score the Global Layer Scorecard** — six dimensions, each 1-5. See `references/global-layer-scorecard.md` for the condensed rubrics.

1. **Preference Precision** — Concise, universally applicable, free of domain-specific content?
2. **Style Coherence** — Styles work with, not against, other layers?
3. **Memory Hygiene** — Global Memory clean, no stale entries, no misplaced content?
4. **Skill Portfolio Fitness** — Skill set well-curated, no orphans, no collisions?
5. **Connector Alignment** — Connectors match Project needs?
6. **Cross-Layer Efficiency** — Context budget used efficiently, no redundant layering?

### Component 3: Cross-Layer Alignment Check

This is where full-stack visibility provides unique value. Evaluate all eight cross-layer failure modes across the complete set of layers. Some failure modes are only detectable when both Project and global layers are visible simultaneously.

For each detected failure mode, produce: layers involved, specific conflicting content, severity (Critical/Major/Minor), symptom, cause, fix, expected impact. See `references/cross-layer-checks.md`.

1. **Redundant Layering** (L1 + L6) — Same instruction in Preferences and Project CI.
2. **Silent Override** (L2 + L1/L6) — Style overriding Preferences or CI without awareness.
3. **Skill/Project Collision** (L4 + L6/L7) — Skill instructions conflicting with Project.
4. **Connector/Instruction Mismatch** (L5 + L6) — CI references unconfigured tools.
5. **Memory/Preference Confusion** (L3/L8 + L1) — Stable patterns not codified.
6. **Style/CI Tension** (L2 + L6) — Style formatting vs. Project output requirements.
7. **Cross-Project Duplication** (L6 across Projects) — Same instruction in 3+ Projects.
8. **Context Waste from Global Layers** (L1-5 combined) — Excessive global context overhead.

### Component 4: Evolutionary Recommendations

Run the Evolutionary Recommendation Engine — four pathways that strengthen the user's environment over time. The combined visibility of Project and global layers enables the most complete analysis. See `references/evolutionary-pathways.md`.

**Promotion** (Project → Global): Scan CIs from 3+ Projects for repeated patterns. Apply Universality Test. Draft Preferences text for candidates that pass. Requires 3+ Project CIs.

**Demotion** (Global → Project): Scan Preferences for domain-specific instructions. Apply Specificity Test. Identify which Projects benefit, which are harmed. Recommend placement in specific Project CIs.

**Codification** (Memory → Preferences/CI): Scan Memory for stabilized behavioral patterns. Apply Stability Test (persistence + intentionality). Determine destination (Preferences if universal, CI if project-specific). Draft instruction text.

**Skill Extraction** (KF → Skill): Scan knowledge files for portable procedural content. Apply Portability Test (task-triggered + context-independent + multi-project utility). Produce draft Skill description and extraction outline.

Each pathway executes independently based on available information. State which pathways were skipped and why. State confidence levels: high for promotion candidates with clear cross-project evidence, moderate for recent codification candidates, lower for inferred Skill extraction candidates.

### Output: The Unified Action Plan

After all four components complete, merge all findings into a single prioritized action plan. This is the most important deliverable — the user's single to-do list for improving their entire Claude environment.

**Output structure:**

1. **Project Audit Results** — Architecture map, Project Scorecard (six dimensions scored), anti-pattern sweep findings, quality criteria evaluation. Findings by severity (Critical / Major / Minor).

2. **Global Audit Results** — Global layer snapshot, Global Layer Scorecard (six dimensions scored), global-specific findings.

3. **Cross-Layer Alignment Report** — All detected failure modes with severity, evidence, and fixes. Highlight cross-layer issues visible only through full-stack analysis.

4. **Evolutionary Roadmap** — All four pathways organized as a prioritized evolution plan. Promotion candidates with drafted Preferences text. Demotion candidates with placement guidance. Codification candidates with destination and drafted text. Skill extraction candidates with design spec outlines.

5. **Unified Action Plan** — All changes from all components, merged and ordered by impact across all layers. The user should not need to cross-reference multiple sections to build their own plan. Each action item: what to change, in which layer, why, expected impact.

6. **Information Gaps** — What could not be evaluated and what additional input would enable those checks.

When the unified action plan includes reconstructed Custom Instructions, output the complete CI as a separately copyable unit with XML tags. When it includes optimized User Preferences, output the complete Preferences text as a separately copyable unit.

## Output Guidance

Write in prose by default. Use tables for scorecards, numbered lists for the action plan. The full-stack audit is the most comprehensive mode — it earns length, but every section must contain findings, not padding. If a component finds nothing notable, state that in one sentence and move on.

Before delivering, verify: Does every finding cite specific evidence? Does every fix specify the exact change and target layer? Are findings ordered by impact in the unified plan? Would the optimized versions pass their own audits? Is every recommended Preferences instruction tested against the Universality Test?

## Troubleshooting

**Audit is overwhelming — too many findings:** The unified action plan should handle this. If there are 20+ findings, group into three tiers: "Do now" (Critical findings), "Do next" (Major findings that improve daily quality), "Do later" (Minor optimizations). The user works through tiers sequentially.

**Project scores well but global layers are weak (or vice versa):** This is normal and expected. The full-stack audit's value is exposing exactly this mismatch. The cross-layer alignment check will likely reveal issues that neither scoped audit would catch alone.

**User provides only one side (Project without Preferences, or Preferences without Project):** Recommend the appropriate scoped audit instead. The full-stack audit's unique value comes from simultaneous visibility into both scopes. Running it with half the input produces a half-quality audit that the scoped Skills handle better.

**Evolutionary recommendations feel speculative:** Expected for some pathways. State confidence levels. The user decides which recommendations to act on. Promotion candidates with clear cross-project pattern evidence are highest confidence. Codification candidates from recent Memory patterns are moderate. Skill extraction from inferred portability is lowest.
