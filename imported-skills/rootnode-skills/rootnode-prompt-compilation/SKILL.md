---
name: rootnode-prompt-compilation
description: >-
  Builds complete, optimized Claude prompts and Project scaffolds from task
  descriptions. Use when building, designing, creating, or structuring a
  Claude prompt or system prompt. Trigger on: "build me a prompt," "compile a
  prompt for," "create a system prompt," "write a Claude prompt," "design a
  prompt for," "help me write a prompt," "scaffold a Claude Project," "design
  a Project for." Uses a four-stage methodology (Parse, Select, Construct,
  Validate) and a tested 5-layer architecture (Identity, Objective, Context,
  Reasoning, Output + Quality Control). In Project Mode, the Compiler is
  global-layer-aware — checks User Preferences, installed Skills, and MCP
  Connectors to avoid redundancy and flag gaps. Do NOT use for auditing
  existing prompts (use rootnode-prompt-validation if available) or
  diagnosing existing Projects (use rootnode-project-audit if available).
  Opus recommended; non-Opus models may produce less complete prompt
  construction.
license: Apache-2.0
metadata:
  author: rootnode
  version: "1.2.1"
  original-source: "PROMPT_COMPILER.md, MASTER_FRAMEWORK.md"
---

# Prompt Compilation

> **Calibration:** Tier 3, Opus-primary. See repository README for model compatibility.

Build complete, ready-to-use Claude prompts and Project scaffolds from task descriptions. This Skill transforms rough requirements into structured prompts using a tested 5-layer architecture and a four-stage assembly methodology.

When building Project scaffolds, you are aware of the user's global Claude configuration — User Preferences, installed Skills, and configured MCP Connectors. You use this awareness to avoid redundancy (not repeating Preferences in CI), design around overlaps (not creating knowledge files that duplicate installed Skills), and flag gaps (noting connector dependencies the user needs to configure). You read but do not modify global layers — that is the Optimizer's role.

## Critical: The No-Interrogation Principle

Do not ask a cascade of clarifying questions before building. Make reasonable defaults for anything the user did not specify, assemble the prompt, and flag the defaults in a brief note after the deliverable. The user adjusts specific elements rather than answering a questionnaire.

The one exception: when the request is genuinely ambiguous in a way that would produce fundamentally different outputs (e.g., "write a strategy document" could mean a 500-word executive brief or a 3000-word strategic memo), ask one targeted question to resolve the ambiguity. One question, not five.

## Critical: Complexity Calibration

Not every task needs the full 5-layer treatment. Match prompt complexity to task complexity.

**Simple tasks** (clear deliverable, single step, obvious format): Use 2-3 layers. A role statement, a clear objective, and an output format. Skip formal reasoning — a brief inline instruction is sufficient. Skip quality control when default behavior is adequate. Example: "Write a professional email declining a vendor's proposal."

**Medium tasks** (some ambiguity, multiple dimensions, meaningful format requirements): Use 4-5 layers. Full identity, objective, reasoning, and output. Add quality control if the task has known failure modes. Add context if the user provided situational detail. Example: "Evaluate three cloud providers for our migration."

**Complex tasks** (high stakes, multiple competing dimensions, deep analysis required): Use all 5 layers plus quality control with task-specific additions. Full context, detailed reasoning (or combined approaches), specific output structure with per-section length guidance, and behavioral countermeasures. Example: "Develop a market entry strategy for our AI product in the healthcare vertical."

## Model requirements

This Skill performs multi-stage construction across the four-stage pipeline (Parse, Select, Construct, Validate) and three modes (Prompt, Project, Prep), with decision trees spanning identity × reasoning × output × domain selection. In Project Mode, synthesis extends across User Preferences, installed Skills, and MCP Connectors. Opus is recommended, with effort set to `high` or `xhigh` when the deployment context allows it. On Opus at default Adaptive effort, block selection and validation steps may compress — set effort higher for intelligence-sensitive compilations.

On non-Opus models (Sonnet 4.6, Haiku 4.5 with extended thinking enabled), expect compressed selection logic, less specific block recommendations, and reduced cross-layer validation. The Skill will execute and produce correctly-shaped output; users should weight the resulting prompts accordingly. Haiku without extended thinking is not a supported deployment target for this Skill.

## The Four-Stage Workflow

Produce a complete, defensible prompt — identity, objective, context, reasoning, and output structure selected and assembled so the prompt yields the user's intended deliverable on first execution, with defaults flagged in a delivery note. The method that reliably gets there: parse the task, select the approaches, construct the prompt, validate the assembly. The stages are the path; the within-stage rules (XML wrapping, primacy-recency ordering, the validate-before-deliver checks) are the load-bearing gates that keep the output correct.

### Stage 1 — Parse

Extract from the user's description:

- **Core task:** What must be accomplished? (action + deliverable)
- **Task category:** Which domain? (strategic, technical, analytical, creative, research, comparative, operational, educational)
- **Audience:** Who reads the output? What expertise level?
- **Constraints:** What boundaries exist? (length, format, tone, domain limits, timeline)
- **Context signals:** What background is provided or implied? What is missing that would make the output generic?
- **Deliverable type:** What format should the final output take?

Where elements are missing, infer reasonable defaults from the task category and stated context. Record your defaults — you will flag them in the delivery note.

**Project Mode — Global Layer Awareness Inputs:**

When building a Project scaffold, check for available global layer information:
- **User Preferences text** — if visible in context, note behavioral instructions already established globally. These do not need to be repeated in the Project CI.
- **Installed Skills** — if the user mentions relevant Skills or if Skill descriptions are visible, note procedural capabilities already available. Knowledge files should not duplicate what an installed Skill provides.
- **Configured MCP Connectors** — if the user mentions integrations or connectors are visible, note available tool access. CI should reference configured connectors and flag dependencies on unconfigured ones.

Graceful degradation: if no global layer information is available, proceed without it. The scaffold will be self-contained, which is functional but may duplicate global configuration. Note in the compilation note that global awareness was not available and suggest the user check for redundancy with their Preferences after deployment.

### Stage 2 — Select

Choose approaches for each architectural layer based on the parsed task.

**Identity (Layer 1):** Match the task domain to the appropriate expert role. Customize the domain focus, seniority, and values to fit the specific task. If the task sits at the intersection of two domains, build a hybrid identity. Use the task category routing table below to start, then consult `references/five-layer-architecture.md` for detailed identity guidance and templates.

**Reasoning (Layer 4):** Match the task category to the appropriate reasoning family, then the specific variant. If the task spans categories, combine elements — but keep total reasoning steps to 5-7, leading with the dominant task type. See the reasoning selection logic below.

**Output (Layer 5):** Match the deliverable type to the appropriate output structure. Adjust section names, lengths, and constraints to fit the specific task. See the output selection logic below.

**Quality Control:** Start with the standard quality checks (accuracy, completeness, assumptions, pushback, actionability). Add task-specific checks based on domain. See the quality control selection logic below.

**Project Mode — Global-Layer-Aware Design Decisions:**

When global layer information is available, three design decisions change:

1. **CI behavioral rules defer to Preferences.** If the user's Preferences already establish a behavioral pattern (e.g., "be direct and concise"), do not repeat it in CI. Focus CI behavioral rules on project-specific calibration that goes beyond the universal defaults. If a Preference partially covers a needed behavior but the Project requires a more specific version, include the specific version in CI and note the relationship.

2. **Knowledge file architecture defers to installed Skills.** If an installed Skill covers procedural content the Project would otherwise need in a knowledge file (e.g., a code review Skill eliminates the need for a code review checklist KF), design the KF architecture around the Skill's coverage. The CI should reference the Skill's capability rather than duplicating it. The KF should provide the project-specific context the Skill needs (e.g., "our coding standards" rather than "how to review code").

3. **CI references configured connectors.** If the Project's tasks involve external tools that have configured connectors, reference them in CI: "Use the [connector] for [task]." If the Project depends on a connector that is not configured, flag it in the compilation note rather than building CI instructions that assume capabilities Claude doesn't have.

### Stage 3 — Construct

Assemble the complete prompt following these structural rules:

1. **Wrap every layer in XML tags.** Use clear, descriptive tag names: `<role>`, `<objective>`, `<context>`, `<reasoning>`, `<output_format>`, `<quality_standards>`.

2. **Order layers following the primacy-recency pattern.** Identity and critical constraints at the top (highest attention). Context and reasoning in the middle. Output format and quality standards at the bottom (closest to generation).

3. **Write the Objective (Layer 2) fresh for each task.** This is never a reused template because it must be specific to the task. Apply the clarity test: could two people read this and produce substantially different outputs? If yes, sharpen it.

4. **Include Context (Layer 3) only if the user provided specific situational information.** If context is thin, note in the delivery which specific context elements would most improve results. Do not fabricate context.

5. **Add behavioral countermeasures only when the task domain triggers known tendencies:**
   - Strategic/advisory tasks: counter agreeableness — add explicit pushback permission.
   - Analytical/research tasks: counter excessive hedging — add decisiveness instruction.
   - Long-form tasks: counter verbosity drift — add a specific length constraint.
   - Tasks that could produce lists: add a prose instruction if prose is more appropriate.

6. **Audit before finalizing.** Every instruction must earn its place. Remove anything included "just in case."

### Stage 4 — Validate

Before delivering, check the assembled prompt:

1. Objective passes the clarity test (unambiguous success criteria).
2. No conflicting instructions (e.g., "be concise" alongside a 1500-word output specification).
3. Reasoning steps are specific to the task type, not generic "think carefully."
4. Output format specifies per-section length, not just total length.
5. Every instruction earns its place — nothing included "just in case."
6. If context is thin, the prompt still works (produces more generic output, but does not fail).
7. The prompt can be copied directly into Claude and used as-is.

**Global Layer Alignment (Project Mode, when global layer information is available):**

| Check | Failure Signal | Fix |
|---|---|---|
| CI does not duplicate User Preferences | Behavioral instructions semantically equivalent to Preferences content | Remove from CI; note in Global Layer Advisory |
| Knowledge files do not duplicate installed Skills | KF covers procedural content an installed Skill provides | Remove or reduce the KF; reference Skill coverage in architecture note |
| Connector dependencies flagged | CI references tools requiring unconfigured connectors | Flag in CI and in Global Layer Advisory |
| Promotion candidates identified | CI contains behavioral instructions that appear universally useful | Note in Global Layer Advisory as potential Preference candidates |

Fix any issues found. Deliver only a clean prompt.

## The 5-Layer Architecture (Overview)

Every prompt is built from five architectural layers. Each has a specific job:

| Layer | Purpose | Always Required? |
|---|---|---|
| **Layer 1 — Identity** | WHO Claude is — expert role, seniority, values | Yes, even if brief |
| **Layer 2 — Objective** | WHAT must be accomplished — task, success criteria, audience | Yes |
| **Layer 3 — Context** | WHAT Claude needs to know — situation, constraints, prior decisions | Only if user provides it |
| **Layer 4 — Reasoning** | HOW Claude should think — task-specific analytical steps | Medium and complex tasks |
| **Layer 5 — Output** | WHAT the deliverable looks like — structure, length, format | Yes for structured output |
| **Quality Control** | Cross-cutting standards — accuracy, pushback, consistency | Medium and complex tasks |

For detailed layer descriptions, templates, ready-to-use approaches for each layer, the Context Engineering Toolkit, and global layer interaction guidance for Project Mode, see `references/five-layer-architecture.md`.

## Task Category Routing

Use this quick-reference to route tasks to the right approaches. When a task matches multiple categories, lead with the dominant one and fold in elements from the secondary.

**Strategic / Advisory** — Identity: Strategic Advisor or Product Strategist. Reasoning: Market and Competitive Strategy, Resource Allocation, or Change and Transformation. Output: Executive Brief, Strategic Memo, or Decision Matrix.

**Technical / Engineering** — Identity: Technical Architect. Reasoning: System Design, Debugging and Incident Analysis, or Migration and Transition. Output: Technical Design Document or Implementation Plan.

**Analytical / Evaluative** — Identity: Research Synthesist or Financial Analyst. Reasoning: General Analysis, Root Cause Diagnosis, or Risk Assessment. Output: Research Summary, Post-Mortem, or Decision Matrix.

**Creative / Generative** — Identity: Communications Strategist or custom. Reasoning: Concept Development, Messaging and Narrative, or Solution Ideation. Output: custom, matched to deliverable type.

**Research / Synthesis** — Identity: Research Synthesist. Reasoning: Evidence Synthesis, Landscape Scan, or Gap Analysis. Output: Research Summary or Competitive Analysis.

**Comparative / Decision** — Identity: matched to domain. Reasoning: Option Evaluation, Vendor/Tool Selection, or Prioritization. Output: Decision Matrix or Executive Brief.

**Operational / Process** — Identity: Operations Designer. Reasoning: General Analysis or custom. Output: Process Documentation, Implementation Plan, or Stakeholder Update.

**Educational / Explanatory** — Identity: Educator/Explainer. Reasoning: light, focused on progressive complexity. Output: custom, matched to format.

## Selection Decision Trees

### Identity Selection

1. What domain is the task in? Match to the closest expert role from the routing table.
2. Does the task sit at an intersection of two domains? Build a hybrid identity combining both.
3. Seniority calibration: Expert audience → use "principal" or "world-class" (more nuanced, assumption-challenging). Audience needs guidance → reduce seniority (more explanatory). Default → "senior."
4. No role fits? Build custom: `[SENIORITY] [ROLE] with expertise in [DOMAINS]. Approaches problems by [REASONING STYLE]. Prioritizes [VALUE 1] over [VALUE 2]. [ONE BEHAVIORAL SENTENCE].`

### Reasoning Selection

1. Identify the primary task shape:
   - Evaluate something that exists → Analytical family (General Analysis, Root Cause Diagnosis, Risk Assessment)
   - Plan or decide a strategic direction → Strategic family (Market Strategy, Resource Allocation, Change and Transformation)
   - Generate something new → Creative family (Concept Development, Messaging and Narrative, Solution Ideation)
   - Build or fix a technical system → Technical family (System Design, Debugging, Migration and Transition)
   - Synthesize information across sources → Research family (Evidence Synthesis, Landscape Scan, Gap Analysis)
   - Compare options and recommend → Comparative family (Option Evaluation, Vendor Selection, Prioritization)
2. Select the specific variant within the family that fits the task shape.
3. Task spans categories? Combine elements from both families. Keep total steps to 5-7. Lead with the dominant type.

### Output Selection

1. Match the deliverable type: leadership decision → Executive Brief; architecture proposal → Technical Design Document; evidence synthesis → Research Summary; project plan → Implementation Plan; structured comparison → Decision Matrix; market positioning → Competitive Analysis; incident/project analysis → Post-Mortem; status report → Stakeholder Update; strategy recommendation → Strategic Memo; workflow or SOP → Process Documentation.
2. No match? Build custom with named sections, per-section length, total length, tone, and audience.
3. Calibration checks: Does it specify per-section length? Does it match the audience? Is the total length realistic?

### Quality Control Selection

1. Always include the standard checks: accuracy, completeness, assumptions, pushback, actionability.
2. Add task-specific checks: Strategic work → internal consistency. Technical work → edge case identification. Research work → source discrimination. Creative work → distinctiveness. Financial work → assumption transparency. Advisory work → agreeableness counter.
3. Add behavioral countermeasures based on likely tendencies: Task invites agreement → add pushback permission. Task invites hedging → add decisiveness instruction. Long-form task → add length constraint. Task could produce lists → add prose instruction if prose is better.

## Delivery Standards

### Prompt Mode Delivery

1. Present the complete prompt in a single, clean code block with XML tags. No interleaved commentary.
2. Follow with a compilation note (3-7 sentences) covering: which approaches were selected and why, what defaults were assumed, and what the user should customize to improve results.
3. Do not explain what each section does — the user can read it.
4. Do not add disclaimers about prompt engineering being iterative.

### Project Mode Delivery

When the user needs a full Claude Project scaffold (multiple related tasks, ongoing usage, reference material needed across conversations), deliver each file as a separately copyable unit. Do not combine the Custom Instructions and knowledge files into a single document — the user will paste each into their Project individually.

1. Present the complete Custom Instructions in its own code block, using XML tags for all section boundaries (`<identity>`, `<core_rules>` or `<core_instructions>`, `<knowledge_file_guide>` or `<knowledge_routing>`, `<operational_modes>`, `<output_standards>`, and any other top-level sections). Do not use markdown headers (##) for section boundaries in Custom Instructions. The user should be able to copy this code block directly into the Custom Instructions field.
2. Present each knowledge file in its own code block, preceded by the filename and a one-line purpose statement. Each file's code block must be independently copyable — the user pastes it as a new knowledge file. For critical files, write the full content. For reference files that depend on the user's domain, provide the structural outline with section descriptions and content guidance.
3. Follow with an architecture note explaining key decisions.
4. Be explicit about what the user needs to supply vs. what you have provided.

**Global Layer Advisory (Project Mode only, when global layer information is available):**

After the architecture note, append a brief Global Layer Advisory (3-5 sentences) covering:
- **Preference redundancies avoided** — behavioral instructions intentionally omitted from CI because User Preferences already establish them. This tells the user why certain expected instructions are absent.
- **Skill overlaps designed around** — knowledge file decisions informed by installed Skills. This explains why certain KFs are leaner than expected or absent.
- **Connector dependencies** — MCP Connectors the Project relies on, plus any missing connectors the user needs to configure.
- **Promotion candidates** — behavioral instructions included in this Project's CI that might belong in User Preferences if the user finds them universally useful after burn-in. This seeds the evolutionary loop.

The advisory is informational — the Compiler does not modify global layers. If the user wants to act on promotion candidates or Preference optimization, recommend rootnode-global-audit if available.

For Project Mode, the same four stages apply but expand in scope: Parse extracts project purpose, task types, knowledge requirements, audience, and scope boundaries. Select designs identity, operational modes, knowledge file architecture, and Custom Instructions structure. Construct builds the full scaffold with primacy-recency ordering and XML tags. Validate checks comprehensibility, coherence, efficiency, evolvability, and format compliance (XML tags in Custom Instructions, each file separately copyable).

### In All Modes

- Write in direct, professional prose. Not bullet points unless genuinely parallel items.
- Be decisive about recommendations. If one approach is clearly right, say so — do not present it as "one option among many."
- If the user's request has a flaw or a better framing, state it before building. Then build what they actually need.

## Prep Mode

When the user needs help developing a task description before compilation, shift into preparation mode. Two paths:

**Generator:** Walk the user through the highest-leverage dimensions to produce a structured task description. Ask 1-2 batched questions, not a list of six. Dimensions (in leverage order): Task and Deliverable, Audience and Stakes, Situational Context, Constraints, Success Criteria, Reusability Intent. Batch related dimensions into the same question. Complete in 2-4 turns.

**Evaluator:** Score an existing task description against the six dimensions above (each 1-5) to identify gaps. Deliver scorecard results, 2-3 improvement priorities, and a revised version when any dimension scores below 3.

Apply the same No-Interrogation Principle: batch dimensions, drop those already covered, complete in minimal turns.

## Troubleshooting

**Output is generic, could apply to any company.** Context is too thin. Flag in your compilation note which specific context elements would most improve results: numbers, constraints, prior decisions.

**Analysis is shallow, states the obvious.** Reasoning layer is missing or generic. Replace "think step by step" with task-specific analytical steps that direct attention to the right dimensions.

**Claude agrees with a flawed premise.** Quality control layer does not include pushback permission. Add: "If the request contains a flawed premise, challenge it before proceeding."

**Recommendations contradict each other.** No internal consistency check. Add a verification step requiring Claude to check that recommendations are mutually compatible.

**Output keeps growing across turns.** No length constraint combined with verbosity drift. Specify target length in the output layer. Restate when asking follow-up questions.

**Prompt is bloated — instructions that add no value.** Failed the "every instruction earns its place" audit. Remove sections included "just in case." A lean prompt with five precise instructions outperforms a bloated one with twenty vague ones.

## Examples

For 2-3 annotated end-to-end compilation examples showing the full workflow from task description to finished prompt at different complexity levels, see `references/compilation-examples.md`.
