# Skills Spec Reference

This document is the authoritative reference for the Agent Skills specification as of March 2026. It is extracted from Anthropic's official "Complete Guide to Building Skills for Claude" and supplemented with patterns observed in production Skills (Anthropic's public skills, partner skills, and the skill-creator).

---

## What Is a Skill

A Skill is a set of instructions — packaged as a simple folder — that teaches Claude how to handle specific tasks or workflows. Skills are one of the most powerful ways to customize Claude for specific needs. Instead of re-explaining preferences, processes, and domain expertise in every conversation, Skills let you teach Claude once and benefit every time.

Skills work identically across Claude.ai, Claude Code, and API. Create a Skill once and it works across all surfaces without modification, provided the environment supports any dependencies the Skill requires.

---

## Folder Structure

```
your-skill-name/
├── SKILL.md          # Required — main skill file
├── scripts/          # Optional — executable code (Python, Bash, etc.)
├── references/       # Optional — documentation loaded as needed
└── assets/           # Optional — templates, fonts, icons used in output
```

### Critical Rules

**SKILL.md naming:** Must be exactly `SKILL.md` (case-sensitive). No variations accepted (`SKILL.MD`, `skill.md`, etc.).

**Skill folder naming:** Use kebab-case only. No spaces, no underscores, no capitals.
- Correct: `notion-project-setup`
- Wrong: `Notion Project Setup`, `notion_project_setup`, `NotionProjectSetup`

**No README.md:** Do not include `README.md` inside the skill folder. All documentation goes in SKILL.md or `references/`. A repo-level README for human visitors is separate from the skill folder itself.

**Skills named with "claude" or "anthropic" are reserved** and will be rejected.

---

## Skill Subdirectory Structure

The Skill folder is the unit of distribution. Subdirectories within it carry layered content that the methodology layer (SKILL.md) invokes or references on demand. The subdirectory taxonomy:

```
your-skill-name/
├── SKILL.md              # Required — methodology layer (frontmatter + body)
├── references/           # Optional — methodology depth (loaded on demand)
├── scripts/              # Optional — Python tooling (executed on demand)
├── agents/               # Optional — subagent prompts (invoked when subagent
│                         #            execution is available)
├── eval-viewer/          # Optional — HTTP-served review UI (Tier A only)
└── assets/               # Optional — templates, fonts, icons used in output
```

Each subdirectory has a defined purpose. Mixing content across subdirectories produces a Skill that is hard to reason about and hard to evolve.

### references/

Methodology depth that supports the workflow in SKILL.md but does not need to be loaded at activation. SKILL.md references each file with explicit "when to read" guidance; the model loads the file only when its scope is in play. This is the second level of progressive disclosure (per "Progressive Disclosure Model" below). Reference files over ~300 lines should carry a table of contents at the top.

No nested subdirectories. The flat layout under `references/` is part of the spec — nested directories complicate model navigation and break the "load on demand" pattern.

### scripts/

Executable code (typically Python; Bash and other interpreted languages permitted). Scripts execute without being loaded into context — the model invokes them as tool calls and the output flows back without the script's source ever entering the conversation. This is the third level of progressive disclosure for executable content.

Script invocation pattern: SKILL.md or a reference file documents what the script does, when to invoke it, and what arguments it takes. The model invokes the script via the execution surface (Bash tool in CC; Code Interpreter in CP/Claude.ai). The script reads inputs (typically files in the working directory or stdin), runs its logic, writes outputs (typically files), and prints a summary to stdout. The model parses stdout and continues the workflow.

When `scripts/` is present, include `__init__.py` (zero-byte) so the directory functions as a Python package — required for relative imports between scripts. A shared `utils.py` is the conventional location for parsing helpers and other cross-script utilities.

### agents/

Subagent prompt files. Each `.md` file in `agents/` is a complete subagent prompt — system prompt + role definition + output schema — that can be invoked as a Task subagent in environments that support subagent execution (CC-side currently; not available in CP). The files are not loaded into the parent conversation; they are passed to the subagent at spawn time.

Subagent prompt invocation pattern: SKILL.md or a reference file documents which subagent to invoke for which task (grader, comparator, analyzer per the rootnode skill-builder convention). The methodology layer invokes the subagent via the Task tool; the subagent runs in isolated context with its own prompt loaded; the subagent returns structured output that the parent reads. This isolates context-heavy or judgment-heavy work from the parent conversation.

Subagent availability is environment-dependent. Skills with `agents/` should declare tier compatibility (Tier A requires subagents available; Tier B/C falls back to inline procedures or analytical reasoning). See `references/multi-environment-adaptation.md` for the operational model.

### eval-viewer/

Optional. HTTP-served review interface for browsing eval runs and collecting feedback. Used by Skills with empirical evaluation pipelines (e.g., behavioral validation, version comparison) where the operator wants an interactive view of run outcomes rather than reading raw JSON. Typical contents: a Python generator (`generate_review.py`) and an HTML template (`viewer.html`). The generator scans a workspace for runs, embeds output data into the HTML template, and serves the page via a tiny HTTP server with feedback auto-save.

Tier compatibility: Tier A only (requires Python + browser). Skills with `eval-viewer/` document the subdirectory's purpose and tier compatibility in their tooling-layer reference.

### assets/

Static templates, fonts, icons, and other artifacts that the Skill or its scripts reference but that are not themselves methodology, code, or subagent content. Assets are not the same as references — references are markdown content the model reads; assets are binary or template files the model references but does not parse.

---

## Executable Layer in Skills

A Skill that includes only `SKILL.md` and `references/` is a **methodology-only** Skill — pure prose, loaded into context when relevant, applied by the model as instructions. A Skill that adds `scripts/`, `agents/`, or `eval-viewer/` is a **multi-modality** Skill — methodology plus executable tooling that the methodology invokes.

The executable layer extends what the Skill can do without expanding what the Skill loads into context. A 200-line Python script executes for tens of seconds, produces a structured output, and never burns context budget; the same logic written as natural-language instructions in SKILL.md would consume thousands of tokens, run unreliably (model judgment vs. deterministic code), and pollute the conversation with intermediate state. Executable layer for deterministic logic; methodology layer for judgment-heavy reasoning.

### When to use scripts vs. methodology

Push logic into `scripts/` when:

- The logic is deterministic — given the same input, it always produces the same output. Validation, schema checking, parsing, packaging, format conversion.
- The logic is computational — counting tokens, computing statistics, running diff analyses, generating reports.
- The logic is repetitive — invoked many times per session, where the per-invocation context cost compounds.
- The logic interfaces with external state — file system operations, HTTP requests, structured data writes.

Keep logic in methodology (SKILL.md / references) when:

- The logic is judgment-heavy — applying a rubric, weighing tradeoffs, deciding between approaches.
- The logic is one-shot — executed once per Skill invocation; the per-invocation context cost is amortized.
- The logic depends on context the model already has — requires reasoning about the conversation, the user's intent, or the surrounding code.

### When to use subagents vs. inline procedures

Push procedures into `agents/` when:

- The procedure requires isolated context — graders need to evaluate output against rubrics without parent-conversation context bleeding into their judgment.
- The procedure produces structured output that the parent consumes — schema-defined JSON, scored rubric outputs, analyzer findings.
- The procedure runs many times per session — keeping each run in isolated context prevents context contamination across runs.

Keep procedures inline when:

- The procedure runs once and the model has the context it needs — the cost of subagent setup exceeds the value of context isolation.
- Subagent execution is not available in the deployment environment — Tier B/C falls back to inline procedures.

### Tier compatibility for executable content

Skills with executable content document per-component tier compatibility:

- **Tier A** (subagents + runnable environment available): Full executable layer — scripts run, subagents invoked, eval-viewer served.
- **Tier B** (runnable environment, no subagents): Scripts run; subagent procedures fall back to inline; eval-viewer typically unavailable (depends on browser surface).
- **Tier C** (neither): Scripts and subagents both unavailable; methodology layer applies analytical fallback.

The tier model is canonical at `root_AGENT_ENVIRONMENT_ARCHITECTURE.md §4.12` and detailed in `references/multi-environment-adaptation.md`. Skills with executable layers reference the tier model rather than re-documenting it.

### The methodology-tooling boundary

The methodology layer (SKILL.md, references/) is **content the model reads and applies as judgment**. The tooling layer (scripts/, agents/, eval-viewer/) is **content the model invokes as tools**. The two layers compose — methodology decides when to invoke tooling; tooling produces structured artifacts that methodology then interprets. Neither layer subsumes the other; mixing them produces a Skill that is hard to maintain (a SKILL.md that embeds executable logic) or hard to invoke (scripts that require methodology-grade judgment to run correctly).

The boundary is most legible in the file structure: scripts/ holds code, references/ holds prose, SKILL.md orchestrates both. A reader of the Skill folder can tell the layers apart without reading the contents.

---

## YAML Frontmatter

The YAML frontmatter is how Claude decides whether to load a Skill. This is the first level of progressive disclosure — always loaded in Claude's system prompt for all enabled skills.

### Required Fields

```yaml
---
name: your-skill-name
description: What it does. Use when user asks to [specific phrases].
---
```

**`name`** (required):
- Kebab-case only
- Max 64 characters
- No spaces or capitals
- Must match folder name
- No leading or trailing hyphens

**`description`** (required):
- Max 1024 characters
- MUST include BOTH: what the skill does AND when to use it (trigger conditions)
- No XML angle brackets (`<` or `>`) — security restriction, as frontmatter appears in Claude's system prompt
- Include specific task phrases users would actually say
- Mention file types if relevant

### Optional Fields

**`license`**: Use if making skill open source. Common values: `MIT`, `Apache-2.0`.

**`compatibility`**: 1-500 characters. Indicates environment requirements (intended product, required system packages, network access needs).

**`metadata`**: Any custom key-value pairs. Suggested: `author`, `version`, `mcp-server`.

```yaml
metadata:
  author: rootnode
  version: "1.0"
  original-source: AUDIT_FRAMEWORK.md
  discipline_post: phase-30
```

**`metadata.discipline_post`** (rootnode build convention, required from skill-builder v2.x onward): Marks the build-discipline phase under which the Skill was produced. Value `phase-30` indicates the Skill was built under the Phase 30 audit-artifact discipline (placement note + conditional promotion provenance + conditional AP warnings). The field is not optional for new builds — it is part of D1 spec compliance going forward; Skills built without it fail D1. Future phases may extend the enum (`phase-31a`, etc.); the field carries the most recent applicable phase. The field's absence on a Skill signals it predates the discipline. See `root_SKILL_BUILD_DISCIPLINE.md` §4.6 for the canonical convention.

---

## Progressive Disclosure Model

Skills use a three-level loading system to minimize token usage while maintaining specialized expertise:

### Level 1 — Metadata (Always Loaded)
The YAML frontmatter (`name` + `description`) is always present in Claude's system prompt for all enabled skills. This is approximately 100 words. It provides just enough information for Claude to know when each skill should be used without loading the full body.

### Level 2 — SKILL.md Body (Loaded on Activation)
The full SKILL.md body is loaded when Claude determines the skill is relevant to the current task. Contains the complete instructions and guidance. Recommended: under 500 lines, under ~5000 tokens.

### Level 3 — Linked Files (Loaded on Demand)
Additional files in `scripts/`, `references/`, and `assets/` directories. Claude navigates to and reads these only as needed. Scripts can execute without being loaded into context. Reference files are read into context when Claude needs detailed documentation.

### Key Patterns

- Keep SKILL.md under 500 lines. If approaching this limit, add hierarchy and clear pointers to reference files.
- Reference files clearly from SKILL.md with guidance on when to read them.
- For large reference files (>300 lines), include a table of contents at the top.
- Domain organization: when a skill supports multiple variants, organize references by variant so Claude reads only the relevant one.

```
cloud-deploy/
├── SKILL.md (workflow + selection logic)
└── references/
    ├── aws.md
    ├── gcp.md
    └── azure.md
```

---

## Writing Effective Descriptions

The description field is the activation trigger. Claude decides whether to load a Skill based almost entirely on this field. Getting this right is the single most important task.

### Structure

```
[What it does] + [When to use it] + [Key capabilities]
```

### Good Examples

```yaml
# Specific and actionable
description: Analyzes Figma design files and generates developer handoff documentation. Use when user uploads .fig files, asks for "design specs", "component documentation", or "design-to-code handoff".

# Includes trigger phrases
description: Manages Linear project workflows including sprint planning, task creation, and status tracking. Use when user mentions "sprint", "Linear tasks", "project planning", or asks to "create tickets".

# Clear value proposition
description: End-to-end customer onboarding workflow for PayFlow. Handles account creation, payment setup, and subscription management. Use when user says "onboard new customer", "set up subscription", or "create PayFlow account".
```

### Bad Examples

```yaml
# Too vague — will never activate
description: Helps with projects.

# Missing triggers — Claude doesn't know when to use it
description: Creates sophisticated multi-page documentation systems.

# Too technical, no user triggers
description: Implements the Project entity model with hierarchical relationships.
```

### Undertriggering Bias

Claude currently has a tendency to undertrigger Skills — to not use them when they would be useful. To combat this, make descriptions slightly "pushy." Include trigger phrases that cover both explicit and implicit user requests. For example, instead of just listing the primary function, add phrases like "Use this skill whenever the user mentions [X], [Y], or [Z], even if they don't explicitly ask for [specific term]."

### Negative Triggers

When a Skill risks overtriggering, add explicit negative triggers:

```yaml
description: Advanced data analysis for CSV files. Use for statistical modeling, regression, clustering. Do NOT use for simple data exploration (use data-viz skill instead).
```

---

## Writing the SKILL.md Body

### Recommended Structure

```markdown
---
name: your-skill
description: [What + When + Capabilities]
---

# Your Skill Name

## Instructions

### Step 1: [First Major Step]
Clear explanation of what happens.
[Add more steps as needed]

## Examples

### Example 1: [Common Scenario]
User says: "[trigger phrase]"
Actions:
1. [Step]
2. [Step]
Result: [What success looks like]
[Add more examples as needed]

## Troubleshooting

**Error: [Common error or failure mode]**
Cause: [Why it happens]
Solution: [How to fix]
```

### Writing Principles

**Be specific and actionable.** Prefer concrete instructions over vague guidance.
- Good: `Run python scripts/validate.py --input {filename} to check data format.`
- Bad: `Validate the data before proceeding.`

**Use imperative form.** Direct instructions, not suggestions.

**Include error handling.** Document common failure modes and their solutions.

**Reference bundled resources clearly.** When referring to files in `references/`, state what the file contains and when to consult it.

**Critical instructions at the top.** Put the most important rules and behaviors early in the document. Use `## Important` or `## Critical` headers for must-follow rules.

---

## Distribution

### Current Model (March 2026)

**Individual users:**
1. Download the skill folder
2. Zip the folder (if needed)
3. Upload to Claude.ai via Settings > Capabilities > Skills
4. Or place in Claude Code skills directory

**Organization-level skills:**
- Admins can deploy skills workspace-wide
- Automatic updates
- Centralized management

**API access:**
- `/v1/skills` endpoint for listing and managing skills
- Add skills to Messages API requests via the `container.skills` parameter
- Works with the Claude Agent SDK for building custom agents
- Requires the Code Execution Tool beta

**GitHub distribution (recommended):**
- Public repo for open-source skills
- Clear repo-level README with installation instructions (separate from skill folders)
- Example usage and screenshots
- Link to related documentation

### Open Standard

Agent Skills is published as an open standard — portable across tools and platforms. Skills designed for specific platform capabilities can note this in the `compatibility` field.

---

## Testing Criteria

### Triggering Tests
- Triggers on obvious tasks (direct requests matching the skill's domain)
- Triggers on paraphrased requests (same intent, different wording)
- Does NOT trigger on unrelated topics

### Functional Tests
- Valid outputs generated
- Error handling works
- Edge cases covered

### Performance Comparison
- Without skill: how many messages, tool calls, tokens, errors?
- With skill: improvement on all dimensions?

### Quantitative Targets (Aspirational)
- 90%+ trigger accuracy on relevant queries
- 0 failed API calls per workflow
- Consistent results across sessions

### Debugging Activation

Ask Claude: "When would you use the [skill name] skill?" Claude will quote the description back. Adjust based on what's missing.

### Behavioral Validation (D9)

Canonical source: `root_SKILL_BUILD_DISCIPLINE.md` §3.9 D9. The text below is reproduced verbatim from the canonical KF (heading style and list formatting adapted for integration; pass conditions, skip condition, and classification preserved exactly).

**Check.** Has the Skill been tested against at least one adversarial scenario where Claude would fail without it? The dimension assesses the Skill's behavioral effectiveness, not its document architecture (D1–D8 cover architecture).

**Three pass conditions** (all must be met OR the skip condition must apply):

1. **Pressure scenario documented.** At least one scenario is described where Claude, without the Skill loaded, would produce incorrect behavior that the Skill is designed to prevent. The scenario should target the Skill's core discipline — the failure mode it exists to stop.
2. **Baseline failure confirmed or credibly expected.** The scenario has been run against a subagent without the Skill (RED), or the expected failure is credible based on documented Claude behavioral tendencies (cite the specific tendency from the 10-tendency taxonomy if applicable).
3. **Compliance with Skill confirmed or credibly expected.** The scenario has been re-run with the Skill loaded (GREEN), or compliance is credible based on the Skill's instruction specificity and the countermeasure's alignment with the identified tendency.

**Skip condition.** The Skill is reference-only, data-carrying, or configuration-driven — it has no behavioral compliance to test. Examples: context carriers (drayline-ecosystem), profile schemas, block libraries used by other Skills. Mark as `D9: SKIPPED — no behavioral compliance surface` with one-sentence justification.

**Classification: RECOMMENDED, not REQUIRED.** Full RED-GREEN-REFACTOR pressure testing requires subagent access (CC-side only) and is therefore not feasible for CP-only Skill validation. Skills that pass D1–D8 but lack D9 validation are shippable; D9 adds confidence but its absence is not a build-blocker.

**Pass evidence.** Name the pressure scenario, the expected failure mode, and the validation result (tested or credibly expected). For tested scenarios, cite the session or test artifact. For credibly-expected scenarios, cite the behavioral tendency and explain why the Skill's countermeasure formulation addresses it.

**Disposition.** Advisory for v2.1. Future evolution may tighten to REQUIRED for discipline-enforcing Skills (tendencies #1–#10 countermeasures) while keeping RECOMMENDED for procedural and reference Skills.

**Source pattern.** The pressure-testing methodology was identified during the CC ecosystem analysis (May 2026) from Superpowers v5.1.0's `writing-skills` skill, which applies TDD to skill authoring — write pressure test scenarios with subagents, watch Claude fail without the skill, write the skill to address observed rationalizations, verify compliance. The Meincke et al. (2025, N=28,000) finding that persuasion techniques more than doubled LLM compliance rates (33% → 72%) provides the research grounding for why countermeasure language design matters enough to validate empirically.

---

## Common Problems

**Skill doesn't trigger:** Description too vague. Add specific trigger phrases and user intent language. Check that the description includes both what AND when.

**Skill triggers too often:** Description too broad. Add negative triggers, be more specific about scope.

**Instructions not followed:** Instructions may be too verbose (keep concise, use lists), buried (critical instructions at top), or ambiguous (replace vague language with specific checks).

**Large context issues:** SKILL.md too large. Move detailed docs to `references/`. Keep SKILL.md under 500 lines / ~5000 tokens.

---

## Skill Categories

Anthropic identifies three common use case categories:

**Category 1 — Document & Asset Creation:** Creating consistent, high-quality output (documents, presentations, apps, designs, code). No external tools required — uses Claude's built-in capabilities. Key techniques: embedded style guides, template structures, quality checklists.

**Category 2 — Workflow Automation:** Multi-step processes benefiting from consistent methodology. Key techniques: step-by-step workflows with validation gates, templates, iterative refinement loops.

**Category 3 — MCP Enhancement:** Workflow guidance enhancing tool access from an MCP server. Key techniques: coordinated multi-tool sequences, embedded domain expertise, context provision, error handling.
