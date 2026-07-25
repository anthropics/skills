---
name: workflow-skill-creator
description: >
  Distills a completed user workflow or interaction into a reusable agent
  skill. Use when the user asks to turn their workflow, interaction, or
  multi-step process into a skill, or when they say "make this a skill",
  "create a skill from what we just did", "package this workflow" or similar.
  Do not use for creating skills from scratch without an existing workflow
  (use a generic skill-creator for that).
---

# Workflow-to-Skill Distiller

Turns a completed workflow into a reusable agent skill. Specifically, this skill
extracts patterns from an interaction or workflow that **already happened** and
packages them.

> [!CAUTION] **You MUST complete Phase 1 (Brainstorming) before writing any code
> or SKILL.md content.** Skipping brainstorming produces skills that are either
> too rigid or too vague. The brainstorming conversation is the most important
> part of this process.

## Phase 1: Brainstorming (MANDATORY)

Have an **iterative back-and-forth conversation** with the user. Do NOT ask all
questions at once. Pick 2-3 relevant questions per round from the bank below,
refine your understanding, and ask follow-ups.

### Round 1: Understand the Workflow

Start by summarizing what you observed from the workflow, then ask:

1.  "Here's my understanding of the workflow: [summary]. Is this accurate? What
    would you change?"
2.  "What are the expected inputs and outputs for this workflow?"
3.  "How often do you expect to run this workflow? Is it recurring or one-off?"

### Round 2: Flexibility and Error Handling

For each step identified in the workflow, determine its rigidity:

1.  "For [step X], if the primary approach fails (e.g., API down, no results),
    should the agent: (a) ask you for guidance, (b) try alternative approaches
    automatically, or (c) fail loudly with an error?"
2.  "Are there any steps where the exact method matters (e.g., must use a
    specific database), vs. steps where any reasonable approach is fine?"
3.  "Should the skill handle edge cases silently or surface them to the user?"

### Round 3: Dependencies and Resources

Before asking these questions, check which of your installed skills overlap with
the workflow. If an existing skill from the science bundle covers a step, the
new skill **MUST** reference it — do not offer a self-contained option.

1.  "I noticed the workflow uses functionality covered by [existing skill X,
    skill Y]. The new skill will reference these rather than reimplementing
    them. Are there any other tools or skills you'd like me to incorporate?"
2.  "Are there any API rate limits I should be aware of for services used in
    this workflow that aren't already covered by an existing skill?"
3.  "Are there specific files that provide important scientific context for
    creating this skill? For example: API documentation, reference papers,
    example datasets, or domain-specific notes. If so, please share them and I
    will incorporate their content into the skill's reference materials."

### Round 4: Scope and Shape

1.  "Our workflow covered [X, Y, Z]. Should I distill all of these into the
    skill, or is there additional functionality that's important to include?
    Conversely, should any of these be left out?"
2.  Determine whether the skill needs any code. If any step involves calling an
    API, processing data, reading/writing files, or computing results, the skill
    **needs code** and you should default to the CLI pattern. Only use a
    text-only instruction skill when every step is purely about reasoning,
    coordinating existing tools, or following a written protocol with no
    programmatic work at all. Confirm your assessment with the user in plain
    language:
    -   If code is needed: "Some of these steps involve [fetching data from an
        API / processing files / computing results], so I'll create a helper
        script that the agent can run for you. The script will have simple
        commands like `search`, `fetch`, `analyze`, etc. — you won't need to
        write any code yourself. Does that sound right?"
    -   If no code is needed: "This workflow is entirely about following a set
        of steps and using existing tools — no new code is needed. I'll write it
        as a set of clear instructions the agent follows. Does that sound
        right?"
3.  If a helper script will be created: "I'm thinking the script should have
    these commands: [proposed commands in plain English, e.g. 'search for
    proteins', 'fetch results', 'compare sequences']. What would you add or
    change?"
4.  "What should the skill be called? Proposed name: `[suggestion]`."

### Round 5: Testing (Optional)

1.  "Can you provide a sample query and expected answer that I can use to verify
    the skill works as intended? For example: 'If I ask [question], the skill
    should produce [answer].' This is optional but helps me validate the skill
    during development."

### Brainstorming Completion Criteria

You are ready to move to Phase 2 when you can confidently answer ALL of:

-   [ ] What is the workflow's purpose and scope?
-   [ ] What are the inputs and outputs?
-   [ ] Which steps are strict vs. flexible?
-   [ ] Which existing skills should be referenced?
-   [ ] What new scripts (if any) are needed?
-   [ ] What rate limits apply?
-   [ ] How should errors be handled?
-   [ ] Does the workflow need any code? (If yes → CLI pattern; if no →
    instruction-only)
-   [ ] Where should the skill be installed? (local, global, or custom path)
-   [ ] Is there a sample query/answer for validation?

## Phase 2: Skill Design

Produce a **design document** (as an artifact / implementation plan) and present
it to the user for approval. The document must include:

1.  **Skill name and description** (following YAML frontmatter rules: name ≤64
    chars, lowercase + hyphens; description ≤1024 chars).
2.  **Directory structure** showing all planned files and the **install
    location** (local, global, or custom — see Rule 7).
3.  **Existing skills referenced** with rationale for each.
4.  **New scripts** (if any) with proposed subcommands and arguments.
5.  **Rate limiting strategy** for any APIs not covered by existing skills.
6.  **Error handling strategy** per step.

**Wait for explicit user approval before proceeding to Phase 3.**

## Phase 3: Implementation

### Guiding Principles

General guidelines for skill implementation:

-   Use `uv run`, never `python` or `python3`.
-   Prefer stdlib libraries that come with a default Python 3 installation
    (`urllib` preferred); Avoid libraries that require extra installation if
    possible.
-   Rate limits must be documented and respected in code. Prefer
    **file-lock–based rate limiting** so that concurrent sub-agents sharing the
    same machine collectively respect the limit. See other skills in the Science
    Skills bundle for the canonical cross-process–safe implementation.
-   Skill output must be <500 lines or redirected to a file. Long output files
    should be processed programmatically to extract relevant fields.
-   Hyphens are recommended for the skill name and YAML `name:` field.

### Rule 1: Reuse Existing Skills

When the workflow uses functionality covered by an existing installed skill, the
new SKILL.md **MUST** reference it by name rather than reimplementing. Include a
**Dependencies** section in the SKILL.md listing required skills with a brief
rationale for each.

### Rule 2: Rate Limiting for New APIs

For any API interaction **not** covered by an existing skill, the generated CLI
script **MUST** implement rate limiting. Before writing any rate-limiting code,
**look up the API's official rate-limit guidelines**: check any documentation
the user provided during brainstorming, then search the API's public
documentation online. If no documented rate limit can be found, **default to 1
request per second**. The rate limiting pattern is built directly into the CLI
template at `references/cli_script_template.py` — see the `RateLimitError` class
and the `_request` method of the API client.

Key requirements:

-   Use `time.monotonic()` for timing (not `time.time()`).
-   Calculate delay from documented rate limits.
-   Implement retry with exponential backoff for transient errors (5xx).
-   Raise a dedicated `RateLimitError` when HTTP 429 is received.
-   Log retry attempts to stderr so the agent can observe progress.
-   Include the URL and rate-limit value in error messages.
-   On non-retriable HTTP errors (e.g. 400, 403, 404), read and include the
    response body in the error message — not just the status code. API response
    bodies contain actionable details (e.g., "Invalid parameter") that enable
    the agent to self-correct.

### Rule 3: CLI Script Pattern (Default When Code Is Needed)

**This is the default choice.** If **any** step in the workflow involves API
calls, data processing, file I/O, computation, or any other programmatic work,
produce a multi-command CLI script using `argparse` with subcommands. Follow the
template in `references/cli_script_template.py`.

Key requirements:

-   Each major workflow step becomes a subcommand.
-   All subcommands accept `--output` for writing results to a file.
-   Use `json.dump` with `indent=2` for JSON output.
-   Print a success message with the output file path.
-   Exit with code 1 on errors.
-   Make arguments like `--limit` **required** (no silent defaults). This forces
    the agent to specify the value explicitly, preventing it from assuming it
    retrieved "all" results when it was silently capped.

### Rule 4: Default to File Output

All scripts and workflows **MUST** write output to files, not stdout. Stdout
should only contain short status messages (e.g., "Success! Data written to:
results.json"). This is critical because:

-   API responses can be very large and will truncate in terminal output.
-   File output is token-efficient — the agent reads only the fields it needs
    using `jp` or Python one-liners.
-   Large stdout output wastes context window space.

### Rule 5: Instruction-Only Pattern (Only When No Code Is Needed)

Use this pattern **only** when the workflow requires **zero** programmatic work
— i.e., every step is purely about orchestration, reasoning, multi-skill
coordination, or following a written protocol. If any step needs code (API
calls, data processing, file I/O, etc.), use the CLI pattern from Rule 3
instead. Produce a SKILL.md with a structured workflow section:

```markdown
## Workflow

### 1. Step Name
- Description of what to do
- Which skill to use and how

### 2. Next Step
...
```

### Rule 6: SKILL.md Structure

Every generated SKILL.md must follow this structure:

```markdown
---
name: {skill-name}
description: >-
  {description}
---

# {Skill Title}

## Overview
{Brief description of what the skill does.}

## Dependencies
{List of required skills, if any.}

## Quick Start
{Minimal example to get started.}

## Utility Scripts (if CLI-based)
{Document each subcommand with examples.}

## Workflow (if instruction-only)
{Numbered steps with clear instructions.}

## Rate Limiting (if applicable)
{Document rate limits and how they are enforced.}

## Common Mistakes
{List 2-3 common pitfalls.}
```

### Rule 7: Skill Placement

Skills can be installed **locally** (project-specific, per-workspace) or
**globally** (available across all projects). Ask the user if they want to
install locally, globally, or use a custom install path.

Skill paths by agent CLI (local paths relative to project root):

-   **Claude Code**: local `.claude/skills/`, global `~/.claude/skills/`
-   **Codex**: local `.agents/skills/`, global `~/.agents/skills/`
-   **Antigravity 2.0**: local `.agents/skills/`, global
    `~/.gemini/config/skills/`
-   **Gemini CLI**: local `.gemini/skills/`, global `~/.gemini/skills/`
-   **OpenCode**: local `.opencode/skills/`, global `~/.config/opencode/skills/`

For other CLIs, find out local and global skill paths by yourself.

## Phase 4: Validation

After implementation is complete:

1.  **Test the skill manually** by invoking the agent with a natural-language
    prompt that should trigger the new skill.

2.  **If a sample query/answer was provided** during brainstorming, run it
    through the skill and verify the output matches expectations.
