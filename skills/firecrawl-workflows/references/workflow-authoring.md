# Workflow Authoring

Use this reference when adding or reviewing workflow skills.

## Workflow Checklist

- Name the real user outcome in the first paragraph.
- Define only the blocking onboarding questions.
- Tell the agent what artifacts to gather with Firecrawl.
- Specify the final deliverable shape.
- Include an evidence or citation expectation when claims come from websites.
- Identify work that can run in parallel.
- Keep instructions generic enough for any coding agent harness.

## Harness-Agnostic Language

Use:

- "ask the user a clarifying question"
- "use sub-agents if available"
- "run independent page research in parallel"
- "use Firecrawl through the CLI or equivalent Firecrawl tools"

Avoid:

- editor-specific function names
- assumptions about a single modal UI
- hardcoded sub-agent APIs
- output paths that only one harness can access

## Lightweight Onboarding

Do not run a long interview by default. First infer from the user's message, files, URLs, and surrounding context. If the agent can safely start, start.

Ask at most 1-3 concise clarifying questions only when a required input is missing or ambiguity would materially change the work. Prefer defaults for non-blocking choices and state them briefly.

## Automation Inputs

For recurring jobs, each workflow should be expressible as:

```yaml
workflow: skill-name
cadence: weekly
inputs:
  subject: example
  urls: []
  competitors: []
  output: report.md
```

The skill does not need to implement a scheduler. It should make the inputs and outputs stable enough for another system to schedule it.

## Reference Repos

- `anthropics/skills`: use simple skill directories and minimal metadata.
- `anthropics/financial-services`: borrow outcome orientation and optional agent packaging ideas.
- `anthropics/claude-for-legal`: borrow vertical workflow organization and concrete deliverable framing.

Do not copy heavier managed-agent scaffolding unless this repo starts shipping standalone hosted agents.
