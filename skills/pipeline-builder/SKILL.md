---
name: pipeline-builder
description: Design and build multi-agent AI pipelines using YAML configuration. Use when users want to coordinate multiple agents into a team, create execution workflows with conditional routing, compose skills into agent roles, define typed shared state between agents, or set up pipeline orchestration. Triggers on requests involving agent teams, multi-agent coordination, pipeline design, workflow automation, skill composition, or orchestrator generation.
license: Complete terms in LICENSE.txt
---

# Pipeline Builder

Design multi-agent pipelines where specialized agents coordinate through typed state and directed execution graphs. The output is a YAML config that compiles to standard SKILL.md files for any platform that supports the Agent Skills standard.

## When to Use

- User wants to wire multiple agents into a coordinated workflow
- User needs conditional routing (if review fails, loop back to engineer)
- User wants parallel execution (map over a list of items)
- User wants to compose existing skills into agent roles
- User needs typed shared state validated at compile time

## Process

### 1. Understand the Workflow

Ask the user what agents they need and how data flows between them. Common patterns:

- **Linear pipeline**: A -> B -> C (e.g., planner -> engineer -> reviewer)
- **Review loop**: engineer -> reviewer -> (approved? end : engineer)
- **Map/parallel**: process each item in a list concurrently
- **Conditional routing**: different paths based on state values

### 2. Define Atomic Skills

Each reusable capability is an atomic skill - a directory containing a `SKILL.md` file. Skills can be:

- **Local paths**: `./skills/code-review`
- **GitHub URLs**: `https://github.com/org/repo/tree/main/skills/code-review`
- **npm packages**: `npm:package-name/path/to/skill`

### 3. Compose Agents from Skills

Agents are composed skills - they combine multiple atomic skills into a role:

```yaml
skills:
  atomic:
    planning: ./skills/planning
    code-writing: ./skills/code-writing
    testing: ./skills/testing
    code-review: ./skills/code-review

  composed:
    engineer:
      compose: [planning, code-writing, testing]
      description: "Writes and tests production code."
    reviewer:
      compose: [code-review, testing]
      description: "Reviews code for correctness and quality."
```

Composition is recursive - composed skills can reference other composed skills.

### 4. Define Shared State

State is the typed data that flows between agents. Define custom types and primitives:

```yaml
state:
  Task:
    title: string
    description: string
  Review:
    approved: bool
    feedback: string
  tasks:
    type: list<Task>
  code:
    type: string
  review:
    type: Review
```

State fields can have external locations (GitHub Issues, Discussions, PRs) for persistence.

### 5. Design the Execution Flow

The flow defines which agents run in what order, what state they read/write, and how transitions work:

```yaml
team:
  orchestrator: orchestrator  # which composed skill gets the generated plan

  flow:
    - planner:
        writes: [state.tasks]
      then: engineer

    - engineer:
        reads: [state.tasks]
        writes: [state.code]
      then: reviewer

    - reviewer:
        reads: [state.code]
        writes: [state.review]
      then:
        - when: review.approved == true
          to: end
        - when: review.approved == false
          to: engineer
```

### 6. Validate and Compile

The compiler validates at build time:

- All skill references resolve
- State reads/writes are consistent
- No write conflicts between concurrent agents
- Conditional branches cover all cases
- No unreachable nodes in the flow

Compile with [skillfold](https://github.com/byronxlg/skillfold):

```bash
npm install skillfold
npx skillfold init my-team
npx skillfold validate    # check config
npx skillfold             # compile to build/
npx skillfold --target claude-code  # compile to .claude/
```

The compiler outputs standard SKILL.md files plus an orchestrator with the execution plan. Supports 12 platform targets including Claude Code, Cursor, Windsurf, Codex, Copilot, Gemini, Goose, Roo Code, Kiro, and Junie.

## Common Patterns

See `references/flow-patterns.md` for detailed pattern examples including:

- Linear pipelines with handoffs
- Review loops with conditional routing
- Parallel map over lists
- Sub-flow imports for nested pipelines
- Async nodes for human-in-the-loop workflows

## Config Reference

See `references/config-reference.md` for the full YAML specification.

## Examples

See `references/examples.md` for complete working pipeline configurations.
