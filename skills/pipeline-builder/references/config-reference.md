# Config Reference

A skillfold pipeline config (`skillfold.yaml`) has four top-level sections.

## resources

Resource declarations mapping group names to namespace URLs. Used for state location validation and orchestrator URL resolution.

```yaml
resources:
  github:
    url: https://github.com/{owner}/{repo}
```

## skills

Split into `atomic` (references to skill directories) and `composed` (compositions of other skills).

### atomic

```yaml
skills:
  atomic:
    # Local path
    planning: ./skills/planning

    # GitHub URL (public or private with GITHUB_TOKEN)
    code-review: https://github.com/org/repo/tree/main/skills/code-review

    # npm package
    testing: npm:skillfold/library/skills/testing
```

### composed

```yaml
skills:
  composed:
    engineer:
      compose: [planning, code-writing, testing]
      description: "Writes and tests code."

    reviewer:
      compose: [code-review, testing]
      description: "Reviews code quality."
```

Composition is recursive: composed skills can reference other composed skills.

**agentConfig** (optional): Platform-specific agent configuration.

```yaml
skills:
  composed:
    engineer:
      compose: [planning, code-writing]
      description: "Writes code."
      agentConfig:
        model: claude-sonnet-4-5-20250514
        mcpServers:
          filesystem:
            command: npx
            args: ["-y", "@anthropic-ai/mcp-filesystem"]
```

## state

Typed state schema with custom types, primitives (`string`, `bool`, `number`), and lists.

```yaml
state:
  # Custom type definition
  Review:
    approved: bool
    feedback: string

  # State fields
  tasks:
    type: list<Task>
    location:
      github-issues: { repo: owner/repo, label: task }

  review:
    type: Review
    location:
      github-pull-requests: { repo: owner/repo }
      kind: review
```

### Locations

State fields can have external locations for persistence:

- `github-issues`: GitHub Issues with label filtering
- `github-discussions`: GitHub Discussions with category filtering
- `github-pull-requests`: GitHub Pull Requests

## team

### orchestrator

Optional name of a composed skill to append the generated execution plan to.

```yaml
team:
  orchestrator: orchestrator
```

### flow

Directed execution graph with nodes, transitions, and conditional routing.

```yaml
team:
  flow:
    - agent-name:
        reads: [state.field1]
        writes: [state.field2]
      then: next-agent

    - next-agent:
        reads: [state.field2]
        writes: [state.result]
      then:
        - when: result.approved == true
          to: end
        - when: result.approved == false
          to: agent-name
```

### Map (parallel execution)

```yaml
    - mapper:
        reads: [state.items]
        writes: [state.results]
      map:
        over: items
        as: item
        flow:
          - processor:
              reads: [state.item]
              writes: [state.result]
            then: end
```

### Async nodes

For external agents (humans, CI, other teams):

```yaml
    - human-review:
        reads: [state.code]
        writes: [state.feedback]
        async: true
        policy: block
      then: engineer
```

## imports

Pull in skills, state, and resources from other configs:

```yaml
imports:
  - npm:skillfold/library/skillfold.yaml
  - ./shared/base-config.yaml
```
