# Example Pipelines

Complete working configurations for common scenarios.

## Dev Team

A planner, engineer, and reviewer with a review loop.

```yaml
name: dev-team

skills:
  atomic:
    planning: npm:skillfold/library/skills/planning
    code-writing: npm:skillfold/library/skills/code-writing
    code-review: npm:skillfold/library/skills/code-review
    testing: npm:skillfold/library/skills/testing
    github-workflow: npm:skillfold/library/skills/github-workflow

  composed:
    planner:
      compose: [planning]
      description: "Breaks down requirements into actionable tasks."
    engineer:
      compose: [code-writing, testing, github-workflow]
      description: "Writes production code and tests."
    reviewer:
      compose: [code-review, testing]
      description: "Reviews code for correctness and quality."
    orchestrator:
      compose: [planning, github-workflow]
      description: "Coordinates the team pipeline."

state:
  Task:
    title: string
    description: string
  Review:
    approved: bool
    feedback: string
  plan:
    type: string
  tasks:
    type: list<Task>
  code:
    type: string
  review:
    type: Review

team:
  orchestrator: orchestrator

  flow:
    - planner:
        writes: [state.plan, state.tasks]
      then: engineer

    - engineer:
        reads: [state.plan, state.tasks]
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

## Content Pipeline

Research topics, then map over them to write articles in parallel.

```yaml
name: content-pipeline

skills:
  atomic:
    research: npm:skillfold/library/skills/research
    writing: npm:skillfold/library/skills/writing
    summarization: npm:skillfold/library/skills/summarization

  composed:
    researcher:
      compose: [research]
      description: "Identifies topics worth covering."
    writer:
      compose: [research, writing]
      description: "Writes articles on assigned topics."
    editor:
      compose: [writing, summarization]
      description: "Edits and polishes articles."

state:
  Topic:
    title: string
    angle: string
  Article:
    title: string
    body: string
  topics:
    type: list<Topic>
  articles:
    type: list<Article>

team:
  flow:
    - researcher:
        writes: [state.topics]
      then: writing-team

    - writing-team:
        reads: [state.topics]
        writes: [state.articles]
      map:
        over: topics
        as: topic
        flow:
          - writer:
              reads: [state.topic]
              writes: [state.article]
            then: editor
          - editor:
              reads: [state.article]
              writes: [state.article]
            then: end
```

## Code Review Bot

Minimal two-agent flow for automated code review.

```yaml
name: code-review-bot

skills:
  atomic:
    code-review: npm:skillfold/library/skills/code-review
    writing: npm:skillfold/library/skills/writing

  composed:
    analyzer:
      compose: [code-review]
      description: "Analyzes code for issues."
    reporter:
      compose: [writing]
      description: "Formats review findings into a report."

state:
  findings:
    type: string
  report:
    type: string

team:
  flow:
    - analyzer:
        writes: [state.findings]
      then: reporter

    - reporter:
        reads: [state.findings]
        writes: [state.report]
      then: end
```

## Quick Start

To use any of these examples:

```bash
npm install skillfold
npx skillfold init my-team --template dev-team
cd my-team
npx skillfold validate
npx skillfold --target claude-code
```

The `--template` flag scaffolds from one of the library examples. Templates available: `dev-team`, `content-pipeline`, `code-review-bot`.
