# Flow Patterns

Common execution patterns for multi-agent pipelines.

## Linear Pipeline

Agents execute in sequence, each reading the previous agent's output.

```yaml
team:
  flow:
    - planner:
        writes: [state.plan]
      then: engineer

    - engineer:
        reads: [state.plan]
        writes: [state.code]
      then: tester

    - tester:
        reads: [state.code]
        writes: [state.results]
      then: end
```

## Review Loop

The most common pattern: work -> review -> conditional loop back.

```yaml
team:
  flow:
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

The compiler validates that conditional branches cover all cases and that the loop has an exit condition.

## Parallel Map

Process each item in a list concurrently with a subgraph.

```yaml
state:
  Topic:
    title: string
    description: string
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
      then: writers

    - writers:
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

    - publisher:
        reads: [state.articles]
      then: end
```

Each item in `topics` gets its own writer -> editor subgraph running concurrently.

## Human in the Loop

Async nodes pause the pipeline for external input.

```yaml
team:
  flow:
    - engineer:
        writes: [state.code]
      then: human-review

    - human-review:
        reads: [state.code]
        writes: [state.feedback]
        async: true
        policy: block
      then: engineer
```

Policies: `block` (wait), `skip` (continue without), `use-latest` (use most recent value).

## Sub-flow Import

Embed an entire external pipeline as a single node.

```yaml
team:
  flow:
    - planner:
        writes: [state.plan]
      then: build

    - build:
        flow: ./pipelines/build-and-test.yaml
      then: deploy

    - deploy:
        reads: [state.artifacts]
      then: end
```

The imported pipeline's skills and state are merged into the parent config. Circular imports are detected at compile time.

## Conditional Branching

Route to different agents based on state values.

```yaml
team:
  flow:
    - classifier:
        writes: [state.category]
      then:
        - when: category == "bug"
          to: bug-fixer
        - when: category == "feature"
          to: feature-builder
        - when: category == "docs"
          to: docs-writer
```

The compiler validates that all referenced targets exist and are reachable.
