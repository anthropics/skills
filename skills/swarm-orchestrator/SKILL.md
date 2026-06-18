---
name: swarm-orchestrator
description: Design, build, and debug multi-agent systems and agent swarms. Use this skill whenever the user wants to create a team of AI agents, orchestrate multiple agents working together, design agent architectures, implement agent communication patterns, build agent pipelines, debug multi-agent failures, or optimize agent costs. Also use when the user mentions swarms, agent teams, multi-agent systems, agent orchestration, agent pipelines, chalkboard patterns, or agent-to-agent communication.
---

# Swarm Orchestrator

Design multi-agent systems where specialized agents collaborate through structured communication protocols. This skill teaches Claude to architect, implement, and debug agent swarms that are deterministic-first, cost-efficient, and debuggable.

## Core Principles

1. **Single responsibility** — Each agent does ONE thing well
2. **Deterministic first** — Try rules/code before LLM calls
3. **Sequential over parallel** — Agents run one at a time unless truly independent
4. **Chalkboard protocol** — Shared state that agents read from and write to
5. **Fail loud** — Every agent validates its input and flags problems, never silently passes garbage

## 1. Designing Agent Roles

### The Archetype System

Every agent in a swarm maps to one of these archetypes:

| Archetype | Role | Input | Output |
|-----------|------|-------|--------|
| **Perceiver** | Extracts structured data from raw input | Raw text, images, data | Structured facts, entities |
| **Classifier** | Categorizes and routes work | Structured input | Labels, categories, routing decisions |
| **Analyzer** | Deep analysis of a specific domain | Focused input + context | Findings, scores, assessments |
| **Synthesizer** | Combines multiple analyses into coherent output | Multiple agent outputs | Unified result |
| **Validator** | Checks work quality and catches errors | Any agent output | Pass/fail + error details |
| **Resolver** | Handles conflicts and contradictions | Conflicting outputs | Resolution + reasoning |
| **Planner** | Breaks complex tasks into subtasks | High-level goal | Ordered task list |
| **Executor** | Carries out a specific action | Task specification | Action result |

### Role Design Rules

When designing agents for a swarm:

1. **Name reveals function** — "CauseAnalyzer" not "Agent3"
2. **One archetype per agent** — Don't combine Perceiver + Analyzer
3. **Define input/output contracts** — Every agent has a typed schema for what it accepts and produces
4. **Specify when deterministic** — Mark which agents NEVER need LLM calls
5. **Set cost budget** — Mark which agents are allowed to make API calls and how many

Example agent definition:
```json
{
  "name": "ContradictionDetector",
  "archetype": "Validator",
  "description": "Checks new findings against existing knowledge for conflicts",
  "input_schema": {
    "new_finding": "string",
    "existing_facts": "array<string>"
  },
  "output_schema": {
    "contradictions": "array<{fact: string, conflict: string, severity: float}>",
    "passed": "boolean"
  },
  "deterministic": true,
  "api_calls": 0,
  "position_in_pipeline": 5
}
```

## 2. Communication Patterns

### Pattern 1: Sequential Chalkboard (Recommended Default)

Agents execute in a fixed order. Each agent reads the shared chalkboard, does its work, writes its results back, and the next agent runs.

```
[Input] → Agent A writes → Agent B reads + writes → Agent C reads + writes → [Output]
                    ↕                    ↕                    ↕
              ┌─────────────────────────────────────────────────────┐
              │              SHARED CHALKBOARD                      │
              │  agent_a_output: {...}                              │
              │  agent_b_output: {...}                              │
              │  agent_c_output: {...}                              │
              └─────────────────────────────────────────────────────┘
```

**When to use:** Most swarms. Sequential is easier to debug, reproduce, and reason about.

**Chalkboard rules:**
- Agents can READ any previous agent's output
- Agents can only WRITE to their own section
- Each agent's output is immutable once written
- The chalkboard is the single source of truth

### Pattern 2: Fan-Out / Fan-In

One agent splits work across multiple parallel agents, then a synthesizer combines results.

```
                    ┌→ Analyzer A ─┐
[Input] → Splitter ─┼→ Analyzer B ─┼→ Synthesizer → [Output]
                    └→ Analyzer C ─┘
```

**When to use:** Only when sub-tasks are truly independent AND the order doesn't matter. Example: analyzing different aspects of the same document.

**Rules:**
- Parallel agents MUST NOT depend on each other's output
- Synthesizer MUST handle missing/failed parallel results
- Set timeouts on parallel agents

### Pattern 3: Pipeline with Gates

Sequential pipeline where gate agents can halt execution or redirect.

```
[Input] → Perceiver → Gate → Analyzer → Gate → Synthesizer → [Output]
                        ↓                 ↓
                     [REJECT]          [REDIRECT]
```

**When to use:** When quality control checkpoints are needed. Example: content moderation, compliance checks.

**Gate rules:**
- Gates are always deterministic (no API calls)
- Gates return: PASS, REJECT (with reason), or REDIRECT (with target)
- A rejected pipeline stops immediately — no partial results
- Gates should be fast (< 100ms)

### Pattern 4: Adversarial Pair

Two agents with opposing objectives review the same input, then a resolver decides.

```
[Input] → Advocate Agent ──┐
                            ├→ Resolver → [Output]
[Input] → Critic Agent ────┘
```

**When to use:** High-stakes decisions, fact validation, security review.

**Rules:**
- Advocate builds the strongest case FOR
- Critic builds the strongest case AGAINST
- Resolver weighs both, must cite which arguments won and why
- Neither agent sees the other's output until the Resolver phase

### Pattern 5: Iterative Refinement

An agent produces output, a validator checks it, and failures loop back for retry.

```
[Input] → Generator → Validator ──PASS──→ [Output]
              ↑            │
              └───FAIL─────┘ (max 3 retries)
```

**When to use:** When output quality is variable and can be objectively checked. Example: code generation with test validation.

**Rules:**
- Set a hard retry limit (3 is default)
- Validator feedback must be specific enough to guide the fix
- Track retry count on the chalkboard
- If max retries hit, escalate to user — don't loop forever

## 3. Deterministic-First Cascade

The most important optimization pattern. Always try deterministic approaches before spending API tokens.

### The Cascade

```
Input → [Rules/Code] → solved? → YES → Output ($0)
                          ↓ NO
         [Small Local Model] → solved? → YES → Output ($0)
                                  ↓ NO
         [Large API Model] → solved? → YES → Output ($0.01-0.10)
                                  ↓ NO
         [Frontier Model] → Output ($0.10-1.00)
```

### Implementation Rules

1. **Code perceives, model decides** — Use code for data extraction, parsing, pattern matching. Use models only for judgment calls that require reasoning.

2. **Start smallest** — When an LLM is needed, start with the smallest model that might work (0.5B → 1.5B → 3B → 7B). Never jump to 7B for micro-tasks.

3. **Track what's deterministic** — In your agent definitions, explicitly mark `"deterministic": true` for agents that never need API calls. This is your cost floor.

4. **Measure the cascade** — Log which level solved each input. If 90% solve at rules, your cascade is healthy. If 90% fall through to frontier, your rules are broken.

### Cost Budgets

Set cost limits per agent and per pipeline run:

```json
{
  "pipeline_budget": {
    "max_api_calls": 2,
    "max_cost_per_run": 0.20,
    "preferred_model": "local-3b",
    "fallback_model": "claude-sonnet",
    "frontier_model": "claude-opus"
  },
  "agent_budgets": {
    "Perceiver": {"api_calls": 0, "max_cost": 0},
    "Classifier": {"api_calls": 0, "max_cost": 0},
    "Analyzer": {"api_calls": 1, "max_cost": 0.05},
    "Synthesizer": {"api_calls": 1, "max_cost": 0.15},
    "Validator": {"api_calls": 0, "max_cost": 0}
  }
}
```

## 4. Building a Swarm — Step by Step

### Step 1: Define the mission

What does this swarm accomplish? Write a single sentence.
> "This swarm analyzes customer feedback and produces actionable insights with supporting evidence."

### Step 2: Decompose into agents

List the distinct capabilities needed. Each becomes an agent. Follow single-responsibility.

```
1. FeedbackParser (Perceiver) — Extract structured data from raw feedback
2. SentimentScorer (Analyzer, deterministic) — Score sentiment using rules
3. TopicClassifier (Classifier) — Categorize feedback by topic
4. PatternDetector (Analyzer) — Find recurring themes across feedback
5. InsightSynthesizer (Synthesizer) — Combine analyses into actionable insights
6. EvidenceValidator (Validator, deterministic) — Verify insights have supporting data
```

### Step 3: Choose communication pattern

For most swarms, start with **Sequential Chalkboard**. Only use Fan-Out if you have truly independent parallel work.

### Step 4: Define the chalkboard schema

```json
{
  "input": {},
  "feedback_parser": {"entities": [], "structured_feedback": []},
  "sentiment_scorer": {"scores": [], "distribution": {}},
  "topic_classifier": {"topics": [], "confidence": {}},
  "pattern_detector": {"patterns": [], "frequency": {}},
  "insight_synthesizer": {"insights": [], "recommendations": []},
  "evidence_validator": {"validated": [], "rejected": [], "passed": true},
  "metadata": {"start_time": "", "end_time": "", "total_cost": 0, "api_calls": 0}
}
```

### Step 5: Implement the cascade

For each agent, define:
1. Can this be done with pure code/rules? → deterministic
2. If not, what's the smallest model that works? → local model
3. Only if both fail → API call

### Step 6: Add gates

Place Validator agents after any agent whose output quality is critical. Gates are cheap (deterministic) and prevent bad data from propagating.

### Step 7: Test with real input

Run the pipeline with actual data. Check:
- Does each agent produce valid output?
- Does the chalkboard fill correctly?
- What percentage hits the API vs deterministic?
- Where do failures occur?

## 5. Debugging Multi-Agent Failures

### The Chalkboard Trace

When a swarm fails, read the chalkboard top-to-bottom. The failure is at the FIRST agent whose output is wrong or missing.

```
Debugging checklist:
1. Which agent's output is first to be wrong? → That's the broken agent
2. Was the broken agent's INPUT correct? 
   → YES: The agent's logic is broken
   → NO: The upstream agent is the real problem (go to step 1 for that agent)
3. Was it a deterministic or API agent?
   → Deterministic: Check rules/code logic
   → API: Check prompt, check if model is appropriate, check token limits
4. Is this a consistent or intermittent failure?
   → Consistent: Logic bug
   → Intermittent: Model variance — add validation gate after this agent
```

### Common Failure Patterns

| Symptom | Cause | Fix |
|---------|-------|-----|
| Agent produces empty output | Input schema mismatch | Validate input at agent entry |
| Wrong agent runs | Classifier routing error | Add explicit routing rules, reduce classification categories |
| Pipeline hangs | Retry loop with no max | Set hard retry limits (max 3) |
| Output quality drops over time | Context window overflow | Summarize chalkboard between agents, don't pass raw |
| Costs spike unexpectedly | Deterministic agents falling through to API | Check rule coverage, add more deterministic patterns |
| Contradictory outputs | No adversarial validation | Add Validator agent between conflicting sources |
| Correct parts combined wrong | Synthesizer too broad | Split Synthesizer into focused sub-synthesizers |

### Health Metrics

Track these for every swarm:

```json
{
  "pipeline_health": {
    "success_rate": 0.95,
    "avg_latency_ms": 340,
    "avg_cost_per_run": 0.03,
    "deterministic_solve_rate": 0.82,
    "api_calls_per_run": 1.2,
    "agent_failure_rates": {
      "FeedbackParser": 0.01,
      "SentimentScorer": 0.0,
      "TopicClassifier": 0.05,
      "PatternDetector": 0.03,
      "InsightSynthesizer": 0.02,
      "EvidenceValidator": 0.0
    }
  }
}
```

## 6. Scaling Patterns

### When to add agents

- A single agent's prompt exceeds 1000 tokens → split responsibility
- An agent fails on > 10% of inputs → add a specialized pre-processor
- Users request new capability → new agent, don't bloat existing ones

### When to merge agents

- Two agents always run together with no gate between them → merge
- An agent's output is just a passthrough → remove it
- Three agents each handle < 5% of inputs → consolidate

### Mission-Specific Configuration

For different use cases, reconfigure the same agents with different:
- Agent ordering (which runs first)
- Gate thresholds (how strict)
- Cost budgets (how much API spend)
- Model assignments (which model per agent)

Don't rebuild the swarm — reconfigure it.

## Output Format

When presenting a swarm design to the user:

### Architecture Summary
```
Swarm: [Name]
Mission: [One sentence]
Agents: [Count] ([Deterministic count] deterministic, [API count] API-enabled)
Pattern: [Sequential Chalkboard / Fan-Out / Pipeline with Gates / etc.]
Est. cost per run: $[amount]
```

### Agent Table
```
| # | Agent | Archetype | Deterministic | API Calls | Input | Output |
|---|-------|-----------|---------------|-----------|-------|--------|
```

### Pipeline Diagram
Show the flow with ASCII art using the patterns above.

## Do's and Don'ts

**Do:**
- Start with Sequential Chalkboard until you prove you need something else
- Make every agent validate its own input before processing
- Set cost budgets before building
- Log every agent's input/output for debugging
- Test with real data, not toy examples
- Mark deterministic agents explicitly

**Don't:**
- Don't run agents in parallel unless they're truly independent
- Don't let agents call APIs when rules would work
- Don't build 10 agents when 4 would do — complexity is cost
- Don't skip gates between critical agents
- Don't let the synthesizer see raw input — it should only see agent outputs
- Don't retry infinitely — set hard limits
- Don't build the swarm all at once — add one agent at a time and test
