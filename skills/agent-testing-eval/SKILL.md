---
name: agent-testing-eval-skill
description: 7-phase evaluation protocol for AI agent systems. Covers eval framework design, golden dataset construction, regression harness, LLM-as-judge setup, failure mode taxonomy, CI integration, and evaluation-driven prompt iteration. Produces a structured quality report with pass/fail verdicts and actionable remediation. Compatible with Claude, Codex, ChatGPT, AutoGen, CrewAI, LangGraph.
license: MIT
compatibility: Works with any LLM agent or multi-agent framework. No external eval tools required — protocol guides construction from scratch.
metadata:
  author: ClawMerchants (clawmerchants.com)
  version: 1.0.0
  category: agent-skills
  marketplace: clawmerchants.com/api/v1/data/agent-testing-eval-skill
---

# Agent Testing & Evaluation Protocol

## Activation
When asked to test, evaluate, benchmark, or quality-check an AI agent system — or to build an eval harness, CI pipeline, or regression suite for agentic workflows — activate this protocol.

## Phase 1: Advertise (Free Preview)
Describe capability without revealing full methodology:
- "I'll build a complete evaluation system for your agent: golden dataset, LLM-as-judge scoring, failure mode taxonomy, regression harness, and CI integration."
- Provide one diagnostic signal (e.g., identify the top-3 failure modes likely given the agent's task type) to demonstrate value.

## Phase 2: Load (Full Protocol)

---

## Phase 1: Eval Framework Design

### Define the Evaluation Objective
Before writing a single test, answer:
1. **What decisions does this agent make?** (classify, retrieve, generate, plan, act)
2. **What constitutes a correct output?** (exact match, semantic equivalence, valid action, no hallucination)
3. **What failure modes are unacceptable?** (wrong answer vs. slow answer vs. no answer)
4. **Who is the final judge?** (deterministic rule, LLM-as-judge, human, downstream system)

### Choose the Evaluation Mode
| Mode | When to Use | Tradeoff |
|------|-------------|----------|
| **Exact match** | Structured outputs (JSON, code, SQL) | Fast, cheap, brittle to format variation |
| **Semantic match** | Open-ended responses, summaries | Flexible, requires embedding similarity threshold |
| **LLM-as-judge** | Complex reasoning, multi-step tasks | Accurate, costs tokens, needs calibration |
| **Human eval** | Launch gate, bias audits | Ground truth, slow and expensive |
| **Tool use verification** | Agentic tool calls | Confirm correct tool + correct arguments |
| **Outcome-based** | Multi-step pipelines | Measure end-state, not intermediate steps |

### Define the Eval Scorecard
For each eval dimension, define: metric name, measurement method, threshold to pass, weight.

Example scorecard structure:
```
| Dimension         | Method           | Pass Threshold | Weight |
|-------------------|------------------|----------------|--------|
| Correctness       | LLM judge (0-5)  | ≥ 4.0          | 40%    |
| Tool accuracy     | Exact call match | ≥ 95%          | 30%    |
| Hallucination rate| LLM judge        | ≤ 5%           | 20%    |
| Latency           | P95 wall time    | ≤ 8s           | 10%    |
```

---

## Phase 2: Golden Dataset Construction

### What Makes a Good Golden Dataset
A golden dataset is the ground truth your evals run against. Quality > quantity.

**Required properties:**
- **Coverage**: Covers the full distribution of real inputs (happy path + edge cases + adversarial)
- **Correct labels**: Each example has a ground-truth expected output or verdict
- **Metadata**: Tags for task type, difficulty, domain, known failure mode
- **Reproducibility**: Fixed seeds, deterministic prompts — same input always produces same test

**Minimum viable golden dataset by agent type:**
| Agent Type | Min Examples | Required Coverage |
|------------|-------------|-------------------|
| Q&A / RAG agent | 50 | 80% in-distribution, 10% edge, 10% adversarial |
| Code-generation agent | 30 | Across 5+ language patterns, includes syntax errors, security issues |
| Planning / orchestrator | 20 | Multi-step plans with ≥3 subtasks; include ambiguous inputs |
| Tool-use agent | 40 | All tools represented; include invalid tool inputs |
| Summarization agent | 30 | Short, long, conflicting sources, no relevant info |

### Golden Example Schema
Each example should capture:
```json
{
  "id": "eval-001",
  "category": "tool-use",
  "difficulty": "medium",
  "input": { "user_message": "...", "context": "..." },
  "expected_output": "...",          // or null for LLM-judged evals
  "expected_tool_calls": [...],       // for tool-use verification
  "judge_criteria": "...",            // instructions for LLM judge
  "known_failure_mode": "hallucination",
  "created_at": "2026-01-01",
  "last_validated": "2026-03-01"
}
```

### Seeding the Dataset
1. **Mine production logs** — identify the top-20 real user inputs by frequency
2. **Generate adversarial variants** — prompt an LLM to produce edge cases for each real input
3. **Inject known failures** — deliberately include inputs that previously caused failures
4. **Balance difficulty** — aim for 60% easy / 30% medium / 10% hard
5. **Validate ground truth** — have a second LLM (or human) verify the expected outputs before publishing

---

## Phase 3: Regression Test Harness

### Harness Architecture
```
Input Dataset → Agent Under Test → Raw Outputs
                                        ↓
                              Scoring Engine (per eval mode)
                                        ↓
                              Score Report (per example + aggregate)
                                        ↓
                              Pass/Fail Gate → CI exit code
```

### Implementation Pattern (TypeScript/Node)
```typescript
interface EvalExample {
  id: string;
  input: Record<string, unknown>;
  expectedOutput?: string;
  judgeInstructions?: string;
}

interface EvalResult {
  id: string;
  score: number; // 0-1
  passed: boolean;
  agentOutput: string;
  latencyMs: number;
  failure?: string;
}

async function runEvalSuite(examples: EvalExample[], agent: AgentFn): Promise<EvalResult[]> {
  const results: EvalResult[] = [];
  for (const ex of examples) {
    const start = Date.now();
    const output = await agent(ex.input);
    const latencyMs = Date.now() - start;
    const score = await scoreOutput(ex, output);
    results.push({ id: ex.id, score, passed: score >= PASS_THRESHOLD, agentOutput: output, latencyMs });
  }
  return results;
}
```

### Snapshot Testing for Agentic Outputs
- Store the first accepted output for each eval example as a "snapshot"
- On future runs, flag any output that diverges by more than the semantic threshold
- Treat snapshot regressions as blocking — they signal unintended behavior change
- Update snapshots only via explicit `--update-snapshots` flag in CI

### Test Isolation Requirements
- Each eval case runs in an isolated execution context (fresh agent state, no cross-contamination)
- Mock all external APIs (web search, databases) with deterministic fixtures
- Run with a fixed LLM temperature (0 or near-0) for reproducibility
- Log all tool calls, model inputs, and raw outputs for debugging

---

## Phase 4: LLM-as-Judge Setup

### When to Use LLM-as-Judge
Use LLM-as-judge when the correct output cannot be determined by exact match or simple rules:
- Open-ended generation (summaries, explanations, plans)
- Reasoning quality assessment
- Multi-turn conversation correctness
- Subtle safety / hallucination detection

### Judge Calibration Protocol
Before trusting an LLM judge, calibrate it:
1. **Create 20 hand-labeled examples** with known correct verdicts (0-5 scores)
2. **Run the judge prompt** on all 20 examples
3. **Measure agreement**: target Pearson r ≥ 0.85 with human labels
4. **Adjust the rubric** if agreement is below threshold — be more specific about each score level
5. **Test for positional bias**: shuffle A/B pairs and verify judge isn't systematically favoring first response

### Judge Prompt Template
```
You are an evaluation judge for an AI agent system.

Task: [describe the agent's task]
Rubric:
- 5: Perfect — fully correct, no hallucinations, all requirements met
- 4: Good — mostly correct, minor gaps, no hallucinations
- 3: Acceptable — partially correct, significant gaps but useful
- 2: Poor — mostly incorrect, some correct elements
- 1: Fail — wrong, hallucinated, or harmful

Input: {{input}}
Expected qualities: {{judge_criteria}}
Agent output: {{agent_output}}

Respond with JSON: { "score": 1-5, "reasoning": "...", "hallucination": true/false }
```

### Judge Model Selection
| Judge Model | Best For | Watch Out For |
|-------------|----------|---------------|
| GPT-4o | General eval, balanced | May be lenient with ChatGPT outputs |
| Claude Opus 4.6 | Nuanced reasoning, long outputs | Slow for large eval suites |
| Claude Sonnet 4.6 | Speed/quality balance, CI evals | Fine for most production eval pipelines |
| Gemini 1.5 Pro | Long-context, multimodal evals | Different scoring tendencies |

**Rule**: Never use the same model as both the agent under test and the judge. Cross-model judging reduces self-preference bias.

---

## Phase 5: Failure Mode Taxonomy

### Agentic Failure Mode Classification

**Category A: Correctness Failures**
| Failure Mode | Description | Detection Method |
|---|---|---|
| `HALLUCINATION` | Agent asserts false facts not in context | LLM judge + fact-check against source |
| `WRONG_ANSWER` | Logically incorrect output | Exact/semantic match against ground truth |
| `INCOMPLETE_OUTPUT` | Task partially completed, stops early | Completeness check + required field validation |
| `INSTRUCTION_DRIFT` | Agent stops following system prompt mid-conversation | Prompt adherence score per turn |

**Category B: Tool Use Failures**
| Failure Mode | Description | Detection Method |
|---|---|---|
| `WRONG_TOOL` | Called incorrect tool for the task | Tool call log comparison to expected |
| `WRONG_ARGS` | Called correct tool with incorrect arguments | Argument schema validation |
| `TOOL_LOOP` | Retried same failing tool call >3 times | Loop detection counter |
| `TOOL_SKIP` | Should have called a tool but didn't | Missing tool call assertion |

**Category C: Reliability Failures**
| Failure Mode | Description | Detection Method |
|---|---|---|
| `TIMEOUT` | Agent didn't respond within latency SLA | Wall-clock timer |
| `CRASH` | Unhandled exception or null output | Error logging |
| `NONDETERMINISM` | Same input produces different correct-class outputs | Run same input 3x, check output variance |
| `CONTEXT_OVERFLOW` | Agent loses track of early instructions in long context | Early-instruction retention test |

**Category D: Safety Failures**
| Failure Mode | Description | Detection Method |
|---|---|---|
| `PROMPT_INJECTION` | Agent follows injected instructions from user/tool data | Injection test suite |
| `DATA_LEAK` | Agent reveals system prompt or other users' data | Extraction attempt suite |
| `UNSAFE_ACTION` | Agent takes harmful action (delete, send, pay) without confirmation | Destructive action audit |

### Failure Mode Prioritization
Assign each failure mode a risk tier:
- **P0 (Blocking)**: Safety failures, data leaks, wrong tool with destructive consequence
- **P1 (High)**: Hallucinations in user-visible output, crashes, wrong answers in critical paths
- **P2 (Medium)**: Incomplete outputs, tool loops, nondeterminism under load
- **P3 (Low)**: Minor completeness gaps, latency above SLA by <2×, instruction drift in edge cases

---

## Phase 6: CI Integration

### CI Pipeline Design
```
On PR or push to main:
  1. Run unit tests (fast, deterministic — no LLM calls)
  2. Run eval suite (golden dataset, isolated fixtures)
     - If pass rate < threshold → BLOCK merge
     - If regression vs. baseline → BLOCK merge + post diff to PR
  3. Run safety eval subset (P0 + P1 failure modes only)
     - Any P0 failure → BLOCK merge, notify on-call
  4. Generate eval report → post as PR comment
  5. Update baseline scores if merge approved
```

### Baseline Management
- Store baseline scores as a JSON file in the repo: `evals/baseline.json`
- Format: `{ "suite_name": { "pass_rate": 0.94, "avg_score": 4.2, "p95_latency_ms": 6200 } }`
- Treat any regression >2% pass rate or >10% latency increase as a blocking regression
- Update baseline only on explicit `[update-baseline]` commit message tag (reviewed by senior engineer)

### GitHub Actions Example
```yaml
name: Agent Eval
on: [pull_request, push]
jobs:
  eval:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Run eval suite
        run: npm run eval:ci
        env:
          ANTHROPIC_API_KEY: ${{ secrets.ANTHROPIC_API_KEY }}
      - name: Post eval report
        if: always()
        uses: actions/github-script@v7
        with:
          script: |
            const report = require('./evals/report.json');
            github.rest.issues.createComment({
              issue_number: context.issue.number,
              body: `## Eval Results\nPass rate: ${report.passRate}\nRegression: ${report.regression}`
            });
```

---

## Phase 7: Evaluation-Driven Prompt Iteration

### The Eval → Improve Loop
```
1. Run full eval suite → identify failing examples
2. Cluster failures by failure mode
3. For each cluster:
   a. Identify root cause in prompt / context / tool definition
   b. Draft prompt change
   c. Run eval on the failing cluster only (fast iteration)
   d. Accept change only if cluster pass rate improves AND no regression elsewhere
4. Run full eval suite to confirm aggregate improvement
5. Commit prompt change with eval delta in commit message
```

### Prompt Change Validation Rules
- **Never accept a prompt change based on spot-checking** — always run the full eval suite
- **Test prompt changes on the failing cluster first** — validate the fix before running expensive full suite
- **Require net positive**: overall pass rate must improve or hold; no individual dimension can regress by >2%
- **Track prompt version**: tag each prompt version with a hash, log which version produced which eval score

### Continuous Improvement Cadence
| Cadence | Action |
|---------|--------|
| Every PR | Run golden dataset eval — block on regression |
| Weekly | Review top-5 failing examples — prioritize prompt fixes |
| Monthly | Refresh golden dataset — add new failure patterns from production logs |
| Quarterly | Re-calibrate LLM judge — verify agreement with updated human labels |
| On model upgrade | Re-run full eval suite — treat model upgrade as a breaking change |

## Phase 3: Resources
- HELM (Stanford CRFM) — Holistic Evaluation of Language Models
- RAGAS — RAG evaluation framework
- PromptFoo — open-source LLM testing and red-teaming
- LangSmith — LangChain eval and tracing platform
- Braintrust — eval platform for LLM applications
- Haiku — lightweight LLM eval framework
- The Eval Manifesto — principles for rigorous LLM evaluation

## Related Skills
- Multi-Agent Coordination & Task Routing: https://clawmerchants.com/v1/data/multi-agent-coordination-skill ($0.03)
- Deep Code Review Protocol: https://clawmerchants.com/v1/data/code-review-skill ($0.02)
