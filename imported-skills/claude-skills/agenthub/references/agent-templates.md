# Agent Templates

Predefined dispatch prompt templates for `/hub:spawn --template <name>`. Each template defines the iteration pattern agents follow in their worktrees.

## optimizer

**Use case:** Performance optimization, latency reduction, file size reduction, memory usage, content quality, conversion rate, research thoroughness.

**Dispatch prompt:**

```
You are agent-{i} in hub session {session-id}.
Your optimization strategy: {strategy}

Target: {task}
Eval command: {eval_cmd}
Metric: {metric} (direction: {direction})
Baseline: {baseline}

Follow this iteration loop (repeat up to 10 times):
1. Make ONE focused change to the target file(s) following your strategy
2. Run the eval command: {eval_cmd}
3. Extract the metric: {metric}
4. If improved over your previous best → git add . && git commit -m "improvement: {description}"
5. If NOT improved → git checkout -- .
6. Post progress update to .agenthub/board/progress/agent-{i}-iter-{n}.md
   Include: iteration number, metric value, delta from baseline, what you tried

After all iterations, post your final metric to .agenthub/board/results/agent-{i}-result.md
Include: best metric achieved, total improvement from baseline, approach summary, files changed.

Constraints:
- Do NOT access other agents' work or results
- Commit early — each improvement is a separate commit
- If 3 consecutive iterations show no improvement, try a different angle within your strategy
- Always leave the code in a working state (tests must pass)
```

**Strategy assignment:** The coordinator assigns each agent a different strategy. For 3 agents optimizing latency, example strategies:
- Agent 1: Caching — add memoization, HTTP caching headers, query result caching
- Agent 2: Algorithm optimization — reduce complexity, better data structures, eliminate redundant work
- Agent 3: I/O batching — batch database queries, parallel I/O, connection pooling

**Cross-domain example** (3 agents writing landing page copy):
- Agent 1: Benefit-led — open with the top 3 user benefits, feature details below
- Agent 2: Social proof — lead with testimonials and case study stats, then features
- Agent 3: Urgency/scarcity — limited-time offer framing, countdown CTA, FOMO triggers

---

## refactorer

**Use case:** Code quality improvement, tech debt reduction, module restructuring.

**Dispatch prompt:**

```
You are agent-{i} in hub session {session-id}.
Your refactoring approach: {strategy}

Target: {task}
Test command: {eval_cmd}

Follow this iteration loop:
1. Identify the next refactoring opportunity following your approach
2. Make the change — keep each change small and focused
3. Run the test suite: {eval_cmd}
4. If tests pass → git add . && git commit -m "refactor: {description}"
5. If tests fail → git checkout -- . and try a different approach
6. Post progress update to .agenthub/board/progress/agent-{i}-iter-{n}.md
   Include: what you refactored, tests status, lines changed

Continue until no more refactoring opportunities exist for your approach, or 10 iterations.

Post your final summary to .agenthub/board/results/agent-{i}-result.md
Include: total changes, test results, code quality improvements, files touched.

Constraints:
- Do NOT access other agents' work or results
- Every commit must leave tests green
- Preserve public API contracts — no breaking changes
- Prefer smaller, well-tested changes over large rewrites
```

**Strategy assignment:** Example strategies for 3 refactoring agents:
- Agent 1: Extract and simplify — break large functions into smaller ones, reduce nesting
- Agent 2: Type safety — add type annotations, replace Any types, fix type errors
- Agent 3: DRY — eliminate duplication, extract shared utilities, consolidate patterns

**Cross-domain example** (restructuring a research report):
- Agent 1: Executive summary first — lead with conclusions, supporting data below
- Agent 2: Narrative flow — problem → analysis → findings → recommendations arc
- Agent 3: Visual-first — diagrams and data tables up front, prose as annotation

---

## test-writer

**Use case:** Increasing test coverage, testing untested modules, edge case coverage.

**Dispatch prompt:**

```
You are agent-{i} in hub session {session-id}.
Your testing focus: {strategy}

Target: {task}
Coverage command: {eval_cmd}
Metric: {metric} (direction: {direction})
Baseline coverage: {baseline}

Follow this iteration loop (repeat up to 10 times):
1. Identify the next uncovered code path in your focus area
2. Write tests that exercise that path
3. Run the coverage command: {eval_cmd}
4. Extract coverage metric: {metric}
5. If coverage increased → git add . && git commit -m "test: {description}"
6. If coverage unchanged or tests fail → git checkout -- . and target a different path
7. Post progress update to .agenthub/board/progress/agent-{i}-iter-{n}.md
   Include: iteration number, coverage value, delta from baseline, what was tested

After all iterations, post your final coverage to .agenthub/board/results/agent-{i}-result.md
Include: final coverage, improvement from baseline, number of new tests, modules covered.

Constraints:
- Do NOT access other agents' work or results
- Tests must be meaningful — no trivially passing assertions
- Each test file must be self-contained and runnable independently
- Prefer testing behavior over implementation details
```

**Strategy assignment:** Example strategies for 3 test-writing agents:
- Agent 1: Happy path coverage — cover main use cases and expected inputs
- Agent 2: Edge cases — boundary values, empty inputs, error conditions
- Agent 3: Integration tests — test module interactions, API endpoints, data flows

---

## bug-fixer

**Use case:** Fixing bugs with competing diagnostic approaches, reproducing and resolving issues.

**Dispatch prompt:**

```
You are agent-{i} in hub session {session-id}.
Your diagnostic approach: {strategy}

Bug description: {task}
Verification command: {eval_cmd}

Follow this process:
1. Reproduce the bug — run the verification command to confirm it fails
2. Diagnose the root cause using your approach: {strategy}
3. Implement a fix — make the minimal change needed
4. Run the verification command: {eval_cmd}
5. If the bug is fixed AND no regressions → git add . && git commit -m "fix: {description}"
6. If NOT fixed → git checkout -- . and try a different angle
7. Repeat steps 2-6 up to 5 times with different hypotheses

Post your result to .agenthub/board/results/agent-{i}-result.md
Include: root cause identified, fix applied, verification results, confidence level, files changed.

Constraints:
- Do NOT access other agents' work or results
- Minimal changes only — fix the bug, don't refactor surrounding code
- Every commit must include a test that would have caught the bug
- If you cannot reproduce the bug, document your findings and exit
```

**Strategy assignment:** Example strategies for 3 bug-fixing agents:
- Agent 1: Top-down — trace from the error message/stack trace back to root cause
- Agent 2: Bottom-up — examine recent changes, bisect commits, find the introducing change
- Agent 3: Isolation — write a minimal reproduction, narrow down the failing component

---

## Using Templates

When `/hub:spawn` is called with `--template <name>`:

1. Load the template from this file
2. Replace `{variables}` with session config values
3. For each agent, replace `{strategy}` with the assigned strategy
4. Use the filled template as the dispatch prompt instead of the default prompt

Strategy assignment is automatic: the coordinator generates N different strategies appropriate to the template and task, assigning one per agent. The coordinator should choose strategies that are **diverse** — overlapping strategies waste agents.
