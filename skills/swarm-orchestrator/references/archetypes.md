# Agent Archetypes — Detailed Reference

## Archetype Decision Matrix

Use this to pick the right archetype for each role in your swarm.

### Perceiver
**Purpose:** First contact with raw data. Extracts structure from chaos.

**Deterministic?** Almost always YES. Use regex, parsers, ASTs — not LLMs.

**Input types:** Raw text, JSON, images, logs, CSV, API responses
**Output types:** Structured entities, key-value pairs, normalized records

**Design rules:**
- Never interpret — only extract
- Output schema must be strict (typed, validated)
- If parsing fails, return empty + error flag — never guess
- One Perceiver per data format

**Example implementations:**
```
FeedbackParser — regex + NLP rules to extract sentiment phrases, entities, topics
LogIngester — structured log parsing into event objects  
DocumentScanner — section headers, tables, lists extracted from documents
APIResponseNormalizer — flatten nested JSON into uniform records
```

### Classifier
**Purpose:** Routes work to the right agent or assigns labels.

**Deterministic?** YES — use keyword matching, decision trees, or embedding similarity.

**Input types:** Structured data from Perceiver
**Output types:** Category labels, routing decisions, confidence scores

**Design rules:**
- Define categories upfront — no open-ended classification
- Use keyword banks with weights, not LLM calls
- Multi-label is OK, but limit to max 3 labels per input
- Log classification distribution to detect drift

**Keyword bank example:**
```json
{
  "archetypes": {
    "security_threat": {
      "keywords": ["vulnerability", "exploit", "breach", "CVE", "attack"],
      "weight": 1.0,
      "threshold": 0.6
    },
    "performance_issue": {
      "keywords": ["slow", "latency", "timeout", "bottleneck", "memory"],
      "weight": 0.8,
      "threshold": 0.5
    }
  }
}
```

### Analyzer
**Purpose:** Deep domain-specific analysis. This is where expertise lives.

**Deterministic?** SOMETIMES. Many analyses can be rule-based (scoring, thresholds, comparisons). Use LLM only for nuanced judgment.

**Input types:** Classified/filtered data + domain context
**Output types:** Findings, scores, assessments, ranked results

**Design rules:**
- Each Analyzer covers ONE domain — don't combine
- Always output confidence scores
- Cite evidence for every finding
- If using LLM, provide focused context (not the whole chalkboard)

**Cascade pattern:**
```
1. Try rules (threshold checks, pattern matching) → $0
2. Try local model (3B) with focused prompt → $0  
3. Try API model with minimal context → $0.02-0.05
```

### Synthesizer
**Purpose:** Combines multiple agent outputs into a coherent result. Usually the ONLY agent that needs a frontier LLM.

**Deterministic?** Rarely. Synthesis is a judgment task.

**Input types:** Multiple agent outputs from the chalkboard
**Output types:** Unified analysis, recommendations, summaries

**Design rules:**
- Only reads agent outputs — never raw input
- Single API call maximum
- Must cite which agent's findings support each conclusion
- If agents disagree, flag the conflict rather than silently picking one
- This is usually the most expensive agent — optimize everything else first

### Validator
**Purpose:** Quality gate. Checks that output meets standards before passing downstream.

**Deterministic?** ALWAYS. Validators are rules, never LLMs.

**Input types:** Any agent output
**Output types:** Pass/fail + error list + severity

**Design rules:**
- Check schema compliance (required fields present, correct types)
- Check value ranges (confidence > 0, counts non-negative)
- Check logical consistency (no contradictions in output)
- Check completeness (no empty required fields)
- Return structured error list, not just boolean

**Validator template:**
```json
{
  "passed": false,
  "errors": [
    {"field": "confidence", "error": "below_minimum", "value": -0.1, "expected": ">= 0.0"},
    {"field": "findings", "error": "empty_array", "value": [], "expected": "at least 1 finding"}
  ],
  "severity": "blocking"
}
```

### Resolver
**Purpose:** Handles conflicts between agents or contradictory evidence.

**Deterministic?** SOMETIMES. Simple conflicts (newer > older) are deterministic. Complex conflicts may need LLM.

**Input types:** Conflicting outputs from two or more agents
**Output types:** Resolution decision + reasoning

**Design rules:**
- Always present both sides before deciding
- Log which resolution strategy was used
- If genuinely ambiguous, escalate to user — don't guess
- Prefer the source with higher confidence + more recent data

### Planner
**Purpose:** Decomposes complex goals into ordered subtasks.

**Deterministic?** For known domains, YES (template-based). For open-ended, needs LLM.

**Input types:** High-level goal + constraints
**Output types:** Ordered task list with dependencies

**Design rules:**
- Each subtask must be achievable by a single agent
- Include estimated cost per subtask
- Flag tasks that depend on external input (blocking)
- Maximum 10 subtasks — if more are needed, decompose recursively

### Executor
**Purpose:** Carries out a specific action (write file, call API, run command).

**Deterministic?** YES — Executors follow instructions, they don't decide.

**Input types:** Specific action specification from Planner or other agent
**Output types:** Action result + status

**Design rules:**
- Never decide what to do — only how to do it
- Always confirm action before executing if destructive
- Return full result including any errors
- Set timeouts on all external operations

## Archetype Combinations to Avoid

| Combination | Why It Fails |
|-------------|-------------|
| Perceiver + Analyzer | Perception should be pure extraction. Analysis requires different context. |
| Classifier + Synthesizer | Classification is routing, synthesis is combining. Different concerns. |
| Validator + Resolver | Validators detect problems, Resolvers fix them. Keep them separate for debuggability. |
| Planner + Executor | Planning is strategic, execution is tactical. Combining them creates agents that both decide and act with no checkpoint. |

## Typical Swarm Sizes

| Complexity | Agents | Deterministic % | API Calls |
|------------|--------|-----------------|-----------|
| Simple (single task) | 3-4 | 75-100% | 0-1 |
| Medium (analysis pipeline) | 5-7 | 60-80% | 1-2 |
| Complex (multi-domain) | 8-12 | 50-70% | 2-4 |
| Enterprise (full workflow) | 10-15 | 40-60% | 3-5 |

More agents is NOT better. Every agent adds latency, complexity, and potential failure points.
