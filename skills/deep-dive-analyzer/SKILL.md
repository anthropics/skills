---
name: deep-dive-analyzer
description: Microscopic deconstruction and exhaustive analysis of code, systems, documents, or concepts. Breaks subjects into atomic components, examines every facet, and produces encyclopedic reports. Use when deep understanding is needed before making changes, analyzing unfamiliar codebases, or producing thorough technical documentation. Triggers on "심층 분석", "deep dive", "분석해줘", "해부", "deconstruct", "뜯어봐", "thoroughly analyze", "코드 분석".
argument-hint: "[file, system, concept, or codebase to analyze]"
allowed-tools: Read, Grep, Glob, Bash, Agent
---

# Deep Dive Analyzer

Microscopic deconstruction engine for exhaustive analysis.

> - Loti Codex Engine: 5-part academic structure (Thesis → Multi-Vector → Terminology → Causal → Conclusion)
> - Ailey Microscopic Analyst mode: atomic deconstruction of structure
> - Neutral-Persona: Micro-Analytic Expansion Engine (encyclopedic depth)
> - Hybrid Analysis Mode: full-structure analytical deconstruction

## Rules (Absolute)

1. **Exhaust all components.** Every constituent building block must be examined before concluding. No "and so on" or "etc."
2. **Define before use.** Every domain-specific term must be defined at first appearance.
3. **Depth over breadth.** Go deep on fewer topics rather than shallow on many. If time-constrained, explicitly note what was deferred.
4. **Evidence-based.** Every claim about the analyzed subject must reference specific code lines, config values, or documented behavior.
5. **Structure follows subject.** The analysis format adapts to what's being analyzed — code gets different treatment than architecture.

## Analysis Modes

### Mode A: Code Analysis
For analyzing specific files, functions, or modules.

**Process:**
1. **Read** all relevant files with the Read tool
2. **Map** the dependency graph (imports, calls, data flow)
3. **Decompose** each function/class into atomic responsibilities
4. **Evaluate** against principles (SRP, DRY, coupling, cohesion)
5. **Trace** data flow from input to output
6. **Identify** patterns, anti-patterns, and hidden assumptions

**Output structure:**
```markdown
## Code Analysis: [file/module]

### Overview
- **Purpose:** [what this code does]
- **Complexity:** [LOC, cyclomatic complexity estimate, dependency count]
- **Key Dependencies:** [critical imports and their roles]

### Architecture Map
```
[ASCII diagram of component relationships]
```

### Component Breakdown
#### [Component 1]
- **Responsibility:** [SRP description]
- **Input:** [what it receives]
- **Output:** [what it produces]
- **Internal Logic:** [step-by-step breakdown]
- **Edge Cases:** [identified boundary conditions]
- **Concerns:** [potential issues]

### Data Flow
[Input] → [Transform 1] → [Transform 2] → [Output]

### Findings
| ID | Category | Severity | Description | Location |
|----|----------|----------|-------------|----------|
| 1  | [type]   | [level]  | [detail]    | [file:line] |

### Recommendations
[Prioritized list of improvements]
```

### Mode B: System Analysis
For analyzing architectures, infrastructure, or multi-service systems.

**Process:**
1. **Map** all system components and their interactions
2. **Identify** data flows, protocols, and integration points
3. **Evaluate** scalability, reliability, and security posture
4. **Stress-test** mentally with failure scenarios
5. **Compare** against established architectural patterns

**Output structure:**
```markdown
## System Analysis: [system name]

### Architecture Overview
[High-level description + ASCII diagram]

### Component Registry
| Component | Type | Responsibility | Dependencies | Health |
|-----------|------|---------------|--------------|--------|

### Data Flow Analysis
[How data moves through the system, including edge cases]

### Failure Mode Analysis
| Failure Scenario | Impact | Current Mitigation | Gap |
|-----------------|--------|-------------------|-----|

### Scalability Assessment
[Current limits, bottlenecks, scaling strategy]

### Security Surface
[Attack vectors, authentication flow, data protection]
```

### Mode C: Concept Analysis
For analyzing technical concepts, frameworks, or methodologies.

**Process (5-Part Codex Structure):**

Inspired by Loti's Codex Engine academic paper structure:

1. **Thesis:** Core definition and significance (what is it, why does it matter)
2. **Multi-Vector Analysis:** Examine from 3+ independent perspectives
3. **Terminology Map:** Define all key terms and their relationships
4. **Causal Chain:** How did this emerge? What does it enable? What are the consequences?
5. **Synthesis:** Integrated understanding with practical implications

**Output structure:**
```markdown
## Concept Analysis: [topic]

### 1. Thesis
[Core definition and why it matters — 2-3 paragraphs]

### 2. Multi-Vector Analysis

#### Perspective A: [Technical]
[Analysis from technical standpoint]

#### Perspective B: [Practical]
[Analysis from practitioner standpoint]

#### Perspective C: [Historical/Ecosystem]
[Analysis from evolution standpoint]

### 3. Terminology Map
| Term | Definition | Relationship |
|------|-----------|--------------|

### 4. Causal Chain
[Predecessor] → [This concept] → [What it enables]
                      ↓
              [Side effects / Trade-offs]

### 5. Synthesis
[Integrated understanding + practical takeaways]
```

## When to Use

- Before modifying unfamiliar code — understand first, change later
- Evaluating whether to adopt a technology or framework
- Onboarding to a new codebase or project
- Producing technical documentation or architecture guides
- When someone asks "how does X work?" and the answer is non-trivial
- Post-incident analysis of complex failures

## When NOT to Use

- Simple code that's self-explanatory
- When speed matters more than depth (use quick Read instead)
- For decision-making (use `creativity-sampler` or `adversarial-review`)
- For fact-checking (use `cross-verified-research`)

## Integration Notes

- **Before adversarial-review:** Deep dive first to understand, then adversarial-review to challenge
- **Before creativity-sampler:** Understand the problem space deeply, then explore alternatives
- **With skill-composer:** Commonly the first step in research-to-decision pipelines
