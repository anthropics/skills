# Swarm Design Examples

## Example 1: Code Review Swarm (5 Agents)

### Mission
"Review pull requests for bugs, security issues, and style violations."

### Architecture
```
Pattern: Sequential Chalkboard with Gate
Agents: 5 (4 deterministic, 1 API)
Est. cost: $0.02/review
```

### Agent Design
| # | Agent | Archetype | Deterministic | API | Input | Output |
|---|-------|-----------|---------------|-----|-------|--------|
| 1 | DiffParser | Perceiver | YES | 0 | Raw PR diff | Structured changes: files, hunks, additions, deletions |
| 2 | ComplexityGate | Validator | YES | 0 | Parsed diff | PASS if < 500 lines, REDIRECT to split if > 500 |
| 3 | PatternScanner | Analyzer | YES | 0 | Parsed diff | Known anti-patterns, security flags, style violations |
| 4 | ContextAnalyzer | Analyzer | NO | 1 | Flagged issues + surrounding code | Nuanced review: logic bugs, missing edge cases |
| 5 | ReviewSynthesizer | Synthesizer | NO | 0 | All findings | Formatted review comment with severity rankings |

### Pipeline
```
[PR Diff] → DiffParser → ComplexityGate ──PASS──→ PatternScanner → ContextAnalyzer → ReviewSynthesizer → [Review]
                               │
                            REDIRECT → "Split this PR into smaller changes"
```

### Chalkboard
```json
{
  "diff_parser": {
    "files_changed": 12,
    "lines_added": 145,
    "lines_deleted": 38,
    "hunks": [{"file": "auth.rs", "changes": [...]}]
  },
  "complexity_gate": {"passed": true, "total_lines": 183},
  "pattern_scanner": {
    "findings": [
      {"type": "security", "severity": "high", "file": "auth.rs", "line": 42, "pattern": "sql_concatenation"},
      {"type": "style", "severity": "low", "file": "utils.rs", "line": 15, "pattern": "unused_import"}
    ]
  },
  "context_analyzer": {
    "findings": [
      {"type": "logic", "severity": "medium", "file": "auth.rs", "line": 38, "issue": "Missing null check before database lookup"}
    ]
  },
  "review_synthesizer": {
    "summary": "1 critical security issue, 1 logic bug, 1 style nit",
    "blocking": true,
    "comments": [...]
  },
  "metadata": {"cost": 0.02, "api_calls": 1, "latency_ms": 890}
}
```

### Key Design Decisions
- DiffParser is pure code (git diff parsing) — no LLM needed
- PatternScanner uses regex + AST rules — catches 80% of issues at $0
- ContextAnalyzer only runs on flagged files — focused LLM call
- ReviewSynthesizer formats without API — template-based

---

## Example 2: Research Analysis Swarm (7 Agents)

### Mission
"Analyze research documents and produce structured insights with adversarial validation."

### Architecture
```
Pattern: Sequential Chalkboard with Adversarial Pair
Agents: 7 (4 deterministic, 3 API)
Est. cost: $0.08/document
```

### Agent Design
| # | Agent | Archetype | Deterministic | API | Input | Output |
|---|-------|-----------|---------------|-----|-------|--------|
| 1 | DocumentParser | Perceiver | YES | 0 | Raw document | Sections, claims, citations, data points |
| 2 | ClaimClassifier | Classifier | YES | 0 | Extracted claims | Claims tagged by type: factual, opinion, prediction |
| 3 | EvidenceMapper | Analyzer | NO | 1 | Claims + citations | Each claim mapped to supporting/opposing evidence |
| 4 | AdvocateAgent | Analyzer | NO | 1 | Evidence map | Strongest case FOR the document's conclusions |
| 5 | CriticAgent | Analyzer | NO | 1 | Evidence map | Strongest case AGAINST, gaps, missing evidence |
| 6 | ConflictResolver | Resolver | YES | 0 | Advocate + Critic | Point-by-point resolution with confidence |
| 7 | InsightWriter | Synthesizer | YES | 0 | Resolved analysis | Structured insight report |

### Pipeline
```
[Document] → DocumentParser → ClaimClassifier → EvidenceMapper
                                                       ↓
                                              ┌→ AdvocateAgent ─┐
                                              │                  ├→ ConflictResolver → InsightWriter → [Report]
                                              └→ CriticAgent ───┘
```

### Key Design Decisions
- Adversarial pair (Advocate + Critic) prevents confirmation bias
- ConflictResolver is deterministic — compares confidence scores and evidence counts
- InsightWriter uses templates, not LLM — consistent output format
- 3 API calls total, all focused on judgment tasks (evidence mapping, advocacy, criticism)

---

## Example 3: Customer Support Triage Swarm (4 Agents)

### Mission
"Classify incoming support tickets, estimate priority, and route to the right team."

### Architecture
```
Pattern: Pipeline with Gates
Agents: 4 (ALL deterministic)
Est. cost: $0.00/ticket
```

### Agent Design
| # | Agent | Archetype | Deterministic | API | Input | Output |
|---|-------|-----------|---------------|-----|-------|--------|
| 1 | TicketParser | Perceiver | YES | 0 | Raw ticket | Customer ID, product, issue text, sentiment |
| 2 | UrgencyGate | Validator | YES | 0 | Parsed ticket | Priority: P0 (immediate) → P3 (low) |
| 3 | TopicRouter | Classifier | YES | 0 | Parsed ticket | Team assignment: billing, technical, account, product |
| 4 | ResponseDrafter | Executor | YES | 0 | Routed ticket | Auto-acknowledgment with estimated response time |

### Pipeline
```
[Ticket] → TicketParser → UrgencyGate ──P0──→ [IMMEDIATE ALERT]
                               │
                             P1-P3 → TopicRouter → ResponseDrafter → [Queued + Auto-Reply]
```

### Key Design Decisions
- **Zero API calls** — all keyword-based classification + templates
- P0 tickets bypass the normal pipeline — direct alert
- This handles 70-80% of tickets. Only edge cases need human or LLM review.
- Perfect example of deterministic-first: solve the easy 80% for free

---

## Example 4: Debugging a Broken Swarm

### Symptom
"The InsightWriter produces empty reports even though other agents seem to work."

### Chalkboard Trace
```json
{
  "document_parser": {"sections": 5, "claims": 12, "citations": 8},     // ✅ Good
  "claim_classifier": {"factual": 7, "opinion": 3, "prediction": 2},    // ✅ Good
  "evidence_mapper": {"mapped_claims": 12, "with_evidence": 9},         // ✅ Good
  "advocate_agent": {"arguments": 4, "confidence": 0.85},               // ✅ Good
  "critic_agent": {"arguments": 3, "confidence": 0.72},                 // ✅ Good
  "conflict_resolver": {"resolutions": []},                              // ❌ EMPTY
  "insight_writer": {"report": ""}                                       // ❌ EMPTY (downstream)
}
```

### Diagnosis
1. InsightWriter is empty because ConflictResolver is empty — InsightWriter is NOT the problem
2. ConflictResolver received valid input (Advocate and Critic both produced output)
3. ConflictResolver's logic is the bug — check its resolution rules

### Root Cause
ConflictResolver expected field `advocate_agent.findings` but Advocate outputs `advocate_agent.arguments`. Schema mismatch.

### Fix
Update ConflictResolver to read `arguments` instead of `findings`, OR update AdvocateAgent to output `findings`. Then re-test.

### Lesson
This is why input validation matters. If ConflictResolver validated its input schema, it would have thrown a clear error instead of silently producing empty output.
