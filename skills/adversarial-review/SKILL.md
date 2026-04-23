---
name: adversarial-review
description: Devil's Advocate stress-testing for code, architecture, PRs, and decisions. Surfaces hidden flaws through structured adversarial analysis with metacognitive depth. Use for high-stakes review, stress-testing choices, or when the user wants problems found deliberately. NOT for routine code review (use engineering:code-review). Triggers on "스트레스 테스트", "stress test", "devil's advocate", "반론", "이거 괜찮아", "문제 없을까", "깊은 리뷰", "critical review", "adversarial".
argument-hint: "[code/decision/PR to stress-test]"
allowed-tools: Read, Grep, Glob, Bash, Agent
---

# Adversarial Review

Structured Devil's Advocate analysis that surfaces hidden flaws, edge cases, and blind spots.


## Rules (Absolute)

1. **Always find problems.** Even if the code/decision looks good, find at least 3 substantive concerns. "Looks good to me" is not an acceptable output.
2. **Attack the strongest points.** Don't waste time on trivial issues. Target the parts the author is most confident about — that's where hidden assumptions live.
3. **Separate severity levels.** Not all issues are equal. Clearly distinguish critical from minor.
4. **Propose alternatives.** Every criticism must include a concrete alternative or mitigation.
5. **Steel-man first.** Before attacking, state the strongest version of why the current approach was chosen. This prevents straw-man critiques.
6. **No ad hominem.** Critique the work, not the author. Be sharp but constructive.

## Process

### Phase 1: Steel-Man

Before any criticism, articulate:
- **Why was this approach chosen?** (Best possible justification)
- **What does it optimize for?** (Performance? Simplicity? Time-to-market?)
- **Under what conditions is this the right choice?**

This ensures the subsequent critique is intellectually honest, not reflexive opposition.

### Phase 2: Adversarial Attack (3 Vectors)

Apply three independent attack vectors simultaneously:

#### Vector A: Logical Soundness
Inspired by the Logical Adjudicator — pure logical analysis:
- Are there logical contradictions?
- Does the reasoning follow from the premises?
- Are there unstated assumptions that could be false?
- Is there circular reasoning or confirmation bias?

#### Vector B: Edge Case Assault
Inspired by Bailey's critical inquiry DNA — find the cracks:
- What happens at boundaries? (empty input, max load, concurrent access)
- What's the failure mode? (graceful degradation vs. catastrophic failure)
- What happens in 6 months? (scaling, maintenance, team changes)
- What would a malicious actor do with this?

#### Vector C: Microscopic Deconstruction
Inspired by Ailey's Microscopic Analyst — atomic-level analysis:
- Break the system into its smallest components
- Examine each component's single responsibility
- Identify coupling points and dependency chains
- Find the weakest link in the chain

### Phase 3: Severity Classification

Classify every finding:

| Severity | Symbol | Meaning | Action Required |
|----------|--------|---------|-----------------|
| Critical | `🔴` | Will cause production issues, security vulnerabilities, or data loss | Must fix before merge/deploy |
| Major | `🟠` | Significant risk, performance issue, or maintainability problem | Should fix, blocking for merge |
| Minor | `🟡` | Code smell, style issue, or small optimization opportunity | Consider fixing, non-blocking |
| Note | `💡` | Observation, alternative approach, or future consideration | Informational only |

### Phase 4: Counter-Proposal

For each Critical and Major finding, provide:
1. **What's wrong** (1-2 sentences)
2. **Why it matters** (concrete impact)
3. **Suggested fix** (code snippet or approach)
4. **Trade-off of the fix** (nothing is free — what does the fix cost?)

## Output Format

```markdown
## Adversarial Review: [Subject]

### Steel-Man
> [Why this approach makes sense — strongest justification]

### Findings

#### 🔴 Critical: [Title]
**Vector:** [Logical / Edge Case / Microscopic]
**What:** [Description]
**Impact:** [Concrete consequence]
**Fix:** [Proposed solution]
**Trade-off:** [Cost of the fix]

#### 🟠 Major: [Title]
...

#### 🟡 Minor: [Title]
...

#### 💡 Note: [Title]
...

### Summary
| Severity | Count |
|----------|-------|
| 🔴 Critical | N |
| 🟠 Major | N |
| 🟡 Minor | N |
| 💡 Note | N |

### Verdict
[PASS / PASS WITH CONDITIONS / FAIL]
- [If PASS WITH CONDITIONS: list required changes]
- [If FAIL: list blocking issues]

### Hidden Assumptions Exposed
- [Assumption 1 that the current approach relies on]
- [Assumption 2 that could invalidate the approach if wrong]
```

## Specialized Modes

### Code Review Mode
When reviewing code (files, PRs, diffs):
- Read all changed files with the Read tool
- Check for OWASP Top 10 vulnerabilities
- Verify error handling completeness
- Assess test coverage of edge cases
- Review naming, structure, and abstraction levels

### Architecture Decision Mode
When reviewing architecture/design decisions:
- Evaluate scalability assumptions
- Test with 10x and 100x current load mentally
- Check for single points of failure
- Assess vendor lock-in risks
- Consider team capability alignment

### PR Review Mode
When reviewing pull requests:
- Focus on behavioral changes, not style
- Check for breaking changes to public APIs
- Verify backward compatibility
- Assess rollback strategy
- Check migration paths for data changes

## When to Use

- Before merging any significant PR
- Before committing to an architecture decision
- When evaluating third-party dependencies
- When someone says "this should be fine"
- When stakes are high and mistakes are expensive
- After completing implementation, before calling it done

## When NOT to Use

- Trivial changes (typos, formatting)
- When exploration is needed first (use `cross-verified-research`)
- When generating alternatives (use `creativity-sampler`)
- Personal preferences or subjective design choices

## Integration Notes

- **With creativity-sampler:** After adversarial review reveals problems, use creativity-sampler to generate alternative approaches
- **With cross-verified-research:** Use research to verify claims made during review (e.g., "is this really a security risk?")
- **With orchestrator strategy team:** Complements the strategy team's Devil's Advocate agent with structured methodology
