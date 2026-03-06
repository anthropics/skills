---
name: creativity-sampler
description: Generate exactly 5 probability-weighted options for a specific decision point. Forces unconventional alternatives beyond safe defaults. For quick decision-point analysis, NOT full design exploration (use brainstorming for that). Triggers on "대안", "alternatives", "옵션 뽑아", "options", "어떤 방법이", "아이디어", "다른 방법", "선택지".
argument-hint: "[decision or question to explore]"
---

# Creativity Sampler

Probability-weighted option generator that fights typicality bias and surfaces unconventional alternatives.


## Rules (Absolute)

1. **Always generate exactly 5 options.** No more, no less. k=5 is the magic number for decision diversity without overload.
2. **At least 1 option must be unconventional** (probability < 10%). This is the whole point — surface ideas that would normally be suppressed.
3. **Assign relative probabilities** that sum to ~100%. These represent "how likely a typical AI would suggest this", NOT recommendation strength.
4. **Lower probability = more creative**, not worse. Explicitly frame low-p options as valuable exploration.
5. **No default recommendation.** Present all 5 as viable. Let the user decide after seeing trade-offs.
6. **Trade-off analysis is mandatory.** Each option must have concrete pros/cons, not vague descriptions.

## Process

### Step 1: Frame the Decision Space

Identify:
- What is being decided? (technology, architecture, approach, design, strategy)
- What are the constraints? (time, budget, team skill, existing stack)
- What would the "obvious" answer be? (this is what we want to challenge)

### Step 2: Generate 5 Options (Distribution-First)

Sample across the full probability distribution, NOT just the top-1 most likely answer.

```
Distribution zones:
  p > 40%  — Conventional (the "obvious" choice most would pick)
  p 20-40% — Mainstream alternative (commonly considered)
  p 10-20% — Less common (valid but often overlooked)
  p 5-10%  — Unconventional (challenges assumptions)
  p < 5%   — Wild card (radical rethink, paradigm shift)
```

Force at least one option from each of the bottom two zones.

### Step 3: Analyze Each Option

For every option, provide:
1. **What it is** (1 sentence)
2. **Why it might be the best choice** (strongest argument FOR)
3. **Why it might fail** (strongest argument AGAINST)
4. **Best suited when...** (specific scenario where this option wins)
5. **Estimated effort** relative to other options (Low / Medium / High)

### Step 4: Surface Hidden Assumptions

After presenting all 5, explicitly state:
- "The conventional choice assumes [X]. If that assumption is wrong, consider options [Y, Z]."
- Identify which constraints, if removed, would change the ranking.

## Output Format

```markdown
## Decision: [The question being decided]

### Constraints
- [constraint 1]
- [constraint 2]

### Options

#### 1. [Option Name] — p ≈ XX%
> [One-line description]

| Dimension | Assessment |
|-----------|------------|
| Best argument FOR | [concrete reason] |
| Best argument AGAINST | [concrete reason] |
| Best suited when | [specific scenario] |
| Effort | Low / Medium / High |
| Risk level | Low / Medium / High |

#### 2. [Option Name] — p ≈ XX%
> ...

#### 3. [Option Name] — p ≈ XX%
> ...

#### 4. [Option Name] — p ≈ XX%
> ...

#### 5. [Option Name] — p ≈ XX% ⚡ Unconventional
> ...

### Hidden Assumptions
- The conventional choice (Option 1) assumes: [assumption]
- If [condition changes], reconsider: Option [N]

### Decision Matrix
| Criteria | Opt 1 | Opt 2 | Opt 3 | Opt 4 | Opt 5 |
|----------|-------|-------|-------|-------|-------|
| [criteria 1] | rating | ... | ... | ... | ... |
| [criteria 2] | rating | ... | ... | ... | ... |
| [criteria 3] | rating | ... | ... | ... | ... |
```

## When to Use

- Architecture decisions: "monolith vs microservices vs..."
- Technology selection: "which database/framework/language"
- Design approaches: "how should we structure this feature"
- Strategy: "how should we launch/market/scale this"
- Problem-solving: "how can we fix/improve/optimize this"
- Any moment where you catch yourself defaulting to one obvious answer

## When NOT to Use

- Factual questions with one correct answer (use `cross-verified-research`)
- Tasks with clear requirements and no decision points
- Simple implementation where the approach is obvious and uncontested
- When user has already decided and just wants execution

## Integration Notes

- **With brainstorming:** Can replace the "Propose 2-3 approaches" phase with 5 deeper options
- **With adversarial-review:** Feed the chosen option into adversarial review for stress-testing
- **Standalone:** Invoke directly with `/creativity-sampler [question]` for quick decision support

## Anti-Patterns to Avoid

- **False diversity:** Don't generate 5 options that are minor variations of the same thing. Each option should represent a fundamentally different approach.
- **Probability theater:** Don't assign probabilities randomly. Base them on actual prevalence in industry/community.
- **Burying the lead:** If one option is dramatically better given the constraints, say so in Hidden Assumptions — but still present all 5 fairly.
- **Ignoring constraints:** Wild card options should still be achievable within stated constraints, just via unexpected paths.
