# program.md Templates

Copy the template for your domain and paste into your project root as `program.md`.

---

## ML Training (Karpathy-style)

```markdown
# autoresearch — ML Training

## Goal
Minimize val_bpb on the validation set. Lower is better.

## What You Can Change (train.py only)
- Model architecture (depth, width, attention heads, FFN ratio)
- Optimizer (learning rate, warmup, scheduler, weight decay)
- Training loop (batch size, gradient accumulation, clipping)
- Regularization (dropout, weight tying, etc.)
- Any self-contained improvement that doesn't require new packages

## What You Cannot Change
- prepare.py (fixed — contains evaluation harness)
- Dependencies (pyproject.toml is locked)
- Time budget (always 5 minutes, wall clock)
- Evaluation metric (val_bpb is the ground truth)

## Strategy
1. First run: establish baseline. Do not change anything.
2. Explore learning rate range (try 2x and 0.5x current)
3. Try depth changes (±2 layers)
4. Try optimizer changes (Muon vs. AdamW variants)
5. If things improve, double down. If stuck, try something radical.

## Simplicity Rule
A small improvement with ugly code is NOT worth it.
Equal performance with simpler code IS worth it.
Removing code that gets same results is the best outcome.

## Stop When
val_bpb < 0.95 OR after 100 experiments, whichever comes first.
```

---

## Prompt Engineering

```markdown
# autoresearch — Prompt Optimization

## Goal
Maximize eval_score on the test suite. Higher is better (0-100).

## What You Can Change (prompt.md only)
- System prompt instructions
- Examples and few-shot demonstrations
- Output format specifications
- Chain-of-thought instructions
- Persona and tone
- Task decomposition strategies

## What You Cannot Change
- evaluate.py (fixed evaluation harness)
- Test cases in tests/ (ground truth)
- Model being evaluated (specified in evaluate.py)
- Scoring criteria (defined in evaluate.py)

## Strategy
1. First run: baseline with current prompt (or empty)
2. Add clear role/persona definition
3. Add output format specification
4. Add chain-of-thought instruction
5. Add 2-3 diverse examples
6. Refine based on failure modes from run.log

## Evaluation
- evaluate.py runs the prompt against 20 test cases
- Each test case is scored 1-10 by your CLI tool (Claude, Codex, or Gemini)
- quality_score = average * 10 (maps to 10-100)
- Run log shows which test cases failed

## Stop When
eval_score >= 85 OR after 50 experiments.
```

---

## Code Performance

```markdown
# autoresearch — Performance Optimization

## Goal
Minimize p50_ms (median latency). Lower is better.

## What You Can Change (src/module.py only)
- Algorithm implementation
- Data structures (use faster alternatives)
- Caching and memoization
- Vectorization (NumPy, etc.)
- Loop optimization
- I/O patterns
- Memory allocation patterns

## What You Cannot Change
- benchmark.py (fixed benchmark harness)
- Public API (function signatures must stay the same)
- External dependencies (add nothing new)
- Correctness tests (tests/ must still pass)

## Constraints
- Correctness is non-negotiable. benchmark.py runs tests first.
- If tests fail → immediate crash status, no metric recorded.
- Memory usage: p99 < 2x baseline acceptable, hard limit at 4x.

## Strategy
1. Baseline: profile first, don't guess
2. Check if there's any O(n²) → O(n log n) opportunity
3. Try caching repeated computations
4. Try NumPy vectorization for loops
5. Try algorithm-level changes last (higher risk)

## Stop When
p50_ms < 50ms OR improvement plateaus for 10 consecutive experiments.
```

---

## Agent Skill Optimization

```markdown
# autoresearch — Skill Optimization

## Goal
Maximize pass_rate on the task evaluation suite. Higher is better (0-1).

## What You Can Change (SKILL.md only)
- Skill description and trigger phrases
- Core workflow steps and ordering
- Decision frameworks and rules
- Output format specifications
- Example inputs/outputs
- Related skills disambiguation
- Proactive trigger conditions

## What You Cannot Change
- your custom evaluate.py (see Custom Evaluators in SKILL.md)
- Test tasks in tests/ (ground truth benchmark)
- Skill name (used for routing)
- License or metadata

## Evaluation
- evaluate.py runs SKILL.md against 15 standardized tasks
- Your CLI tool scores each task: 0 (fail), 0.5 (partial), 1 (pass)
- pass_rate = sum(scores) / 15

## Strategy
1. Baseline: run as-is
2. Improve trigger description (better routing = more passes)
3. Sharpen the core workflow (clearer = better execution)
4. Add missing edge cases to the rules section
5. Improve disambiguation (reduce false-positive routing)

## Simplicity Rule
A shorter SKILL.md that achieves the same score is better.
Aim for 200-400 lines total.

## Stop When
pass_rate >= 0.90 OR after 30 experiments.
```
