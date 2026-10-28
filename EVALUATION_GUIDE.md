# Skill Evaluation Guide

A comprehensive guide to setting up and running evaluations for Claude skills using the evaluation framework built into skill-creator.

## Quick Start

### 1. Create evaluation prompts
```bash
# In your-skill/evals/evals.json
{
  "skill_name": "your-skill",
  "evals": [
    {
      "id": "eval-1",
      "name": "descriptive-name",
      "prompt": "User task prompt here",
      "expected_output": "What success looks like",
      "expectations": ["Assertion 1", "Assertion 2", "..."]
    }
  ]
}
```

### 2. Run evaluation
```bash
cd skills/skill-creator
python -m scripts.run_eval \
  --skill-path ../your-skill \
  --eval-file ../your-skill/evals/evals.json \
  --workspace ../your-skill/evaluation-workspace/iteration-1
```

### 3. Grade and benchmark
```bash
# Grade the results
python -m scripts.grade_evals \
  ../your-skill/evaluation-workspace/iteration-1 \
  --skill-name your-skill

# Generate benchmark report
python -m scripts.aggregate_benchmark \
  ../your-skill/evaluation-workspace/iteration-1 \
  --skill-name your-skill
```

### 4. View results
```bash
python eval-viewer/generate_review.py \
  ../your-skill/evaluation-workspace/iteration-1 \
  --skill-name your-skill \
  --benchmark ../your-skill/evaluation-workspace/iteration-1/benchmark.json
```

---

## Evaluation File Format (evals.json)

### Required Fields

```json
{
  "skill_name": "unique-skill-id",
  "description": "What this skill does and what these evals test",
  "evals": [
    {
      "id": "eval-1",
      "name": "descriptive-name-of-test",
      "prompt": "The exact user prompt to test",
      "expected_output": "Description of what success looks like",
      "expectations": [
        "Specific assertion 1",
        "Specific assertion 2"
      ]
    }
  ]
}
```

### Optional Fields

```json
{
  "files": ["input_file.pdf", "data.csv"],
  "context": "Additional context for the evaluator",
  "tags": ["objective", "complex-workflow", "edge-case"]
}
```

## Evaluation Types by Skill Category

### Document Skills (PDF, DOCX, PPTX, XLSX)

**Characteristics:**
- Objective outputs (files, data structures)
- Can be verified programmatically
- Quality criteria often quantifiable

**Example evals:**
```json
{
  "id": "eval-pdf-1",
  "name": "extract-invoice-data",
  "prompt": "Extract all line items and total from the invoice",
  "expected_output": "Table with item names, quantities, prices, totals",
  "files": ["sample_invoice.pdf"],
  "expectations": [
    "All line items extracted without omission",
    "Numbers correctly transcribed (±0.01 tolerance)",
    "Table properly formatted",
    "Totals match source PDF"
  ]
}
```

**Assertions to write:**
- Correctness checks (numbers match source within tolerance)
- Completeness checks (all expected items present)
- Format checks (proper table structure, column alignment)
- Integrity checks (no corruption, proper encoding)

### Workflow/Process Skills (skill-creator, doc-coauthoring, chief-of-staff)

**Characteristics:**
- Guide users through multi-step processes
- Output is guidance/structure, not final deliverable
- Quality measured by user understanding and next-step clarity

**Example evals:**
```json
{
  "id": "eval-workflow-1",
  "name": "onboarding-guide-planning",
  "prompt": "Help me plan writing an onboarding guide for new hires",
  "expected_output": "Structured plan including: audience analysis, scope definition, content outline, timeline",
  "expectations": [
    "Clarifying questions asked about audience and scope",
    "Existing gaps identified",
    "Clear next steps provided",
    "Realistic timeline estimate given"
  ]
}
```

**Assertions to write:**
- Completeness of guidance (all necessary stages covered)
- Clarity of next steps (user knows what to do)
- Quality of structure (logical flow, proper sequencing)
- Realism (suggestions are actionable, not generic)

### Creative/Design Skills (algorithmic-art, canvas-design, theme-factory)

**Characteristics:**
- Output is visual or stylistic
- Subjective quality criteria
- Better suited for qualitative feedback

**Example evals:**
```json
{
  "id": "eval-art-1",
  "name": "generative-art-philosophy",
  "prompt": "Create generative art based on a Fibonacci sequence philosophy",
  "expected_output": "Visual output that demonstrates understanding of the philosophy",
  "expectations": [
    "Code is syntactically correct (runs without errors)",
    "Visual output is deterministic (same seed = same output)",
    "Philosophy influences the visual characteristics"
  ]
}
```

**Assertions to write:**
- Technical correctness (code runs, no errors)
- Consistency (deterministic output)
- Property verification (uses expected libraries, outputs expected format)
- Avoid subjective assertions (beauty, elegance) — use qualitative feedback instead

### Integration/Building Skills (MCP-builder, webapp-testing, venture-builder)

**Characteristics:**
- Multi-step processes with technical requirements
- Mix of objective (code quality, API correctness) and subjective (design decisions)
- May have external dependencies

**Example evals:**
```json
{
  "id": "eval-build-1",
  "name": "simple-integration-flow",
  "prompt": "Walk me through building an MCP server that provides weather data",
  "expected_output": "Working MCP server code with documentation",
  "expectations": [
    "MCP protocol requirements understood",
    "Tool definition schema correct",
    "Error handling present",
    "Documentation explains setup steps",
    "Server starts without errors"
  ]
}
```

**Assertions to write:**
- Schema correctness (follows protocol spec)
- Functionality (tools execute as specified)
- Error handling (graceful failures, informative errors)
- Documentation completeness (setup, usage, troubleshooting)

---

## Assertions: Best Practices

### Good Assertions
- **Specific**: "Numbers match within ±0.01" not "correct"
- **Verifiable**: Can be checked programmatically or objectively
- **Non-overlapping**: Each tests one thing
- **Discriminating**: Would fail if skill broke

**Example:**
```
"All line items from source PDF are present (within 5% count tolerance)"
"Numbers are correct to 2 decimal places"
"Table columns are properly aligned (no text wrapping within cells)"
```

### Assertions to Avoid
- Too broad: "Output is good"
- Subjective without criteria: "Well-written" (unless you define what that means)
- Redundant: Two assertions testing the exact same thing
- Non-actionable: "There are no issues" (what would failure look like?)

### Subjective Feedback (Instead of Assertions)
For skills where quality judgment is needed, use qualitative feedback rather than assertions:

```json
{
  "id": "eval-writing-1",
  "name": "blog-post-coaching",
  "prompt": "Help me write a technical blog post about distributed systems",
  "expected_output": "Blog post draft with clear thesis, examples, and actionable insights",
  "expectations": [
    "Thesis is clearly stated in opening",
    "Examples are relevant and concrete",
    "Technical accuracy (concepts explained correctly)"
  ],
  "qualitative_feedback_prompts": [
    "Is the writing tone appropriate for a technical blog?",
    "Do examples help readers understand the concept?",
    "Would you recommend changes to the structure?"
  ]
}
```

---

## Running Evaluations: Step-by-Step

### Phase 1: Setup

1. **Create evals.json**
   - Write 2-3 representative test prompts
   - Include both happy path and edge cases
   - Keep prompts realistic (how users actually ask)

2. **Create eval_metadata.json** (for each eval)
   - Use exact path: `your-skill/evaluation-workspace/iteration-1/eval-{id}/eval_metadata.json`
   - Include prompt, expected output, assertions list

### Phase 2: Spawning Runs

Run both with-skill and baseline (without-skill) configurations:

```bash
# With skill
python -m scripts.run_eval \
  --skill-path /path/to/skill \
  --eval-file /path/to/skill/evals/evals.json \
  --workspace /path/to/skill/evaluation-workspace/iteration-1/eval-1/with_skill

# Without skill (baseline)
python -m scripts.run_eval \
  --eval-file /path/to/skill/evals/evals.json \
  --workspace /path/to/skill/evaluation-workspace/iteration-1/eval-1/without_skill \
  --no-skill
```

### Phase 3: Grading

After runs complete, grade each against assertions:

```bash
python -m scripts.grade_evals \
  /path/to/skill/evaluation-workspace/iteration-1 \
  --skill-name your-skill
```

This creates `grading.json` in each run directory with pass/fail for each assertion.

### Phase 4: Aggregation

Aggregate results across all evals:

```bash
python -m scripts.aggregate_benchmark \
  /path/to/skill/evaluation-workspace/iteration-1 \
  --skill-name your-skill
```

Output files:
- `benchmark.json` — Structured data (pass rates, tokens, timing)
- `benchmark.md` — Human-readable summary

### Phase 5: Review

Open the evaluation viewer:

```bash
python eval-viewer/generate_review.py \
  /path/to/skill/evaluation-workspace/iteration-1 \
  --skill-name your-skill \
  --benchmark /path/to/skill/evaluation-workspace/iteration-1/benchmark.json
```

For iteration 2+, also pass previous workspace:
```bash
--previous-workspace /path/to/skill/evaluation-workspace/iteration-1
```

---

## Understanding Benchmark Results

### Key Metrics

**Pass Rate**
- Percentage of assertions that passed
- With-skill should be significantly higher than baseline
- >90% indicates good performance
- 70-89% suggests room for improvement
- <70% may require significant revision

**Token Usage**
- Average tokens per run
- With-skill typically higher (richer guidance)
- Track ratio (with_skill / without_skill)
- 1.5x-2.0x is reasonable; >3x may indicate verbosity

**Duration**
- Time per run in seconds
- With-skill longer is expected
- Ratio >2.0x may indicate unnecessary complexity
- Look for high variance (flaky evals)

### Interpreting Pass Rates by Configuration

```
           with_skill    without_skill    Interpretation
Good       >90%          <70%             Skill is effective, baseline weak
Expected   80-90%        40-60%           Skill provides good improvement
Poor       <80%          >50%             Skill may not be adding much value
Suspicious >95%          >80%             Both too high, assertions may be too easy
```

### Red Flags

- **High variance** (stddev >20% of mean): Evals may be flaky or non-deterministic
- **Non-discriminating assertions**: Both with and without pass at same rate
- **Negative transfer**: with_skill performs worse than without (indicates harmful guidance)
- **Assertion failures**: If all evals fail specific assertion, likely a skill issue

---

## Iteration Workflow

### After First Evaluation

1. **Read feedback** from evaluation viewer
2. **Identify patterns** in failures
3. **Improve skill** based on root causes (not just test cases)
4. **Run iteration 2** with same evals
5. **Compare results** to iteration 1

### Improvement Strategies

**If pass rate is low (<70%):**
- Review failing assertions — are they testing the right thing?
- Read the actual outputs — what's going wrong?
- Rethink the core guidance in SKILL.md
- Add examples or clarify instructions

**If specific assertions always fail:**
- That assertion might not be testable objectively
- Consider reformulating as qualitative feedback
- Or make the guidance more explicit in SKILL.md

**If pass rate is good but user feedback is negative:**
- Assertions might be too permissive
- Add more discriminating assertions
- Run qualitative review with actual users

---

## Example Evaluations in Repository

Reference evaluations are provided for:

- **skill-creator**: `skills/skill-creator/evals/evals.json`
  - Tests workflow guidance, iteration coaching, optimization
  - Shows objective assertions for structured output

- **doc-coauthoring**: `skills/doc-coauthoring/evals/evals.json`
  - Tests multi-stage process guidance
  - Shows mixed objective (structure) and subjective (clarity) criteria

- **pdf**: `skills/pdf/evals/evals.json`
  - Tests document extraction and generation
  - Shows programmatically verifiable assertions

Reference outputs:
- Example grading: `skills/skill-creator/evals/example_grading.json`
- Example benchmark: `skills/skill-creator/evals/example_benchmark.json`

---

## Common Issues & Solutions

| Problem | Cause | Solution |
|---------|-------|----------|
| All evals pass equally with/without skill | Assertions too easy or not discriminating | Make assertions more specific, add edge cases to evals |
| High variance in results | Non-deterministic output or flaky eval | Add determinism where possible, review eval for ambiguity |
| Skill breaks existing functionality | Guidance too prescriptive or overlapping | Narrow skill scope, add "when NOT to use" guidance |
| Pass rate low but feedback positive | Assertions misaligned with actual goals | Revise assertions based on what matters to users |
| Token usage very high | Skill guidance too verbose or repetitive | Trim redundancy, move details to references/ |
| Setup/run scripts error | Python path or dependencies | Ensure `skill-creator/scripts/requirements.txt` installed |

---

## Tips for Effective Evaluations

1. **Start small**: 2-3 evals for initial iteration
2. **Make evals realistic**: Actual user language, realistic inputs
3. **Mix difficulty levels**: Include both straightforward and edge cases
4. **Don't over-engineer assertions**: Some things are better evaluated qualitatively
5. **Track patterns**: Note which evals fail consistently (signal vs. noise)
6. **Iterate quickly**: Small changes, re-run immediately
7. **Compare baselines**: Understanding why baseline fails is as important as why skill works
8. **Expand carefully**: After 2-3 good iterations, expand to 5-10 evals

---

## Next Steps

1. Read `skills/skill-creator/references/schemas.md` for exact JSON schema
2. Study examples in `skills/skill-creator/evals/evals.json`
3. Create evals for your skill following examples above
4. Run evaluation using skill-creator framework
5. Iterate based on results until satisfied

For questions about evaluation methodology, see `TESTING_EXAMPLES.md` for concrete test examples across skill types.

---

**Last Updated**: August 9, 2026  
**Framework**: skill-creator evaluation framework  
**Related Documentation**: `skills/skill-creator/SKILL.md`, `skills/skill-creator/references/schemas.md`, `TESTING_EXAMPLES.md`
