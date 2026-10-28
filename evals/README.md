# Skill Evaluations

This directory contains example evaluation files and guidance for testing Claude skills using the skill-creator evaluation framework.

## What Are Skill Evaluations?

Skill evaluations are structured tests that measure whether a skill helps Claude perform a task better than without the skill. They include:

- **Test prompts** (user requests to test the skill against)
- **Expected outputs** (what success looks like)
- **Assertions** (specific criteria to verify)
- **Results** (pass/fail data, token usage, timing)

## Quick Start

1. **Read** the main evaluation guide: [`EVALUATION_GUIDE.md`](../EVALUATION_GUIDE.md)
2. **Study examples** in skill directories:
   - `skills/skill-creator/evals/evals.json` — Workflow skill evaluations
   - `skills/doc-coauthoring/evals/evals.json` — Multi-stage process evaluations
   - `skills/pdf/evals/evals.json` — Document processing evaluations
3. **Create your own**: Copy an example and adapt for your skill
4. **Run**: Use skill-creator's evaluation framework (see guide)

## Example Files

### Evaluation Prompts (evals.json)

Each skill should have `evals/evals.json` with 2-3 test cases:

```json
{
  "skill_name": "your-skill",
  "evals": [
    {
      "id": "eval-1",
      "name": "descriptive-test-name",
      "prompt": "What the user asks the skill to do",
      "expected_output": "Description of success",
      "expectations": [
        "Specific assertion 1",
        "Specific assertion 2"
      ]
    }
  ]
}
```

### Grading Results (grading.json)

After running evaluations, grading shows pass/fail for each assertion:

```json
{
  "eval_id": "eval-1",
  "expectations": [
    {
      "text": "Assertion text",
      "passed": true,
      "evidence": "Why this passed/failed"
    }
  ],
  "overall_pass_rate": 1.0
}
```

### Aggregated Benchmark (benchmark.json)

Summary statistics across all evals, comparing with-skill vs. without-skill:

```json
{
  "aggregate_metrics": {
    "with_skill": {
      "pass_rate": 0.95,
      "avg_tokens": 3847,
      "avg_duration_seconds": 18.3
    },
    "without_skill": {
      "pass_rate": 0.62,
      "avg_tokens": 2156,
      "avg_duration_seconds": 12.4
    }
  }
}
```

## Evaluation Types

### Document Skills (PDF, DOCX, PPTX, XLSX)
**Best for:** Objective, verifiable outputs (extracted data, formatted files)
**Assertion type:** Technical correctness (numbers match, format correct, completeness)
**Example:** Extracting invoice line items with exact amounts

### Workflow/Process Skills (skill-creator, doc-coauthoring, venture-builder)
**Best for:** Guiding users through multi-step processes
**Assertion type:** Completeness (all stages covered), clarity (next steps clear), realism
**Example:** Walking user through 3 stages of document planning

### Creative/Design Skills (algorithmic-art, canvas-design, theme-factory)
**Best for:** Visual or stylistic output
**Assertion type:** Technical correctness (code runs), property verification
**Qualitative feedback:** Use for aesthetic/design quality

### Integration/Building Skills (MCP-builder, webapp-testing)
**Best for:** Technical implementations with requirements
**Assertion type:** Schema correctness, functionality, error handling, docs

## Creating Evaluations for Your Skill

### Step 1: Design Test Cases
- What are 2-3 realistic user requests?
- Cover: happy path, edge case, difficult case
- Use actual user language (not abstract)

### Step 2: Define Success
- What does good output look like?
- What's non-negotiable vs. nice-to-have?
- How would you verify it?

### Step 3: Write Assertions
- Be specific: "Names extracted without typos" not "works well"
- Make testable: Could you check this programmatically?
- Avoid overlap: Each assertion tests one thing
- Keep it lean: 3-5 assertions per eval

### Step 4: Save and Run
```bash
# Save to: skills/your-skill/evals/evals.json
# Run from: skills/skill-creator/
python -m scripts.run_eval \
  --skill-path ../your-skill \
  --eval-file ../your-skill/evals/evals.json \
  --workspace ../your-skill/evaluation-workspace/iteration-1
```

## Evaluating Results

### Benchmark Interpretation

| Metric | What to Look For |
|--------|------------------|
| Pass Rate | With-skill should be 15-35% higher than without-skill |
| Token Usage | With-skill 1.5-2.0x baseline is normal |
| Duration | With-skill 1.5-2.5x baseline is expected |
| High Variance | Evals might be flaky; review for ambiguity |

### Red Flags
- **Both pass equally** → Assertions too easy
- **Skill performs worse** → Guidance may be confusing or contradictory
- **One assertion always fails** → Likely a skill issue, not test issue

## File Structure

```
your-skill/
├── evals/
│   ├── evals.json                          # Test prompts and expected outputs
│   ├── example_grading.json                # (Optional) Reference grading output
│   └── example_benchmark.json              # (Optional) Reference benchmark output
└── evaluation-workspace/                   # (Created by evaluation script)
    └── iteration-1/
        ├── eval-1/
        │   ├── with_skill/outputs/         # Outputs when using skill
        │   ├── without_skill/outputs/      # Outputs without skill (baseline)
        │   └── eval_metadata.json          # Test metadata and results
        ├── benchmark.json                  # Aggregated results
        ├── benchmark.md                    # Human-readable summary
        └── feedback.json                   # User feedback from evaluation viewer
```

## Next Steps

1. **For new skills**: Start with 2-3 simple evals, then iterate
2. **For existing skills**: Create evals to verify current behavior, then improve
3. **For complex skills**: Break into multiple focused evaluations
4. **For documentation**: Add examples and reference outputs

See [`EVALUATION_GUIDE.md`](../EVALUATION_GUIDE.md) for comprehensive walkthrough and [`skills/skill-creator/SKILL.md`](../skills/skill-creator/SKILL.md) for detailed framework documentation.

---

**Last Updated**: August 9, 2026  
**Framework**: skill-creator evaluation system  
**Key References**: 
- Main guide: `EVALUATION_GUIDE.md`
- Skill framework: `skills/skill-creator/SKILL.md`
- Schema details: `skills/skill-creator/references/schemas.md`
- Testing examples: `TESTING_EXAMPLES.md`
