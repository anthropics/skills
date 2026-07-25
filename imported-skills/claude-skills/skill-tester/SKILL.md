---
name: "skill-tester"
description: "Validate, test, and score the quality of skills within the claude-skills ecosystem. Comprehensive meta-skill: structure validation, Python script testing (syntax + imports + runtime + output format), multi-dimensional quality scoring with letter grades and tier classification (BASIC/STANDARD/POWERFUL). Use when authoring a new skill, auditing existing skills for tier promotion, setting up pre-commit hooks for skill quality, or integrating skill QA into CI."
---

# Skill Tester

**Tier**: POWERFUL · **Category**: Engineering Quality Assurance · **Dependencies**: None (Python stdlib only)

Meta-skill that validates, tests, and scores skills in this repository. Four tools, run from the **repo root** with full paths:

1. **`scripts/skill_validator.py`** — structure + documentation compliance
2. **`scripts/script_tester.py`** — Python script syntax/imports/runtime/output testing
3. **`scripts/quality_scorer.py`** — multi-dimensional scoring with letter grade
4. **`scripts/security_scorer.py`** — security posture scoring (also available via `quality_scorer.py --include-security`)

> **Scope note:** this skill's tier line-count minimums measure *legacy* skills. For authoring *new* skills, `engineering/write-a-skill` (SKILL.md under ~100 lines, Matt Pocock doctrine) is the binding standard — do not pad a new skill to satisfy a tier minimum here.

## Quick Start (exact, runnable from repo root)

```bash
# 1. Validate structure (exit non-zero on failure — usable as a gate)
python3 engineering/skills/skill-tester/scripts/skill_validator.py engineering/skills/self-eval --json

# 2. Test the skill's Python scripts (30s default timeout per script)
python3 engineering/skills/skill-tester/scripts/script_tester.py engineering/skills/self-eval --json

# 3. Score quality (fail CI below threshold with --minimum-score)
python3 engineering/skills/skill-tester/scripts/quality_scorer.py engineering/skills/self-eval --json --detailed --minimum-score 75
```

Consume the JSON: validator emits `overall_score`, `compliance_level`, per-check `checks{}`; scorer emits `overall_score`, `letter_grade`, `tier_recommendation`, `dimensions`, and an `improvement_roadmap` — work the roadmap top-down, then re-run until the target score is met.

For repo-wide auditing prefer `scripts/audit_skills.py` at the repo root (wraps the write-a-skill checklist runner across all skills).

## What Each Tool Checks

### skill_validator.py
- SKILL.md frontmatter parsing, required sections, minimum line counts per tier (`--tier BASIC|STANDARD|POWERFUL`)
- Required structure: SKILL.md, README.md, scripts/, references/, assets/, expected_outputs/
- Python scripts: argparse present, stdlib-only imports

### script_tester.py
- AST-based syntax validation; import analysis (flags external dependencies)
- Controlled execution with timeout protection (`--timeout`, default 30s)
- `--help` functionality verification; sample-data runs compared against expected_outputs/

### quality_scorer.py
Four dimensions, 25% each: **Documentation** (depth, examples, references), **Code Quality** (complexity, error handling, output consistency), **Completeness** (required dirs, sample data, expected outputs), **Usability** (help text, example clarity). Outputs 0-100 + A-F grade + tier recommendation.

## Tier Classification

| Tier | SKILL.md | Scripts | CLI surface |
|---|---|---|---|
| BASIC | ≥ 100 lines | 1 (100-300 LOC) | basic argparse |
| STANDARD | ≥ 200 lines | 1-2 (300-500 LOC) | subcommands, JSON + text output |
| POWERFUL | ≥ 300 lines | 2-3 (500-800 LOC) | multiple modes, CI integration |

(Advisory for legacy skills; new skills follow write-a-skill — see scope note above.)

## CI Integration

```yaml
# GitHub Actions: gate changed skills
- name: "validate-changed-skills"
  run: |
    for skill in $changed_skills; do
      python3 engineering/skills/skill-tester/scripts/skill_validator.py "$skill" --json
      python3 engineering/skills/skill-tester/scripts/script_tester.py "$skill"
      python3 engineering/skills/skill-tester/scripts/quality_scorer.py "$skill" --minimum-score 75
    done
```

Pre-commit hook: run the validator on the staged skill directory and block the commit on non-zero exit.

## Verification Loop

A skill "passes" when, in one run from repo root:

1. `skill_validator.py <skill> --json` exits 0,
2. `script_tester.py <skill>` reports all scripts passing, and
3. `quality_scorer.py <skill> --minimum-score <target>` exits 0.

If any step fails, apply the top `improvement_roadmap` item and re-run all three — never report a partial pass.

## Troubleshooting

- **Timeout errors** → raise `--timeout` or optimize the script under test
- **Import failures** → external deps detected; stdlib-only is the repo policy
- **Tier misclassification** → check line counts/LOC against the tier table; remember the write-a-skill exception for new skills

References: `references/` holds the structure specification, tier requirements matrix, and scoring rubric the tools implement.
