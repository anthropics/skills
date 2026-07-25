# Skill Tester - Quality Assurance Meta-Skill

A POWERFUL-tier skill that provides comprehensive validation, testing, and quality scoring for skills in the claude-skills ecosystem.

## Overview

The Skill Tester is a meta-skill that ensures quality and consistency across all skills in the repository through:

- **Structure Validation** - Verifies directory structure, file presence, and documentation standards
- **Script Testing** - Tests Python scripts for syntax, functionality, and compliance
- **Quality Scoring** - Provides comprehensive quality assessment across multiple dimensions

## Quick Start

### Validate a Skill
```bash
# Basic validation
python scripts/skill_validator.py engineering/my-skill

# Validate against specific tier
python scripts/skill_validator.py engineering/my-skill --tier POWERFUL --json
```

### Test Scripts
```bash
# Test all scripts in a skill
python scripts/script_tester.py engineering/my-skill

# Test with custom timeout
python scripts/script_tester.py engineering/my-skill --timeout 60 --json
```

### Score Quality
```bash
# Get quality assessment
python scripts/quality_scorer.py engineering/my-skill

# Detailed scoring with improvement suggestions
python scripts/quality_scorer.py engineering/my-skill --detailed --json
```

## Components

### Scripts
- **skill_validator.py** (700+ LOC) - Validates skill structure and compliance
- **script_tester.py** (800+ LOC) - Tests script functionality and quality
- **quality_scorer.py** (1100+ LOC) - Multi-dimensional quality assessment

### Reference Documentation
- **skill-structure-specification.md** - Complete structural requirements
- **tier-requirements-matrix.md** - Tier-specific quality standards
- **quality-scoring-rubric.md** - Detailed scoring methodology

### Sample Assets
- **sample-skill/** - Complete sample skill for testing the tester itself

## Features

### Validation Capabilities
- SKILL.md format and content validation
- Directory structure compliance checking
- Python script syntax and import validation
- Argparse implementation verification
- Tier-specific requirement enforcement

### Testing Framework
- Syntax validation using AST parsing
- Import analysis for external dependencies
- Runtime execution testing with timeout protection
- Help functionality verification
- Sample data processing validation
- Output format compliance checking

### Quality Assessment
- Documentation quality scoring (25%)
- Code quality evaluation (25%)  
- Completeness assessment (25%)
- Usability analysis (25%)
- Letter grade assignment (A+ to F)
- Tier recommendation generation
- Improvement roadmap creation

## CI/CD Integration

### GitHub Actions Example
```yaml
name: Skill Quality Gate
on:
  pull_request:
    paths: ['engineering/**']
    
jobs:
  validate-skills:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - name: Setup Python
        uses: actions/setup-python@v4
        with:
          python-version: '3.11'
      - name: Validate Skills
        run: |
          for skill in $(git diff --name-only ${{ github.event.before }} | grep -E '^engineering/[^/]+/' | cut -d'/' -f1-2 | sort -u); do
            python engineering/skill-tester/scripts/skill_validator.py $skill --json
            python engineering/skill-tester/scripts/script_tester.py $skill
            python engineering/skill-tester/scripts/quality_scorer.py $skill --minimum-score 75
          done
```

### Pre-commit Hook
```bash
#!/bin/bash
# .git/hooks/pre-commit
python engineering/skill-tester/scripts/skill_validator.py engineering/my-skill --tier STANDARD
if [ $? -ne 0 ]; then
    echo "Skill validation failed. Commit blocked."
    exit 1
fi
```

## Quality Standards

### All Scripts
- **Zero External Dependencies** - Python standard library only
- **Comprehensive Error Handling** - Meaningful error messages and recovery
- **Dual Output Support** - Both JSON and human-readable formats
- **Proper Documentation** - Comprehensive docstrings and comments
- **CLI Best Practices** - Full argparse implementation with help text

### Validation Accuracy
- **Structure Checks** - 100% accurate directory and file validation
- **Content Analysis** - Deep parsing of SKILL.md and documentation
- **Code Analysis** - AST-based Python code validation
- **Compliance Scoring** - Objective, repeatable quality assessment

## Self-Testing

The skill-tester can validate itself:

```bash
# Validate the skill-tester structure
python scripts/skill_validator.py . --tier POWERFUL

# Test the skill-tester scripts
python scripts/script_tester.py .

# Score the skill-tester quality
python scripts/quality_scorer.py . --detailed
```

## Advanced Usage

### Batch Validation
```bash
# Validate all skills in repository
find engineering/ -maxdepth 1 -type d | while read skill; do
  echo "Validating $skill..."
  python engineering/skill-tester/scripts/skill_validator.py "$skill"
done
```

### Quality Monitoring
```bash
# Generate quality report for all skills
python engineering/skill-tester/scripts/quality_scorer.py engineering/ \
  --batch --json > quality_report.json
```

### Custom Scoring Thresholds
```bash
# Enforce minimum quality scores
python scripts/quality_scorer.py engineering/my-skill --minimum-score 80
# Exit code 0 = passed, 1 = failed, 2 = needs improvement
```

## Error Handling

All scripts provide comprehensive error handling:
- **File System Errors** - Missing files, permission issues, invalid paths
- **Content Errors** - Malformed YAML, invalid JSON, encoding issues  
- **Execution Errors** - Script timeouts, runtime failures, import errors
- **Validation Errors** - Standards violations, compliance failures

## Output Formats

### Human-Readable
```
=== SKILL VALIDATION REPORT ===
Skill: engineering/my-skill
Overall Score: 85.2/100 (B+)
Tier Recommendation: STANDARD

STRUCTURE VALIDATION:
  ✓ PASS: SKILL.md found
  ✓ PASS: README.md found
  ✓ PASS: scripts/ directory found

SUGGESTIONS:
  • Add references/ directory
  • Improve error handling in main.py
```

### JSON Format
```json
{
  "skill_path": "engineering/my-skill",
  "overall_score": 85.2,
  "letter_grade": "B+",
  "tier_recommendation": "STANDARD",
  "dimensions": {
    "Documentation": {"score": 88.5, "weight": 0.25},
    "Code Quality": {"score": 82.0, "weight": 0.25},
    "Completeness": {"score": 85.5, "weight": 0.25},
    "Usability": {"score": 84.8, "weight": 0.25}
  }
}
```

## Requirements

- **Python 3.7+** - No external dependencies required
- **File System Access** - Read access to skill directories  
- **Execution Permissions** - Ability to run Python scripts for testing

## Contributing

See [SKILL.md](SKILL.md) for comprehensive documentation and contribution guidelines.

The skill-tester itself serves as a reference implementation of POWERFUL-tier quality standards.