# Claude Skill Quality Analyzer

Comprehensive quality analysis tool for Claude Skills, evaluating skills from any source across five critical dimensions using a balanced scoring approach.

## Overview

The Skill Quality Analyzer provides systematic evaluation of Claude Skills to ensure they meet best practices for structure, security, user experience, code quality, and integration. It supports three analysis modes and multiple skill sources.

## Features

- **Multi-Source Support**: Analyze skills from GitHub URLs, marketplace links, ZIP files, or local directories
- **Five-Dimensional Evaluation**: Balanced assessment across structure, security, UX, code quality, and integration
- **Three Output Modes**:
  - **Comprehensive Report**: Detailed scores and grades across all dimensions
  - **Interactive Review**: Step-by-step recommendations for improvement
  - **Pass/Fail Certification**: Binary quality assessment with blocking issues
- **Security Integration**: Leverages skill-security-analyzer for vulnerability detection
- **Best Practices Database**: References proven patterns from high-quality skills

## Quick Start

### Analyze a GitHub Skill

```
User: Analyze skill quality for https://github.com/user/my-skill
```

### Analyze a Local Skill

```
User: Review this skill: ~/.claude/skills/my-skill
```

### Certify Skill Quality

```
User: Run quality certification on my-skill
```

## Evaluation Dimensions

### 1. Structure & Documentation (20%)
- SKILL.md format and completeness
- YAML frontmatter validity
- Description quality with trigger phrases
- Section organization (Overview, When to Use, Workflow, Resources)
- Examples and templates

### 2. Security (30%)
- Automated vulnerability scanning via skill-security-analyzer
- Malicious code pattern detection
- YAML injection checks
- File operation safety
- Network call documentation
- Input validation

### 3. User Experience (20%)
- Clarity of purpose
- Trigger phrase quality
- Workflow documentation
- Practical examples
- Logical organization

### 4. Code Quality (15%)
- Directory structure
- Script documentation
- Maintainability
- Consistent formatting
- Efficiency

### 5. Integration & Tools (15%)
- Appropriate tool usage
- MCP integration (if applicable)
- Resource efficiency
- Script integration

## Grading Scale

- **90-100 (A+/A)**: Excellent - Exemplary skill
- **80-89 (B+/B)**: Good - High quality
- **70-79 (C+/C)**: Acceptable - Functional
- **60-69 (D)**: Needs Improvement
- **0-59 (F)**: Poor - Not recommended

## Certification Requirements

To pass certification:
- Overall score ≥ 70/100
- Security score ≥ 80/100
- Structure score ≥ 70/100
- UX score ≥ 70/100
- Code Quality score ≥ 60/100
- Integration score ≥ 60/100
- No CRITICAL security findings

## Output Modes

### Mode 1: Comprehensive Report

Detailed markdown report with:
- Overall quality score (0-100)
- Grade (A+ to F)
- Dimension-by-dimension breakdown
- Specific findings with evidence
- Top strengths and improvement priorities
- Actionable recommendations

### Mode 2: Interactive Review

Step-by-step analysis with:
- Current state assessment
- What's working well
- Specific, actionable recommendations
- Code examples for fixes
- Prioritized action plan with impact/effort ratings

### Mode 3: Pass/Fail Certification

Binary assessment with:
- Certification status (PASS/FAIL)
- Criteria checklist
- Blocking issues (must fix to pass)
- Non-blocking recommendations
- Re-certification guidance

## Resources

### SKILL.md
Main skill documentation with complete workflow and evaluation criteria.

### references/quality-checklist.md
Comprehensive checklist for evaluating skills across all dimensions. Detailed scoring criteria and thresholds.

### references/best-practices-patterns.md
Database of proven patterns from high-quality skills. Examples of excellent SKILL.md structure, trigger phrases, workflows, and code organization.

### references/anti-patterns.md
Common mistakes and issues to flag. Red flags checklist for quick pattern matching during analysis.

## Example Usage

### Comprehensive Report Mode

```
User: Analyze skill quality for my-custom-skill with comprehensive report

Analyzer:
1. Fetches skill from specified source
2. Runs security analysis via skill-security-analyzer
3. Evaluates all five dimensions
4. Generates detailed report with scores, grades, and recommendations
```

### Interactive Review Mode

```
User: Review this skill interactively: https://github.com/user/skill

Analyzer:
1. Clones repository
2. Walks through each dimension step-by-step
3. Provides specific, actionable recommendations
4. Shows code examples for improvements
5. Creates prioritized action plan
```

### Certification Mode

```
User: Certify skill quality for ~/.claude/skills/production-skill

Analyzer:
1. Evaluates against certification criteria
2. Identifies blocking vs. non-blocking issues
3. Provides PASS/FAIL verdict
4. Lists required fixes for certification
```

## Best Practices Highlights

### Excellent SKILL.md Structure

```markdown
---
name: skill-name
description: [Action] for [context]. Use when [scenario]. Triggers: "phrase 1", "phrase 2".
---

# Skill Name

## Overview
[2-3 sentences explaining purpose]

## When to Use This Skill
- [Specific scenario 1]
- [Specific scenario 2]

**Trigger phrases:**
- "natural phrase 1"
- "natural phrase 2"

## [Main Workflow/Content]
[Detailed guidance]

## Resources
[Document references/, scripts/, assets/]
```

### Trigger Phrase Patterns

- Natural language users would say
- 3-5 variations (formal + casual)
- Specific enough to avoid false triggers
- Include action + context

Good examples:
- "analyze this skill for security issues"
- "review frontend code for accessibility"
- "run TDD tests on component"

### Directory Structure

```
skill-name/
├── SKILL.md (required)
├── README.md (for GitHub/marketplace)
├── scripts/ (optional - automation)
├── references/ (optional - detailed docs)
└── assets/ (optional - templates)
```

## Common Anti-Patterns

- Missing or invalid frontmatter
- Vague description without triggers
- No examples or workflow
- Undocumented network calls
- Command injection vulnerabilities
- Hardcoded secrets
- Poor directory organization
- Generic trigger phrases

## Contributing

When creating skills, follow the patterns documented in `references/best-practices-patterns.md` and avoid anti-patterns in `references/anti-patterns.md`.

## License

This skill is designed to improve the quality and security of Claude Skills ecosystem.

## Support

For issues or questions about skill quality analysis, refer to:
- `references/quality-checklist.md` for evaluation criteria
- `references/best-practices-patterns.md` for examples
- `references/anti-patterns.md` for common mistakes
