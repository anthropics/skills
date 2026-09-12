# Best Practices & Patterns for Claude Skills

This reference documents proven patterns from high-quality Claude Skills analyzed during quality assessment.

## Exemplary Skill Patterns

### Pattern 1: Security Analyzer Skill

**What makes it excellent:**

1. **Crystal Clear Purpose**
   - Name: `skill-security-analyzer`
   - Description: "Security analysis tool for Claude Code skills and plugins..."
   - Immediately obvious what it does

2. **Comprehensive Workflow**
   - Step 1: Locate and Identify
   - Step 2: Run Automated Scan
   - Step 3: Manual Code Review
   - Step 4: Network and File System Analysis
   - Step 5: Generate Security Report

3. **Detailed Guidance**
   - Specific bash commands to run
   - Example patterns to detect
   - Clear output format specifications

4. **Rich Resources**
   - `scripts/security_scanner.py` - Automated tooling
   - `references/vulnerability_patterns.md` - Pattern database
   - `references/safe_coding_practices.md` - Best practices guide

**Key Takeaway:** Provide both automated tooling AND detailed manual guidance.

### Pattern 2: Frontend Reviewer Skill

**What makes it excellent:**

1. **Organized by Categories**
   - Component Architecture
   - HTML/CSS Structure
   - Accessibility
   - Performance
   - Security

2. **Dual-Level Documentation**
   - High-level checklist in SKILL.md
   - Deep references for detailed guidelines
   - Efficient context usage

3. **Practical Checklists**
   - React Component Review Checklist
   - Accessibility Review Checklist
   - Performance Review Checklist

4. **Actionable Output Format**
   - Clear symbols (✅ ⚠️ ❌)
   - Location references (file.tsx:42)
   - Specific fixes provided

**Key Takeaway:** Use checklists and categorization for systematic reviews.

### Pattern 3: TDD UI Expert Skill

**What makes it excellent:**

1. **Philosophy First**
   - Explains "why" before "how"
   - Clear about when to use vs. skip
   - Pragmatic, not dogmatic

2. **Quick Start Section**
   - Scripts for setup
   - Templates for common cases
   - Step-by-step getting started

3. **Use Case Driven**
   - Component Testing
   - Form Testing
   - API Integration
   - Custom Hooks
   - Authentication Flows

4. **Rich Templates**
   - `assets/templates/component.test.js`
   - `assets/templates/form.test.js`
   - `assets/templates/api-integration.test.js`
   - Copy-paste ready code

**Key Takeaway:** Provide templates and scripts for common workflows.

## SKILL.md Best Practices

### Excellent Frontmatter

```yaml
---
name: skill-name
description: [Action] for [context]. Use when [trigger scenario]. Trigger phrases: "phrase 1", "phrase 2", "phrase 3".
---
```

**Good Examples:**

```yaml
---
name: skill-security-analyzer
description: Security analysis tool for Claude Code skills and plugins. Use when analyzing skills from marketplaces, zip files, or local directories for security vulnerabilities, malicious code patterns, supply chain risks, and best practice violations. Triggers on requests like "analyze this skill for security issues", "check if this plugin is safe", "audit skill security", or "review skill for malware".
---
```

```yaml
---
name: frontend-reviewer-skill
description: Comprehensive frontend code review skill for React/Vue/Angular applications, focusing on component architecture, HTML/CSS structure, accessibility compliance, and performance optimization. Use this skill when reviewing pull requests, commits, or codebases for frontend best practices. Trigger phrases include "review this frontend PR", "run frontend code review", "check frontend best practices", or similar requests for frontend code quality assessment.
---
```

**Why These Work:**
- Clear action (security analysis, frontend code review)
- Specific context (skills/plugins, React/Vue/Angular apps)
- Trigger scenarios stated
- Natural language trigger phrases

### Excellent Overview Section

```markdown
## Overview

[2-3 sentences that answer:]
- What does this skill do?
- Why does it exist?
- Who is it for?
```

**Example:**

```markdown
## Overview

This skill provides comprehensive security analysis for Claude Code skills and plugins installed from marketplaces, zip files, or local directories. It identifies security vulnerabilities, malicious code patterns, supply chain risks, YAML injection vulnerabilities, and best practice violations to ensure skills are safe to use.
```

**Why This Works:**
- Concrete capabilities listed
- Source types enumerated
- Value proposition clear

### Excellent "When to Use" Section

```markdown
## When to Use This Skill

Use this skill when:
- [Specific scenario 1]
- [Specific scenario 2]
- [Specific scenario 3]

**Trigger phrases:**
- "phrase 1"
- "phrase 2"
- "phrase 3"
```

**Example:**

```markdown
## When to Use This Skill

Use this skill when:
- Analyzing a newly installed skill from any source (marketplace, zip, local)
- Auditing existing skills for security issues
- Reviewing skills before installation
- Investigating suspicious behavior in a skill
- Performing periodic security reviews of installed skills
- Validating skills before sharing or publishing

**Trigger phrases:**
- "Analyze this skill for security issues"
- "Check if this plugin is safe"
- "Audit [skill-name] security"
- "Review this skill for malware"
- "Is this skill safe to install?"
- "Scan skills for vulnerabilities"
```

**Why This Works:**
- Specific, actionable scenarios
- Natural language triggers
- Variety of phrasings
- Covers common use cases

### Excellent Workflow Section

**Pattern: Numbered Steps with Details**

```markdown
## [Main Process Name]

### Step 1: [Action]

[Brief description of what happens in this step]

**How to do it:**
```bash
# Specific commands
command --flag value
```

**What to look for:**
- [Criterion 1]
- [Criterion 2]

### Step 2: [Next Action]

[Same structure...]
```

**Example:**

```markdown
## Security Analysis Workflow

### Step 1: Locate and Identify the Skill

First, determine the skill location based on user input:

**For marketplace skills:**
```bash
# User skills (project-specific)
ls -la .claude-project/skills/

# Global user skills
ls -la ~/.claude/skills/
```

**Skill structure to identify:**
```
skill-name/
├── SKILL.md (required)
├── scripts/ (optional)
├── references/ (optional)
└── assets/ (optional)
```
```

**Why This Works:**
- Clear step progression
- Specific commands provided
- Multiple scenarios covered
- Visual structure examples

### Excellent Resources Section

```markdown
## Resources

### [Resource Name]
[What it contains and when to load it]

### [Resource Name]
[What it contains and when to load it]
```

**Example:**

```markdown
## Resources

### scripts/security_scanner.py
Automated security scanner that detects common vulnerability patterns, malicious code, YAML injection, supply chain risks, and best practice violations. Outputs JSON report with findings.

### references/vulnerability_patterns.md
Comprehensive database of malicious code patterns, attack vectors, and exploitation techniques specific to Claude Code skills. Load when deeper analysis is needed.

### references/safe_coding_practices.md
Best practices guide for secure skill development. Reference when providing remediation recommendations or reviewing code quality.
```

**Why This Works:**
- Clear purpose for each resource
- Indicates when to use it
- Efficient context loading

## Trigger Phrase Patterns

### Natural Language Triggers

**Good Patterns:**
- "analyze [thing] for [issue]" → "analyze this skill for security issues"
- "check if [thing] is [quality]" → "check if this plugin is safe"
- "review [thing]" → "review this frontend PR"
- "run [process]" → "run frontend code review"

**Bad Patterns:**
- Too generic: "skill", "review", "check"
- Too specific: "execute security analysis protocol 7.3.2"
- Implementation details: "invoke security analyzer function"

### Variety Matters

Always provide 3-5 variations:

```markdown
**Trigger phrases:**
- "analyze this skill for security issues" (formal)
- "check if this plugin is safe" (casual question)
- "audit [skill-name] security" (specific)
- "review this skill for malware" (threat-focused)
- "is this skill safe to install?" (conversational)
```

## Directory Structure Patterns

### Minimal Skill (Documentation Only)

```
skill-name/
└── SKILL.md
```

Use when: Skill is pure guidance, no automation needed.

### Standard Skill (Guidance + References)

```
skill-name/
├── SKILL.md
└── references/
    ├── detailed-guide.md
    ├── patterns.md
    └── examples.md
```

Use when: Need deep documentation loaded conditionally.

### Advanced Skill (Automation + Guidance)

```
skill-name/
├── SKILL.md
├── README.md (for GitHub/marketplace)
├── scripts/
│   ├── setup.sh
│   └── analyzer.py
├── references/
│   ├── patterns.md
│   └── best-practices.md
└── assets/
    └── templates/
        ├── template1.js
        └── template2.js
```

Use when: Providing both automated tools and guidance.

## Script Patterns

### Setup Script Pattern

**Purpose:** Automate environment setup

```bash
#!/bin/bash
# Setup script for [skill-name]

set -e  # Exit on error

echo "Setting up [skill-name]..."

# Check prerequisites
command -v npm >/dev/null 2>&1 || { echo "npm required but not installed"; exit 1; }

# Install dependencies
npm install --save-dev \
  package1 \
  package2 \
  package3

# Copy configuration
cp assets/templates/config.js ./config.js

echo "Setup complete!"
```

**Why This Works:**
- Error handling (set -e)
- Prerequisite checks
- Clear feedback
- Idempotent if possible

### Analysis Script Pattern

**Purpose:** Automated analysis/scanning

```python
#!/usr/bin/env python3
"""
Security scanner for Claude Code skills.

Usage:
    python security_scanner.py <path-to-skill> [--verbose] [--output report.json]
"""

import argparse
import json
import sys
from pathlib import Path

def main():
    parser = argparse.ArgumentParser(description="Scan skill for security issues")
    parser.add_argument("skill_path", type=Path, help="Path to skill directory")
    parser.add_argument("--verbose", action="store_true", help="Detailed output")
    parser.add_argument("--output", type=Path, help="Output JSON file")

    args = parser.parse_args()

    # Validate input
    if not args.skill_path.exists():
        print(f"Error: {args.skill_path} does not exist", file=sys.stderr)
        sys.exit(1)

    # Run analysis
    findings = scan_skill(args.skill_path)

    # Output results
    if args.output:
        with open(args.output, 'w') as f:
            json.dump(findings, f, indent=2)
    else:
        print_findings(findings, args.verbose)

if __name__ == "__main__":
    main()
```

**Why This Works:**
- Docstring with usage
- Argparse for CLI
- Input validation
- Multiple output formats
- Proper error handling

## Template Patterns

### Code Template Pattern

**Purpose:** Provide copy-paste starter code

```javascript
// [template-name].test.js
// Template for testing [use case]

import { render, screen } from './test-utils'
import userEvent from '@testing-library/user-event'

test('[what this tests]', async () => {
  const user = userEvent.setup()

  // Arrange
  render(<YourComponent />)

  // Act
  await user.click(screen.getByRole('button', { name: /click me/i }))

  // Assert
  expect(screen.getByText(/result/i)).toBeInTheDocument()
})
```

**Why This Works:**
- Complete, runnable example
- Clear structure (Arrange-Act-Assert)
- Comments guide customization
- Follows best practices

## Reference Document Patterns

### Pattern Database

**Purpose:** Catalog of patterns to detect

```markdown
# [Pattern Type] Patterns

## Pattern 1: [Name]

**Description:** [What this pattern is]

**Why It's [Good/Bad]:** [Explanation]

**Example:**
```[language]
[Code example]
```

**Detection:**
- [How to identify it]
- [What to look for]

**Remediation:** (if anti-pattern)
```[language]
[Fixed code]
```

---

## Pattern 2: [Name]

[Same structure...]
```

### Best Practices Guide

**Purpose:** Comprehensive guidelines

```markdown
# [Topic] Best Practices

## Overview
[Brief intro to why these practices matter]

## Core Principles

### Principle 1: [Name]
[Explanation]

**Good Example:**
```[language]
[Code showing principle]
```

**Bad Example:**
```[language]
[Code violating principle]
```

## Guidelines

### [Category 1]
- ✅ **DO:** [Guideline]
- ❌ **DON'T:** [Anti-pattern]

### [Category 2]
[Same structure...]
```

## Output Format Patterns

### Report Format

```markdown
# [Report Title]

**[Metadata]:** [Values]

## Executive Summary
[High-level overview]

## [Section 1]
[Detailed findings]

### Finding 1: [Title]
**Severity:** [CRITICAL/HIGH/MEDIUM/LOW]
**Location:** `file.ext:line`

**Evidence:**
```[language]
[Code snippet]
```

**Impact:** [Why this matters]

**Remediation:**
```[language]
[How to fix]
```

---

## [Section 2]
[More findings...]

## Summary
[Wrap-up and recommendations]
```

### Checklist Format

```markdown
## [Checklist Category]

- [ ] **[Item 1]** - [Explanation]
- [ ] **[Item 2]** - [Explanation]
- [ ] **[Item 3]** - [Explanation]

**Result:** [X/Y passed]
```

### Interactive Review Format

```markdown
## [Review Section]

### What's Working Well ✅
- [Positive aspect 1]
- [Positive aspect 2]

### Quick Wins 💡
**1. [Improvement]**
   - **Why:** [Benefit]
   - **How:** [Specific action]
   - **Example:**
   ```[language]
   [Code example]
   ```

### Issues to Fix ❌
**1. [Problem]**
   - **Current:** [What exists]
   - **Problem:** [Why it's an issue]
   - **Fix:** [How to resolve]
```

## Common Patterns Checklist

When creating a skill, ensure you follow these patterns:

### Documentation Patterns
- [ ] Frontmatter with name and comprehensive description
- [ ] Overview section (2-3 sentences)
- [ ] "When to Use" section with specific scenarios
- [ ] Trigger phrases documented (3-5 variations)
- [ ] Main workflow/content section
- [ ] Resources section explaining references/scripts/assets
- [ ] Examples throughout

### Structure Patterns
- [ ] SKILL.md as primary documentation
- [ ] references/ for detailed docs (loaded conditionally)
- [ ] scripts/ for automation (documented in Resources)
- [ ] assets/ for templates (copy-paste ready)
- [ ] README.md if published to GitHub/marketplace

### Code Patterns
- [ ] Scripts have error handling
- [ ] Scripts have usage documentation
- [ ] Templates are complete and runnable
- [ ] References are well-organized
- [ ] No unnecessary files

### UX Patterns
- [ ] Immediately clear purpose
- [ ] Natural language triggers
- [ ] Step-by-step workflows
- [ ] Practical examples
- [ ] Logical organization

### Security Patterns
- [ ] Input validation
- [ ] Scoped file operations
- [ ] Documented network calls
- [ ] No hardcoded secrets
- [ ] Safe command execution

These patterns are extracted from analyzing high-quality skills and represent best practices in skill development.
