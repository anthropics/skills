# Skill Patterns

SKILL.md structure and examples for different skill types.

---

## Frontmatter Specification

### Complete Frontmatter Template

```yaml
---
name: skill-name                          # Required
description: |                            # Required
  [What] Brief statement of capability.
  [When] Use when users ask to <triggers>.
allowed-tools: Read, Grep, Glob           # Optional: restrict tool access
model: claude-sonnet-4-20250514           # Optional: model override
---
```

### Field Requirements

| Field | Required | Constraints | Purpose |
|-------|----------|-------------|---------|
| `name` | Yes | Lowercase, numbers, hyphens only; ≤64 chars; must match directory name | Skill identifier |
| `description` | Yes | ≤1024 characters; must include What + When | Claude Code uses this to decide when to trigger |
| `allowed-tools` | No | Comma-separated tool names | Restricts tool access during skill execution |
| `model` | No | Valid model ID | Override model for complex reasoning |

### Name Constraints

```
✅ Valid: pdf-processor, data-viz, api-v2
❌ Invalid: PDF_Processor, dataViz, my skill
```

- Lowercase letters, numbers, hyphens only
- Maximum 64 characters
- Must match the directory name exactly

### Description Format

**Structure**: `[What it does] + [When to use/triggers]`

**Limit**: ≤1024 characters (truncated if exceeded)

**Purpose**: Claude Code reads this to decide when to activate the skill. Include specific trigger phrases users would say.

```yaml
# Good: Clear what + when with triggers (third-person style)
description: |
  Create data visualizations with charts and graphs.
  This skill should be used when users ask to visualize data, create charts,
  build dashboards, or display metrics graphically.

# Bad: Vague, no triggers
description: Helps with charts
```

### allowed-tools Usage

Restrict tool access for security or scope:

```yaml
# Read-only skill (no file modifications)
allowed-tools: Read, Grep, Glob

# Analysis skill with web access
allowed-tools: Read, Grep, WebFetch, WebSearch

# Full access (default if omitted)
# allowed-tools: (omit field)
```

### model Override

Specify when skill needs different model capabilities:

```yaml
# For complex reasoning tasks
model: claude-sonnet-4-20250514

# For simple, fast operations
model: claude-haiku-3-20250514
```

---

## SKILL.md Structure

### Complete Template

```markdown
---
name: skill-name
description: |
  [What] Capability statement.
  [When] Use when users ask to <specific triggers>.
---

# Skill Name

Brief one-line description.

## What This Skill Does
- Capability 1
- Capability 2
- Capability 3

## What This Skill Does NOT Do
- Exclusion 1
- Exclusion 2

---

## Before Implementation

Gather context to ensure successful implementation:

| Source | Gather |
|--------|--------|
| **Codebase** | Existing structure, patterns, conventions to integrate with |
| **Conversation** | User's specific requirements, constraints, preferences |
| **Skill References** | Domain patterns from `references/` (library docs, best practices, examples) |
| **User Guidelines** | Project-specific conventions, team standards |

Ensure all required context is gathered before implementing.
Only ask user for THEIR specific requirements (domain expertise is in this skill).

---

## Required Clarifications

Ask about USER'S context (not domain knowledge):

1. **Use case**: "What's YOUR specific need?"
2. **Constraints**: "Any specific requirements?"

---

## Workflow

1. Step one
2. Step two
3. Step three

---

## [Domain-Specific Section]

Content specific to what the skill does.

---

## Output Checklist

Before delivering, verify:
- [ ] Requirement 1
- [ ] Requirement 2
- [ ] Requirement 3

---

## Reference Files

| File | When to Read |
|------|--------------|
| `references/file1.md` | When X |
| `references/file2.md` | When Y |
```

---

## Skill Types Taxonomy

### Overview

| Type | Purpose | Key Output |
|------|---------|------------|
| **Builder** | Creates new artifacts | Code, documents, widgets, configs |
| **Guide** | Provides instructions | Step-by-step workflows, tutorials |
| **Automation** | Executes workflows | Processed files, transformed data |
| **Analyzer** | Extracts insights | Reports, summaries, reviews |
| **Validator** | Enforces quality | Pass/fail assessments, scores |

### Type Selection Guide

```
What does the skill primarily do?

Creates NEW artifacts (code, docs, widgets)?
  → Builder

Teaches HOW to do something?
  → Guide

Executes multi-step PROCESSES automatically?
  → Automation

EXTRACTS information or provides ANALYSIS?
  → Analyzer

CHECKS quality or ENFORCES standards?
  → Validator
```

---

## Builder Skills (Create Artifacts)

**Purpose**: Generate new code, documents, widgets, configurations

**Key elements**:
- Required Clarifications (MUST ask before building)
- Output specification
- Domain standards enforcement
- Templates in assets/

**Example frontmatter**:
```yaml
---
name: widget-creator
description: |
  Create production widgets for ChatGPT Apps.
  Use when users ask to build UI components, visual interfaces,
  or interactive elements.
---
```

**Required sections**:
```markdown
## Before Implementation

Gather context to ensure successful implementation:

| Source | Gather |
|--------|--------|
| **Codebase** | Existing structure, patterns, conventions to integrate with |
| **Conversation** | User's specific requirements, constraints, preferences |
| **Skill References** | Domain patterns from `references/` |
| **User Guidelines** | Project-specific conventions, team standards |

## Required Clarifications
1. **Data shape**: "What structure will input have?"
2. **Output type**: "What artifact to create?"
3. **Constraints**: "Any specific requirements?"

## Output Specification
[Define what the artifact looks like]

## Domain Standards
### Must Follow
- [ ] Standard 1
### Must Avoid
- Anti-pattern 1

## Output Checklist
- [ ] Artifact meets requirements
```

---

## Guide Skills (Provide Instructions)

**Purpose**: Teach procedures, provide tutorials, explain how-to

**Key elements**:
- Step-by-step workflow
- Good/bad examples
- Official documentation links
- Decision trees for branching

**Example frontmatter**:
```yaml
---
name: api-integration-guide
description: |
  Guide for integrating external APIs.
  Use when users need to connect to third-party services,
  handle authentication, or manage API responses.
---
```

**Required sections**:
```markdown
## Before Implementation

Gather context to ensure successful implementation:

| Source | Gather |
|--------|--------|
| **Codebase** | Existing structure, patterns, conventions to integrate with |
| **Conversation** | User's specific requirements, constraints, preferences |
| **Skill References** | Domain patterns from `references/` |
| **User Guidelines** | Project-specific conventions, team standards |

## Workflow
1. **Step 1** - Action
2. **Step 2** - Action
3. **Step 3** - Action

## Examples
### Good Example
[Correct pattern with explanation]

### Bad Example (Avoid)
[Incorrect pattern with explanation]

## Official Documentation
| Resource | URL | Use For |
|----------|-----|---------|
| Docs | https://... | Reference |
```

---

## Automation Skills (Execute Workflows)

**Purpose**: Process files, deploy systems, execute multi-step operations

**Key elements**:
- Tested scripts in scripts/
- Error handling guidance
- Dependencies documented
- Input/output contracts

**Example frontmatter**:
```yaml
---
name: pdf-processor
description: |
  Process PDF files with extraction, rotation, and form filling.
  Use when users need to manipulate PDF documents programmatically.
---
```

**Required sections**:
```markdown
## Before Implementation

Gather context to ensure successful implementation:

| Source | Gather |
|--------|--------|
| **Codebase** | Existing structure, patterns, conventions to integrate with |
| **Conversation** | User's specific requirements, constraints, preferences |
| **Skill References** | Domain patterns from `references/` |
| **User Guidelines** | Project-specific conventions, team standards |

## Available Scripts
| Script | Purpose | Usage |
|--------|---------|-------|
| `scripts/process.py` | Main processing | `python process.py input output` |

## Dependencies
- Python 3.10+
- Required packages: [list]

## Error Handling
| Error | Recovery |
|-------|----------|
| Invalid input | [Action] |

## Input/Output
- **Input**: [Format, constraints]
- **Output**: [Format, location]
```

---

## Analyzer Skills (Extract Insights)

**Purpose**: Review documents, analyze data, extract information, summarize

**Key elements**:
- Analysis scope and criteria
- Extraction patterns
- Output format specification
- Synthesis guidance

**Example frontmatter**:
```yaml
---
name: code-analyzer
description: |
  Analyze codebases for patterns, issues, and improvements.
  Use when users ask to review code, find patterns,
  assess quality, or understand architecture.
---
```

**Required sections**:
```markdown
## Before Implementation

Gather context to ensure successful implementation:

| Source | Gather |
|--------|--------|
| **Codebase** | Existing structure, patterns, conventions to integrate with |
| **Conversation** | User's specific requirements, constraints, preferences |
| **Skill References** | Domain patterns from `references/` |
| **User Guidelines** | Project-specific conventions, team standards |

## Analysis Scope
- What to analyze
- What to ignore

## Evaluation Criteria
| Criterion | Weight | How to Assess |
|-----------|--------|---------------|
| Criterion 1 | X% | [Method] |

## Output Format
[Specify report structure]

## Synthesis
- Combine findings into actionable insights
- Prioritize by impact
```

---

## Validator Skills (Enforce Quality)

**Purpose**: Check compliance, score quality, enforce standards

**Key elements**:
- Quality criteria with scoring
- Pass/fail thresholds
- Remediation guidance
- Evidence collection

**Example frontmatter**:
```yaml
---
name: accessibility-validator
description: |
  Validate web content for WCAG accessibility compliance.
  Use when users ask to check accessibility, audit for
  compliance, or verify standards adherence.
---
```

**Required sections**:
```markdown
## Before Implementation

Gather context to ensure successful implementation:

| Source | Gather |
|--------|--------|
| **Codebase** | Existing structure, patterns, conventions to integrate with |
| **Conversation** | User's specific requirements, constraints, preferences |
| **Skill References** | Domain patterns from `references/` |
| **User Guidelines** | Project-specific conventions, team standards |

## Quality Criteria
| Criterion | Weight | Pass Threshold |
|-----------|--------|----------------|
| Criterion 1 | X% | [Threshold] |

## Scoring Rubric
- **3 (Excellent)**: [Definition]
- **2 (Good)**: [Definition]
- **1 (Needs Work)**: [Definition]
- **0 (Fail)**: [Definition]

## Thresholds
- **Pass**: Score ≥ X
- **Conditional**: Score X-Y
- **Fail**: Score < Y

## Remediation
| Issue | Fix |
|-------|-----|
| Issue 1 | [How to fix] |
```

---

## Assets Directory Patterns

### When to Use assets/

| Use Case | Example |
|----------|---------|
| Output templates | HTML boilerplate, component scaffolds |
| Exact boilerplate | Config files that must be precise |
| Visual assets | Images, icons, fonts |
| Data templates | JSON schemas, sample data |

### When NOT to Use assets/

| Avoid | Instead |
|-------|---------|
| Code that varies per use | Describe pattern in SKILL.md |
| Large files (>50KB) | Reference external URLs |
| Generated content | Create dynamically |

### Asset Types

```
assets/
├── templates/           # Output scaffolds
│   ├── component.tsx    # React component template
│   ├── page.html        # HTML page template
│   └── config.json      # Configuration template
├── schemas/             # Data structures
│   ├── input.schema.json
│   └── output.schema.json
└── examples/            # Reference implementations
    ├── simple.tsx
    └── advanced.tsx
```

### Referencing Assets in SKILL.md

**Template with placeholders**:
```markdown
Use `assets/templates/component.tsx` as base template.

Replace placeholders:
- `{{COMPONENT_NAME}}` → PascalCase component name
- `{{PROPS_INTERFACE}}` → TypeScript props interface
- `{{RENDER_CONTENT}}` → JSX content
```

**Exact copy**:
```markdown
Copy `assets/config.json` to project root.
Do not modify structure; only update values.
```

**Reference example**:
```markdown
Follow pattern in `assets/examples/simple.tsx` for basic usage.
For advanced features, see `assets/examples/advanced.tsx`.
```

### Template Design Principles

1. **Self-documenting placeholders**: `{{DESCRIPTIVE_NAME}}`
2. **Minimal structure**: Only essential boilerplate
3. **Clear boundaries**: Mark customizable sections
4. **Valid syntax**: Template should be syntactically valid

**Good template**:
```typescript
// assets/templates/component.tsx
import React from 'react';

interface {{COMPONENT_NAME}}Props {
  {{PROPS}}
}

export function {{COMPONENT_NAME}}({ {{DESTRUCTURED_PROPS}} }: {{COMPONENT_NAME}}Props) {
  {{HOOKS}}

  return (
    {{JSX_CONTENT}}
  );
}
```

---

## Frontmatter Best Practices

### Good Description (triggers reliably)

```yaml
description: |
  Create production widgets for ChatGPT Apps using OpenAI Apps SDK.
  Use when users ask to build UI components, visual interfaces,
  progress trackers, quiz interfaces, or interactive elements.
```

**Why it works**:
- [What] Clear capability statement first
- [When] Specific trigger phrases users would say
- ≤1024 characters
- Claude Code can match user intent

### Bad Description (won't trigger)

```yaml
description: Widget stuff
```

**Why it fails**:
- No [What] capability statement
- No [When] trigger phrases
- Too vague for Claude Code to match

---

## Scope Clarity Examples

### Good Scope

```markdown
## What This Skill Does
- Creates ChatGPT widgets with window.openai integration
- Supports all display modes (inline, fullscreen, pip)
- Implements theme support (light/dark)
- Follows OpenAI UX/UI guidelines

## What This Skill Does NOT Do
- Create native mobile apps
- Handle backend server logic
- Manage user authentication
- Deploy widgets to production
```

### Bad Scope (missing exclusions)

```markdown
## What This Skill Does
- Creates widgets
```

---

## Reference Organization

### By Domain (for multi-domain skills)

```
references/
├── aws.md        # AWS-specific patterns
├── gcp.md        # GCP-specific patterns
└── azure.md      # Azure-specific patterns
```

### By Complexity (for single-domain skills)

```
references/
├── quick-start.md     # Basic usage
├── advanced.md        # Complex scenarios
└── troubleshooting.md # Common issues
```

### By Feature (for feature-rich skills)

```
references/
├── authentication.md  # Auth patterns
├── state-management.md # State handling
└── error-handling.md   # Error patterns
```
