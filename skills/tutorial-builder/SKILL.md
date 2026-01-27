---
name: tutorial-builder
description: Create step-by-step tutorials, operating manuals, and procedural documentation. Use when users need to document processes, create how-to guides, write operating procedures, build training materials, or develop equipment/software manuals. Triggers on requests like "create a tutorial", "write operating procedures", "document this process", "make a how-to guide", "build a training manual", or "step-by-step instructions".
---

# Tutorial Builder

Create clear, actionable procedural documentation that guides users through tasks with precision and safety.

## Document Types

### Operating Manuals
Equipment/system operation with safety protocols, startup/shutdown sequences, and troubleshooting.

### Tutorials
Learning-focused guides that build understanding progressively.

### Standard Operating Procedures (SOPs)
Formal procedures with compliance requirements and sign-off checkpoints.

### Quick Reference Guides
Condensed procedures for experienced users.

## Creation Workflow

### 1. Scope Definition

Gather essential context:
- **Audience**: Skill level, prior knowledge, role
- **Objective**: What can they do after completing this?
- **Environment**: Tools, equipment, software versions
- **Constraints**: Safety requirements, compliance needs, time limits

### 2. Task Analysis

Break the procedure into components:

```
PROCEDURE: [Name]
├── Prerequisites (what must be true before starting)
├── Materials/Tools (what's needed)
├── Phase 1: [Name]
│   ├── Step 1.1
│   ├── Step 1.2 (decision point?)
│   └── Step 1.3
├── Phase 2: [Name]
│   └── ...
├── Verification (how to confirm success)
└── Troubleshooting (common issues)
```

### 3. Step Structure

Each step follows this pattern:

```markdown
## Step N: [Action Verb] [Object]

**Purpose**: Why this step matters

**Action**:
[Clear, imperative instruction]

**Expected Result**:
[What should happen when done correctly]

**Checkpoint**: [ ] [Verification the user can perform]

> **Warning**: [Safety/critical information if applicable]

> **Tip**: [Helpful but non-essential information]
```

### 4. Decision Points

When procedures branch, use decision trees:

```markdown
### Decision: [Question to answer]

**If [Condition A]**:
→ Proceed to Step N

**If [Condition B]**:
→ Proceed to Step M

**If unsure**:
→ See Troubleshooting section
```

## Writing Principles

### Imperative Voice
- Write: "Open the valve"
- Not: "The valve should be opened"

### One Action Per Step
- Write: "1. Turn off power. 2. Unplug device."
- Not: "1. Turn off power and unplug device."

### Specific Over Vague
- Write: "Wait 30 seconds"
- Not: "Wait a moment"

### Observable Verification
- Write: "Green LED illuminates"
- Not: "System is ready"

## Safety Integration

### Warning Hierarchy

```markdown
> **DANGER**: Immediate risk of death or serious injury
> [Specific hazard and required action]

> **WARNING**: Potential risk of injury or equipment damage
> [Specific hazard and required action]

> **CAUTION**: Risk of minor injury or operational issue
> [Specific hazard and recommended action]

> **NOTICE**: Important information, no safety risk
> [Relevant information]
```

Place warnings BEFORE the step they apply to, not after.

### Critical Checkpoints

For safety-critical procedures, add mandatory verification:

```markdown
## HOLD POINT: [Name]

Do not proceed until:
- [ ] [Verification 1]
- [ ] [Verification 2]
- [ ] Supervisor sign-off (if required)
```

## Output Formats

### Full Manual Structure

```markdown
# [Equipment/System] Operating Manual

## Overview
- Purpose and scope
- Safety summary
- Required qualifications

## Quick Reference
- Emergency procedures
- Key specifications

## Procedures
### Startup
### Normal Operation
### Shutdown
### Emergency Shutdown

## Maintenance
### Daily checks
### Periodic maintenance

## Troubleshooting
### Symptom → Cause → Solution tables

## Appendices
- Specifications
- Parts lists
- Revision history
```

### Tutorial Structure

```markdown
# [Title]: [Outcome]

## What You'll Learn
- Objective 1
- Objective 2

## Prerequisites
- Required knowledge
- Required tools/materials

## Steps
[Numbered procedures with checkpoints]

## Summary
- Key takeaways
- Next steps

## Practice Exercises
[Application tasks to reinforce learning]
```

## Quality Checklist

Before finalizing:
- [ ] Every step has a single, clear action
- [ ] All warnings appear before relevant steps
- [ ] Prerequisites are complete and specific
- [ ] Verification points exist for critical steps
- [ ] Technical terms are defined on first use
- [ ] Illustrations/diagrams referenced where helpful
- [ ] Troubleshooting covers common failure modes
- [ ] Document tested by someone unfamiliar with procedure
