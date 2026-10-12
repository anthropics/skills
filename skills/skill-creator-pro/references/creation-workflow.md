# Skill Creation Workflow

Detailed step-by-step process for creating production-grade skills.

---

## Overview

```
Metadata → Discovery → Requirements → Analyze → Embed → Structure → Implement → Validate
```

**Key Principle**: Users want domain expertise IN the skill. They may not BE domain experts.

---

## Step 1: Get Skill Metadata

Ask ONLY these two questions first:

| Question | Purpose |
|----------|---------|
| **Skill type?** | Route to appropriate patterns |
| **Domain/technology?** | Focus domain discovery |

**Do NOT ask**: Usage examples, tech stack, constraints (these come AFTER discovery)

**Exit criteria**: Clear skill type + domain identified

---

## Step 2: Domain Discovery (Automatic)

Research the domain BEFORE asking user anything else.

### What to Discover

| Knowledge Area | Search Strategy | Example: "Kafka" |
|----------------|-----------------|------------------|
| Core concepts | Official docs, Context7 | Topics, partitions, consumers, producers |
| Standards/compliance | "[domain] standards compliance" | Exactly-once semantics, ordering guarantees |
| Best practices | "[domain] best practices 2025" | Partition strategies, consumer groups |
| Anti-patterns | "[domain] common mistakes pitfalls" | Over-partitioning, no dead letter queue |
| Security | "[domain] security requirements" | SASL, SSL, ACLs, encryption at rest |
| Ecosystem | "[domain] ecosystem tools" | Schema Registry, Kafka Connect, ksqlDB |
| Official sources | "[domain] official documentation" | kafka.apache.org, Confluent docs |

### Source Priority

1. **Official documentation** - Always authoritative
2. **Library docs (Context7)** - Structured, current
3. **GitHub** - Real implementations, discussions
4. **Community** - Stack Overflow, forums (verify accuracy)
5. **WebSearch** - Last resort, cross-reference

### Knowledge Sufficiency Check

Before proceeding, verify internally:

```
- [ ] Core concepts: Can I explain the fundamentals?
- [ ] Best practices: Do I know the recommended approaches?
- [ ] Anti-patterns: Do I know what to avoid?
- [ ] Security: Do I know the security considerations?
- [ ] Ecosystem: Do I know the related tools/options?
- [ ] Official sources: Do I have authoritative references?

If ANY is incomplete → Research more
Only if CANNOT discover (proprietary/internal) → Ask user
```

**Exit criteria**: Sufficient domain knowledge to create expert-level skill

---

## Step 3: Get User Requirements

NOW ask about user's SPECIFIC context (not domain knowledge):

| Ask | Purpose | NOT This |
|-----|---------|----------|
| "What's YOUR use case?" | Understand their need | "What can [domain] do?" |
| "What's YOUR tech stack?" | Know their environment | "What options exist?" |
| "Existing resources?" | Include their scripts/templates | "What tools are available?" |
| "Specific constraints?" | Their limitations | "What are best practices?" |

### Good vs Bad Questions

```
✅ "What's your use case - event sourcing, messaging, or streaming?"
   (Informed by discovery, asking about THEIR need)

❌ "What is Kafka used for?"
   (Asking user for domain knowledge we should discover)

✅ "Are you using Java, Python, or another language?"
   (Asking about THEIR environment)

❌ "What languages does Kafka support?"
   (Asking user for domain knowledge we should discover)
```

**Exit criteria**: Clear user requirements + existing resources identified

---

## Step 4: Analyze Domain

Combine discovered knowledge + user requirements:

### Procedural Knowledge (HOW)
- Step-by-step workflows
- Decision trees and branching logic
- Error handling sequences
- Validation procedures

### Domain Expertise (WHAT)
- Core concepts and terminology
- Best practices and patterns
- Anti-patterns to avoid
- Standards and compliance requirements

### Variability Analysis
| What VARIES | What's CONSTANT |
|-------------|-----------------|
| (User-specific inputs) | (Domain patterns) |
| (Tool/library choices) | (Best practices) |
| (Configuration options) | (Error handling) |

See `reusability-patterns.md` for detailed guidance.

---

## Step 5: Embed Domain Knowledge

**Critical**: Take the knowledge gathered in Step 2 and EMBED it into the skill.

### What Goes in references/

| Gathered Knowledge | Purpose in Generated Skill |
|--------------------|---------------------------|
| Library/API documentation | Enable correct implementation |
| Best practices | Guide quality decisions |
| Code examples | Provide reference patterns |
| Anti-patterns | Prevent common mistakes |
| Domain-specific details | Support edge cases |

**Structure `references/` based on what the domain needs** - file organization depends on the gathered knowledge and skill's purpose.

### When to Generate scripts/

Generate scripts when the domain requires **deterministic, executable procedures**:

| Domain Need | Example Scripts |
|-------------|-----------------|
| Setup/installation | Install dependencies, initialize project |
| Processing | Transform data, process files |
| Validation | Check compliance, verify output |
| Deployment | Deploy services, configure infrastructure |
| Automation | Batch operations, scheduled tasks |

**Decision**: If a procedure is complex, error-prone, or needs to be exactly repeatable → create a script. Otherwise → document in SKILL.md or references/.

### When to Generate assets/

Generate assets when the domain requires **exact templates or boilerplate**:

| Domain Need | Example Assets |
|-------------|----------------|
| Starting templates | HTML boilerplate, component scaffolds |
| Configuration files | Config templates, schema definitions |
| Code boilerplate | Base classes, starter code |

### Why This Matters

Generated skills are **zero-shot domain experts**. The expertise gathered in Step 2 must be embedded so the skill can implement without runtime discovery.

---

## Step 6: Initialize Structure

```bash
scripts/init_skill.py <skill-name> --path <output-directory>
```

Or manually create:
```
skill-name/
├── SKILL.md
├── references/
├── scripts/
└── assets/
```

---

## Step 7: Implement by Type

### Builder Skills
1. Write Required Clarifications (critical questions before building)
2. Define output specification (what artifact looks like)
3. Add domain standards enforcement (Must Follow/Must Avoid)
4. Create templates in assets/
5. Add output checklist

**Key sections**:
- Required Clarifications
- Output Specification
- Domain Standards
- Output Checklist

### Guide Skills
1. Write step-by-step workflow
2. Add good/bad examples
3. Link to official documentation
4. Create decision trees for branching paths

**Key sections**:
- Workflow Steps
- Examples (Good/Bad)
- Official Documentation table
- When to Use / When NOT to Use

### Automation Skills
1. Create tested scripts in scripts/
2. Document dependencies
3. Add error handling guidance
4. Define input/output contracts

**Key sections**:
- Available Scripts table
- Dependencies
- Error Handling
- Input/Output Specification

### Analyzer Skills
1. Define analysis scope and criteria
2. Create extraction/review patterns
3. Add output format specification
4. Include validation rules

**Key sections**:
- Analysis Scope
- Evaluation Criteria
- Output Format
- Validation Rules

### Validator Skills
1. Define quality criteria
2. Create scoring/evaluation rubrics
3. Add pass/fail thresholds
4. Include remediation guidance

**Key sections**:
- Quality Criteria
- Scoring Rubric
- Thresholds
- Remediation Patterns

---

## Step 8: Write SKILL.md

Follow this structure (includes Before Implementation for zero-shot execution):

```markdown
---
name: skill-name
description: |
  [What] Capability statement.
  [When] Use when users ask to <triggers>.
allowed-tools: Tool1, Tool2    # if restricted
---

# Skill Name

Brief description.

## What This Skill Does
- Capability 1
- Capability 2

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

## [Type-specific sections]
(See Step 6 for sections by type)

## Reference Files
| File | When to Read |
|------|--------------|
| `references/file.md` | When X |

## Output Checklist
- [ ] Requirement 1
- [ ] Requirement 2
```

**CRITICAL**: Generated skills are zero-shot domain experts. The "Before Implementation" section ensures they gather runtime context (codebase, user requirements) and apply their embedded domain expertise (from `references/`) to implement successfully in a single interaction.

---

## Step 9: Validate

Run validation before delivery:

```bash
scripts/package_skill.py <path/to/skill-folder>
```

### Manual Validation Checklist

**Frontmatter**:
- [ ] name: lowercase, hyphens, ≤64 chars, matches directory
- [ ] description: [What]+[When], ≤1024 chars, clear triggers

**Structure**:
- [ ] SKILL.md <500 lines
- [ ] No README.md, CHANGELOG.md
- [ ] Progressive disclosure to references/

**Reusability**:
- [ ] Handles variations (not requirement-specific)
- [ ] Clarifications capture variable elements
- [ ] Encodes constant patterns

**Zero-Shot Implementation**:
- [ ] Includes "Before Implementation" section
- [ ] Gathers runtime context (codebase, conversation, user guidelines)
- [ ] Domain expertise embedded in `references/` (library docs, best practices, examples)
- [ ] Only asks user for THEIR requirements (not domain knowledge)

**Knowledge**:
- [ ] Procedural knowledge (HOW) documented
- [ ] Domain expertise (WHAT) captured
- [ ] Official sources referenced

---

## Step 10: Iterate

1. Use skill on real tasks
2. Notice gaps or issues
3. Update and revalidate
4. Repeat until production-ready
