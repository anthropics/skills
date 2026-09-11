# Skill Creator

A meta-skill for creating, testing, and optimizing Claude skills.

## Quick Start

**Use this skill when:**
- You want to create a brand new skill
- You're iterating on an existing skill to improve it
- You want to measure skill performance with evaluations
- You want to optimize a skill's description for better triggering

## The Workflow

The skill creation process follows these phases:

```
Capture Intent → Write Draft → Create Tests → Run Evals → Iterate → Expand → Optimize
```

**For a quick overview**, see `references/quick-reference.md`.

**For the full workflow**, read `SKILL.md`.

## Key Features

- **Intent Capture**: Clarify what the skill should do and when it should trigger
- **Draft Writing**: Create well-structured SKILL.md with metadata and instructions
- **Test Creation**: Write realistic test prompts and evaluation criteria
- **Evaluation**: Run quantitative and qualitative tests against the skill
- **Iteration**: Refine based on feedback and performance metrics
- **Trigger Optimization**: Improve skill descriptions for accurate triggering

## Common Tasks

### Creating a New Skill
1. Identify a workflow you repeat or want to automate
2. Clarify the intent (what, when, how)
3. Write a draft SKILL.md
4. Create 2-3 test prompts
5. Run evals and review results
6. Iterate based on feedback
7. Expand tests and optimize description

### Improving an Existing Skill
1. Identify what's not working (wrong triggers, poor outputs, missing cases)
2. Modify the SKILL.md to address the issue
3. Create test cases for the specific problem
4. Run evals to verify the fix
5. Expand tests to catch future regressions

### Testing Objectively vs. Subjectively
- **Objective outputs** (code, data transforms): Include expected results in tests
- **Subjective outputs** (writing, design): Use qualitative criteria (tone, completeness, clarity)
- **Hybrid**: Mix both—check for structural correctness + quality

## Skill Structure

A skill consists of:

```
skill-name/
├── SKILL.md                    # Core skill definition (frontmatter + instructions)
├── README.md                   # This file (overview and quick start)
├── LICENSE.txt                 # License declaration
├── references/                 # Optional: reference documentation
│   ├── quick-reference.md
│   └── advanced-patterns.md
├── scripts/                    # Optional: helper scripts for deterministic tasks
│   ├── transform.py
│   └── validate.js
└── assets/                     # Optional: templates, icons, sample files
    └── skill-template.md
```

### SKILL.md Frontmatter

Every skill needs metadata:

```yaml
---
name: skill-identifier           # Unique name (lowercase, hyphens for spaces)
description: |                   # What the skill does, when to use it
  Multi-line description that includes:
  - What the skill does
  - When to use it (specific contexts)
  - What kind of output it produces
license: Apache 2.0
---
```

## Quick Reference

| Task | Location |
|------|----------|
| Overview of workflow | SKILL.md |
| Quick reference guide | references/quick-reference.md |
| Skill template | template/SKILL.md |
| Test examples | TESTING_EXAMPLES.md (repository root) |
| Creating best practices | SKILL.md § Best Practices |

## For Skill Developers

### Before Publishing
- [ ] SKILL.md is under 500 lines (move large sections to references/)
- [ ] Description includes 2-3 specific trigger contexts
- [ ] Tests cover happy path, edge cases, and failure modes
- [ ] eval metrics show >80% pass rate
- [ ] README.md explains when to use the skill
- [ ] LICENSE.txt is present

### Test-Driven Skill Development
1. Write tests FIRST (what should this skill do?)
2. Write skill SECOND (make tests pass)
3. Evaluate THIRD (does it actually work?)
4. Iterate until satisfied

This prevents writing skills that sound good but don't work in practice.

### Making Skills Trigger Correctly

**Under-triggering** (doesn't activate when needed):
- Description too vague or generic
- Missing specific trigger phrases and contexts
- Doesn't explain when to use

Fix: Add 2-3 concrete examples and specific trigger phrases to the description

**Over-triggering** (activates when it shouldn't):
- Description too broad or overlapping with other skills
- Doesn't clarify what it's NOT used for

Fix: Narrow description; explicitly state when NOT to use

**Good triggering** (activates at right times):
- Clear, specific description (2-4 sentences)
- Includes examples of what to use for
- Explains when to use vs. alternatives
- Description appears in skill's own content

## Common Patterns

### Decision/Planning Skills
- Test with ambiguous inputs ("I'm not sure what I want")
- Include options and trade-offs
- Test that user can make a decision based on output

### Code Generation Skills
- Test syntax correctness (actually run the code)
- Test multiple languages/frameworks
- Include error cases and recovery

### Writing/Content Skills
- Define quality criteria upfront (tone, length, style)
- Test with diverse input quality levels
- Test different output formats/audiences

### Reference/Knowledge Skills
- Test accuracy and completeness
- Test with follow-up/clarification questions
- Verify information is current

## Troubleshooting

| Problem | Likely Cause | Solution |
|---------|---|---|
| Skill never triggers | Description too vague | Add specific contexts and examples |
| Skill triggers too often | Too broad scope | Clarify when NOT to use |
| Tests pass but users confused | Tests aren't realistic | Add user-based test cases |
| Can't measure quality | Subjective outputs | Define quality criteria first |
| Performance slow | Skill does too much | Consider splitting into smaller skills |

## Related Skills & Resources

- **doc-coauthoring**: Use for writing documentation about your skill
- **mcp-builder**: Use if your skill needs custom MCP servers
- **TESTING_EXAMPLES.md**: Repository file with detailed eval examples
- **CLAUDE.md**: Repository guide with skill structure overview

## For Repository Contributors

### Adding a New Skill
1. Create `skills/skill-name/` directory
2. Write `SKILL.md` with frontmatter and instructions
3. Create `README.md` (this file as template)
4. Add to `.claude-plugin/marketplace.json` in appropriate plugin collection
5. Create test cases if applicable
6. Commit with clear message referencing the skill

### Updating an Existing Skill
1. Edit `SKILL.md` for changes
2. Update reference files as needed
3. Update test cases if behavior changed
4. Commit with description of what changed

### Quality Standards
- Syntax: YAML frontmatter must be valid
- Coverage: Core functionality should be tested
- Documentation: README and references explain the skill
- Licensing: LICENSE.txt must match declared license
- Examples: Include realistic use cases

## Resources

- **Skill Specification**: https://agentskills.io/specification
- **CLAUDE.md**: Repository guide with full structure
- **Marketplace**: `.claude-plugin/marketplace.json` lists all skills
- **Template**: `template/SKILL.md` is a minimal skill example

---

**Last Updated**: August 2026
**License**: Apache 2.0
**Repository**: anthropics/skills
