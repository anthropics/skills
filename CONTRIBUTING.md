# Contributing to Claude Skills

Thank you for your interest in contributing to the Claude Skills repository! This guide will help you create, test, and submit high-quality skills.

## Table of Contents

- [Getting Started](#getting-started)
- [Contribution Types](#contribution-types)
- [Skill Development Process](#skill-development-process)
- [Submission Guidelines](#submission-guidelines)
- [Code Review Process](#code-review-process)
- [Best Practices](#best-practices)

## Getting Started

### Prerequisites

1. Familiarity with Claude and how skills work
2. Understanding of the [Agent Skills Specification](agent_skills_spec.md)
3. Claude Code or Claude API access for testing

### Repository Structure

```
skills/
├── README.md                    # Main documentation
├── agent_skills_spec.md         # Official specification
├── CONTRIBUTING.md              # This file
├── SKILL_DEVELOPMENT_GUIDE.md   # Detailed development guide
├── skill-creator/               # Meta-skill for creating skills
├── template-skill/              # Starting template
└── [skill-name]/                # Individual skills
    ├── SKILL.md                 # Required: Instructions
    ├── scripts/                 # Optional: Executable code
    ├── references/              # Optional: Documentation
    └── assets/                  # Optional: Output resources
```

## Contribution Types

### 1. New Skills

We welcome skills that:
- **Solve common problems** - Address frequently requested tasks
- **Demonstrate capabilities** - Show what's possible with skills
- **Fill gaps** - Cover domains not yet represented
- **Improve workflows** - Make complex tasks repeatable

**Not Accepted:**
- Skills that duplicate existing functionality
- Malicious or harmful content
- Skills requiring proprietary/paid services without clear documentation
- Overly narrow use cases (consider if it should be a slash command instead)

### 2. Skill Improvements

- Bug fixes in existing skills
- Performance optimizations
- Better documentation or examples
- Additional bundled resources

### 3. Documentation

- Corrections to existing docs
- New tutorials or guides
- Translation efforts
- FAQ additions

### 4. Tooling

- Validation scripts
- Testing utilities
- Development helpers
- CI/CD improvements

## Skill Development Process

### Step 1: Plan Your Skill

Before coding, answer these questions:

1. **What problem does it solve?** Be specific about the use case
2. **Who is the audience?** Developers, designers, analysts, etc.
3. **What makes it reusable?** How does it generalize beyond one task?
4. **What resources are needed?** Scripts, references, assets?

**Discussion First:** For significant new skills, open an issue first to discuss:
- Whether it fits the repository scope
- If similar functionality exists
- Design approach and structure

### Step 2: Initialize Your Skill

Use the skill-creator skill or manually create:

```bash
# Option 1: Use the initialization script
python scripts/init_skill.py your-skill-name

# Option 2: Copy the template
cp -r template-skill/ your-skill-name/
cd your-skill-name/
```

### Step 3: Develop Your Skill

See [SKILL_DEVELOPMENT_GUIDE.md](SKILL_DEVELOPMENT_GUIDE.md) for detailed guidance on:
- Writing effective SKILL.md instructions
- Organizing bundled resources
- Progressive disclosure patterns
- Testing and validation

**Key Requirements:**

1. **SKILL.md** must include:
   ```yaml
   ---
   name: your-skill-name
   description: Clear description of what this skill does and when to use it
   license: Apache-2.0  # or your chosen license
   ---
   ```

2. **Name conventions:**
   - Lowercase only
   - Hyphens for spaces (no underscores)
   - Descriptive but concise
   - Directory name must match `name` in frontmatter

3. **Description guidelines:**
   - Clearly state what the skill does
   - Explain when Claude should use it
   - Keep under 200 characters for marketplace display

### Step 4: Test Your Skill

**Manual Testing:**

1. Test in Claude Code:
   ```bash
   # Symlink your skill to local skills directory
   ln -s /path/to/your-skill ~/.claude/skills/your-skill-name

   # Test in Claude Code
   # Trigger the skill and verify behavior
   ```

2. Test with Claude API (if applicable)

3. Verify with different inputs and edge cases

**Validation:**

Run the validation script to check for common issues:
```bash
python scripts/validate_skill.py your-skill-name/
```

### Step 5: Document Your Skill

Ensure your SKILL.md includes:

- **Clear instructions** - What Claude should do
- **Examples** - Show expected inputs/outputs
- **Constraints** - Any limitations or requirements
- **Tool usage** - Which tools Claude should use
- **Error handling** - How to handle common failures

Optional but recommended:
- Add examples/ directory with sample inputs
- Include LICENSE.txt if different from repository
- Add README.md for skill-specific developer notes

### Step 6: Submit Your Contribution

1. **Fork the repository**
   ```bash
   gh repo fork anthropics/skills
   ```

2. **Create a feature branch**
   ```bash
   git checkout -b add-your-skill-name
   ```

3. **Make your changes**
   ```bash
   git add your-skill-name/
   git commit -m "Add your-skill-name skill for [brief description]"
   ```

4. **Push and create PR**
   ```bash
   git push origin add-your-skill-name
   gh pr create --title "Add your-skill-name skill" --body "Description of your skill and what it does"
   ```

## Submission Guidelines

### Pull Request Requirements

Your PR must include:

1. **Complete skill directory** with all necessary files
2. **Updated README.md** adding your skill to the list
3. **Clear PR description** explaining:
   - What the skill does
   - Why it's useful
   - Any testing you've performed
   - Dependencies or requirements

### Code Quality Standards

- **SKILL.md clarity** - Instructions must be clear and unambiguous
- **No hardcoded secrets** - Use environment variables or user inputs
- **Error handling** - Scripts should handle failures gracefully
- **Dependencies documented** - List all requirements clearly
- **License compliance** - All code must be properly licensed

### Documentation Standards

- Use GitHub-flavored Markdown
- Include code examples with syntax highlighting
- Provide concrete examples, not abstract descriptions
- Keep instructions concise but complete
- Use progressive disclosure (basic → advanced)

## Code Review Process

### What Reviewers Look For

1. **Functionality** - Does the skill work as described?
2. **Usefulness** - Will others benefit from this skill?
3. **Quality** - Is the code clean and well-documented?
4. **Specification compliance** - Follows agent_skills_spec.md?
5. **Security** - No vulnerabilities or malicious code?

### Review Timeline

- Initial review: Within 5 business days
- Follow-up reviews: Within 2 business days
- Merge: After approval from 2 maintainers

### Addressing Feedback

- Respond to all review comments
- Push changes to your PR branch
- Mark conversations as resolved when addressed
- Request re-review when ready

## Best Practices

### Skill Design

1. **Start simple** - Begin with core functionality, add features later
2. **Think reusable** - Generalize beyond your specific use case
3. **Progressive disclosure** - Keep SKILL.md lean, use references/ for details
4. **Minimize context** - Use scripts for deterministic operations
5. **Clear triggers** - Make the description specific about when to use

### Bundled Resources

**Scripts:**
- Make them executable and self-contained
- Include shebangs (#!/usr/bin/env python3)
- Document dependencies at the top
- Return clear error messages

**References:**
- Break long docs into focused files
- Use descriptive filenames
- Include grep patterns in SKILL.md for large files
- Keep technical depth appropriate for Claude

**Assets:**
- Use common formats (PNG, SVG, JSON)
- Include source files when possible
- Document any generation process
- Keep file sizes reasonable (<10MB per file)

### Testing

- Test with typical inputs
- Test with edge cases (empty, very large, malformed)
- Test error conditions
- Verify cross-platform compatibility (if applicable)
- Check performance with large inputs

### Documentation

- Write for clarity, not cleverness
- Include "why" not just "what"
- Provide runnable examples
- Update docs when changing functionality
- Link to external resources when helpful

## Getting Help

### Resources

- **Skill Creator Skill** - Use the skill-creator skill for guidance
- **Examples** - Study existing skills for patterns
- **Specification** - Refer to agent_skills_spec.md
- **Development Guide** - See SKILL_DEVELOPMENT_GUIDE.md

### Communication

- **Questions** - Open a GitHub issue with the `question` label
- **Bugs** - Report issues with the `bug` label
- **Feature Requests** - Use the `enhancement` label
- **Discussions** - Use GitHub Discussions for open-ended topics

### Community Guidelines

- Be respectful and constructive
- Assume good intent
- Help others learn and improve
- Give credit where due
- Focus on the contribution, not the contributor

## License

By contributing to this repository, you agree that your contributions will be licensed under the Apache License 2.0, unless otherwise specified in your skill's LICENSE.txt file.

---

**Thank you for contributing to Claude Skills!** Your work helps the entire community build better AI-powered workflows.
