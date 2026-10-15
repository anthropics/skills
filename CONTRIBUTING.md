# Contributing to Skills

Thanks for your interest in contributing to the Skills repository. This document covers how to contribute and what to expect.

## What This Repo Is

This repository contains Anthropic's official skills for Claude — both open-source examples (Apache 2.0) and source-available document skills. It is primarily maintained by Anthropic. Community contributions are welcome, particularly:

- **Bug fixes** to existing skills or scripts
- **Documentation improvements** (typos, clarifications, broken links)
- **Improvements to existing skills** (better instructions, edge case handling)
- **New skill submissions** (higher bar — see below)

## Before You Start

1. **Search existing skills and open PRs.** Check that your idea doesn't duplicate an existing skill or overlap with an open pull request.
2. **Open an issue first** for new skill submissions or significant changes. Describe what the skill does and why it belongs in this repo. Small fixes (typos, broken links) can go straight to a PR.
3. **Read the [skill-creator](./skills/skill-creator/SKILL.md)** for guidance on skill structure, writing patterns, and the progressive disclosure model.

## Skill Structure

Every skill follows this structure (from the [skill-creator](./skills/skill-creator/SKILL.md#anatomy-of-a-skill)):

```
skill-name/
├── SKILL.md (required)
│   ├── YAML frontmatter (name, description)
│   └── Markdown instructions
└── Bundled Resources (optional)
    ├── scripts/
    ├── references/
    └── assets/
```

The frontmatter requires two fields:

- `name` — lowercase, hyphens for spaces
- `description` — what the skill does and when Claude should use it

For more detail, see the [template](./template/SKILL.md) and the [Agent Skills specification](https://agentskills.io/specification).

## Recommended Practices

These patterns are drawn from the existing skills in this repo:

- **One skill per pull request.** Keep PRs focused on a single change.
- **Keep SKILL.md under 500 lines.** Use bundled reference files for additional content.
- **Self-contained.** Each skill lives in its own folder under `skills/`. No cross-skill dependencies.
- **No malware, exploit code, or misleading content.** A skill's contents should not surprise the user in their intent if described (see [Principle of Lack of Surprise](./skills/skill-creator/SKILL.md)).
- **Test your skill** before submitting. Run it against a few realistic prompts and verify it produces useful results.

## Submitting a Pull Request

1. Fork the repository and create a branch with a descriptive name.
2. Add your skill under `skills/your-skill-name/`.
3. Write a clear PR title and description explaining what the skill does and why.
4. Submit against `main`.

Review timelines vary based on maintainer availability. If your PR hasn't received feedback after a few weeks, a polite follow-up comment is welcome.

## Resources

- [What are skills?](https://support.claude.com/en/articles/12512176-what-are-skills)
- [Creating custom skills](https://support.claude.com/en/articles/12512198-creating-custom-skills)
- [Agent Skills specification](https://agentskills.io/specification)
- [Skill template](./template/SKILL.md)
- [Skill creator](./skills/skill-creator/SKILL.md)
