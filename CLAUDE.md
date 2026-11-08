# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Repository Overview

This is Anthropic's **Skills Repository** (`anthropics/skills`) — a collection of modular, self-contained skill packages that extend Claude's capabilities for specialized tasks. Skills are folders containing instructions, scripts, and resources that Claude loads dynamically.

The repository is **not** a traditional software project — there is no global build system, test suite, or CI/CD pipeline. Each skill is independent.

## Repository Structure

```
skills/           # All skill packages (each is self-contained)
spec/             # Agent Skills specification (points to agentskills.io/specification)
template/         # Minimal SKILL.md template for new skills
```

### Skill Categories

- **Document skills** (`docx/`, `pdf/`, `pptx/`, `xlsx/`) — Production skills powering Claude's document capabilities. Source-available (not open source). Use Python (python-docx, openpyxl, PyPDF, python-pptx) with LibreOffice integration.
- **Creative/Design** (`algorithmic-art/`, `canvas-design/`, `brand-guidelines/`, `theme-factory/`, `slack-gif-creator/`)
- **Technical/Dev** (`web-artifacts-builder/`, `webapp-testing/`, `mcp-builder/`, `skill-creator/`)
- **Enterprise** (`internal-comms/`, `doc-coauthoring/`, `frontend-design/`)
- **Knowledge** (`ai-infra/`, `economic-cycles/`)

## Skill Anatomy

Every skill requires this structure:
```
skill-name/
├── SKILL.md              # Required: YAML frontmatter (name, description) + markdown instructions
├── scripts/              # Optional: executable Python/Bash for deterministic tasks
├── references/           # Optional: documentation loaded into context as needed
└── assets/               # Optional: templates, images, fonts used in output
```

Key constraints:
- SKILL.md frontmatter requires only `name` and `description` fields
- `description` is the primary trigger mechanism — include both what the skill does AND when to use it
- SKILL.md body should stay under 500 lines; split into reference files when approaching this limit
- Do NOT add README.md, CHANGELOG.md, or other auxiliary docs inside skills

## Skill Creation Commands

Initialize a new skill:
```bash
skills/skill-creator/scripts/init_skill.py <skill-name> --path <output-directory>
```

Validate and package a skill into a distributable `.skill` file:
```bash
skills/skill-creator/scripts/package_skill.py <path/to/skill-folder> [output-directory]
```

Quick validation only:
```bash
skills/skill-creator/scripts/quick_validate.py <path/to/skill-folder>
```

## Key Design Principles

- **Context window is a public good** — skills share context with everything else. Be concise; only include what Claude doesn't already know.
- **Progressive disclosure** — Three loading levels: metadata (~100 words, always loaded) → SKILL.md body (on trigger) → bundled resources (on demand).
- **Degrees of freedom** — Match specificity to task fragility: low freedom (exact scripts) for fragile operations, high freedom (text guidance) for flexible tasks.
- **Use imperative/infinitive form** in SKILL.md instructions.

## Plugin Installation (for testing)

Register as Claude Code plugin marketplace:
```
/plugin marketplace add anthropics/skills
```

Install skill sets:
```
/plugin install document-skills@anthropic-agent-skills
/plugin install example-skills@anthropic-agent-skills
```
