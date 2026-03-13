# 🏗️ Architecture

This page describes how the repository is structured, how Claude loads skills, and the conventions that every skill follows.

---

## Repository Layout

```
upstream_skills/
├── .claude-plugin/
│   └── marketplace.json       # Plugin group registry for Claude Code
├── .github/
│   └── workflows/
│       └── update-wiki.yml    # Auto-generates and publishes this wiki
├── scripts/
│   └── generate_wiki.py       # Wiki generator (scans skills/, outputs wiki_output/)
├── skills/                    # One subfolder per skill
│   ├── algorithmic-art/
│   ├── brand-guidelines/
│   ├── canvas-design/
│   ├── claude-api/
│   ├── doc-coauthoring/
│   ├── docx/
│   ├── frontend-design/
│   ├── internal-comms/
│   ├── mcp-builder/
│   ├── pdf/
│   ├── pptx/
│   ├── skill-creator/
│   ├── slack-gif-creator/
│   ├── theme-factory/
│   ├── web-artifacts-builder/
│   ├── webapp-testing/
│   └── xlsx/
├── spec/
│   └── agent-skills-spec.md   # Link to the Agent Skills specification
├── template/
│   └── SKILL.md               # Minimal skill template
├── wiki/                      # Static wiki source pages (copied into output)
│   ├── Architecture.md        # ← this page
│   ├── Contributing.md
│   └── Getting-Started.md
├── README.md
└── THIRD_PARTY_NOTICES.md
```

---

## What Is a Skill?

A **skill** is a folder that Claude reads before responding to a task. It contains:

1. A **`SKILL.md`** file — the required entry point with YAML frontmatter and instructions.
2. Optional **supporting files** — scripts, templates, fonts, reference docs, examples.

Claude matches a skill to a user request based on the `description` field in the frontmatter, then follows the instructions in `SKILL.md` for that request.

### How Claude Loads a Skill

```
User message
    │
    ▼
Claude reads skills/ description fields
    │
    ▼  ← trigger phrases match
Claude loads SKILL.md into context
    │
    ▼
Claude follows the instructions,
calling scripts or reading templates as needed
```

Skills are **self-contained**: each folder is independently usable and makes no assumptions about other skills being present.

---

## SKILL.md Format

Every skill starts with a `SKILL.md` file structured as follows:

```markdown
---
name: my-skill-name
description: When to trigger this skill and what it does. Use this when ...
license: Apache 2.0   # optional
---

# My Skill — Instructions

Detailed instructions that Claude will follow when this skill is active.

## Section 1
...

## Section 2
...
```

### Frontmatter fields

| Field | Required | Purpose |
|-------|----------|---------|
| `name` | ✅ Yes | Unique identifier (lowercase, hyphens for spaces) |
| `description` | ✅ Yes | Trigger description — Claude uses this to decide when to activate the skill |
| `license` | ❌ No | Human-readable license reference. Omit for Apache 2.0. |

### Writing a good description

The `description` field is the most important line in a skill. It tells Claude:

- **When** to activate: include concrete trigger phrases (`"Use this when … "`, `"Triggers include: …"`)
- **What** the skill does at a high level
- **What not to do**: specify exclusions (`"Do NOT use for PDFs"`) to prevent false triggers

Example (docx skill):

> *"Use this skill whenever the user wants to create, read, edit, or manipulate Word documents (.docx files). Triggers include: any mention of 'Word doc', 'word document', '.docx', or requests to produce professional documents with formatting… Do NOT use for PDFs, spreadsheets, Google Docs, or general coding tasks unrelated to document generation."*

---

## Skill Patterns

Skills in this repository demonstrate five recurring patterns:

### 1 — Pure Instructions

No scripts. Claude handles all logic from the instructions alone.

**Examples:** `doc-coauthoring`, `frontend-design`, `brand-guidelines`, `internal-comms`

**When to use:** Tasks where Claude's natural language and reasoning are sufficient — writing, design decisions, structured workflows.

### 2 — Script-Backed

Scripts handle deterministic operations (file format manipulation, formula recalculation, validation) that Claude cannot do reliably on its own.

**Examples:** `docx`, `pdf`, `pptx`, `xlsx`

**Typical directory layout:**
```
my-skill/
├── SKILL.md
└── scripts/
    ├── office/         # shared LibreOffice utilities
    │   ├── pack.py
    │   ├── unpack.py
    │   ├── soffice.py
    │   └── validate.py
    └── my_utility.py
```

**Pattern:**
1. Claude calls the unpack script to expose raw XML.
2. Claude edits the XML directly.
3. Claude calls the pack/validate script to produce a clean output file.

### 3 — Reference-Heavy

Rich reference documentation (API specs, protocol guides, best-practice documents) that Claude reads to generate accurate, idiomatic output.

**Examples:** `mcp-builder`, `skill-creator`, `claude-api`

**Typical directory layout:**
```
my-skill/
├── SKILL.md
└── reference/
    ├── best_practices.md
    ├── typescript_guide.md
    └── python_guide.md
```

### 4 — Template-Based

Reusable HTML, JS, or Markdown templates that Claude fills in based on user input.

**Examples:** `algorithmic-art`, `canvas-design`, `theme-factory`

**Typical directory layout:**
```
my-skill/
├── SKILL.md
└── templates/
    ├── viewer.html
    └── generator_template.js
```

### 5 — Interactive / Library

A Python or JavaScript library is packaged with the skill and called by Claude to produce runnable output.

**Examples:** `slack-gif-creator`, `web-artifacts-builder`, `webapp-testing`

---

## Plugin Groups

The file `.claude-plugin/marketplace.json` registers the repository as a Claude Code plugin marketplace and groups skills into installable collections:

```json
{
  "name": "anthropic-agent-skills",
  "plugins": [
    {
      "name": "document-skills",
      "skills": ["./skills/xlsx", "./skills/docx", "./skills/pptx", "./skills/pdf"]
    },
    {
      "name": "example-skills",
      "skills": [
        "./skills/algorithmic-art",
        "./skills/brand-guidelines",
        ...
      ]
    },
    {
      "name": "claude-api",
      "skills": ["./skills/claude-api"]
    }
  ]
}
```

When you add a new skill to `skills/`, add an entry to the appropriate plugin's `skills` array so it can be installed via `/plugin install`.

---

## Supporting File Conventions

| Path pattern | Convention |
|---|---|
| `scripts/office/` | Shared LibreOffice utilities (used by docx, pptx, xlsx) |
| `scripts/*.py` | Python utility called by Claude during task execution |
| `scripts/*.sh` | Shell script (setup, bundling) |
| `reference/*.md` | Documentation Claude reads for context |
| `examples/` | Worked examples and templates |
| `templates/` | Reusable HTML / JS / Markdown templates |
| `themes/` | Pre-defined colour/font palette files |
| `core/` | Python library module bundled with the skill |
| `assets/` | Images, PDFs, other binary assets |
| `*-fonts/` | Font files (TTF/OTF) |

---

## Wiki Auto-Update System

This wiki is generated automatically by `scripts/generate_wiki.py` and published by `.github/workflows/update-wiki.yml`.

### How it works

```
Push to main
    │
    ▼
GitHub Actions: update-wiki.yml
    │
    ├─ python scripts/generate_wiki.py
    │       │
    │       ├─ scans skills/  → one Skill-<name>.md per skill
    │       ├─ builds Home.md, Skills-Overview.md, _Sidebar.md, _Footer.md
    │       └─ copies wiki/*.md  (Getting-Started, Architecture, Contributing)
    │
    └─ git push → <repo>.wiki.git
```

### Adding a new skill to the wiki

Simply add `skills/<new-skill>/SKILL.md` and push. The workflow detects the change automatically and:

- Creates `Skill-<new-skill>.md`
- Adds the skill to `Home.md` and `Skills-Overview.md`
- Adds a link in `_Sidebar.md`

No manual wiki edits are required.

### Updating static pages

Edit any file in the `wiki/` directory and push. The workflow copies the updated file into the wiki on the next run.

---

## License Overview

| Skill group | License |
|---|---|
| `algorithmic-art`, `brand-guidelines`, `canvas-design`, `claude-api`, `doc-coauthoring`, `frontend-design`, `internal-comms`, `mcp-builder`, `skill-creator`, `slack-gif-creator`, `theme-factory`, `web-artifacts-builder`, `webapp-testing` | Apache 2.0 |
| `docx`, `pdf`, `pptx`, `xlsx` | Proprietary (source-available) — see `LICENSE.txt` in each folder |

---

*See also: [Getting Started](Getting-Started) · [Contributing](Contributing) · [Skills Overview](Skills-Overview)*
