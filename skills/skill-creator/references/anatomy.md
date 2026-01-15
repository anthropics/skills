# Skill Anatomy

Detailed breakdown of skill structure, component purposes, and organizational patterns.

## What Are Skills?

Skills are modular, self-contained packages that extend Claude's capabilities with specialized workflows, tools, and domain knowledge. They transform Claude from a general-purpose agent into a specialized agent equipped with procedural knowledge that models cannot fully possess through training alone.

### What Skills Provide

1. **Specialized workflows** - Multi-step procedures for specific domains
2. **Tool integrations** - Instructions for working with specific file formats or APIs
3. **Domain expertise** - Company-specific knowledge, schemas, business logic
4. **Bundled resources** - Scripts, references, and assets for complex tasks

### Why Skills Matter

The context window is finite. Skills share this space with system prompts, conversation history, and user requests. Effective skills maximize their value-per-token by:
- Providing only non-obvious information
- Using progressive disclosure to load details only when needed
- Leveraging scripts and assets that execute without context overhead

## Directory Structure

### Minimal Skill

```
skill-name/
└── SKILL.md
```

Only SKILL.md is required. Use this for simple, instruction-only skills.

### Typical Skill

```
skill-name/
├── SKILL.md
├── scripts/
│   └── script.py
└── references/
    └── domain.md
```

Most skills include scripts for repeated operations and references for domain knowledge.

### Complex Skill

```
skill-name/
├── SKILL.md
├── scripts/
│   ├── initialize.py
│   ├── process.py
│   └── validate.sh
├── references/
│   ├── workflows.md
│   ├── schema.md
│   └── examples.md
└── assets/
    ├── templates/
    │   └── report-template.docx
    └── logos/
        └── company-logo.png
```

Complex skills may include all three resource types for different purposes.

## Component Details

### SKILL.md

The core instruction file, always loaded when the skill triggers.

**Structure:**
```markdown
---
name: skill-name
description: What it does and when to use it
license: Complete terms in LICENSE.txt
---

# Title

Brief overview.

## Core Instructions
...

## Progressive Disclosure
- Link to references/ for detailed info
- Keep under 500 lines
```

**When Claude reads SKILL.md:**
- After skill is triggered (by matching description)
- Before executing any tool calls
- When user explicitly mentions the skill

**When Claude doesn't read SKILL.md:**
- During skill discovery (only metadata is visible)
- When skill isn't triggered
- When working in other contexts

### scripts/

Executable code that performs operations without consuming context tokens.

**When to use scripts:**
- Same code is rewritten repeatedly across conversations
- Operations require deterministic reliability
- Code is too large to include in SKILL.md
- Performance matters (scripts execute faster than Claude can generate equivalent code)

**Script examples:**
```
pdf-processor/
├── scripts/
│   ├── extract_text.py      # Text extraction with pdfplumber
│   ├── rotate_pdf.py        # PDF page rotation
│   ├── merge_pdfs.py        # Combine multiple PDFs
│   └── fill_form.py         # PDF form filling
```

**How scripts save tokens:**
- Claude can execute scripts without reading their full contents
- Only the script filename and parameters appear in context
- Complex logic is compressed into executable form

**When scripts must be read:**
- Claude needs to patch or modify the script
- Environment-specific adjustments are required
- User asks to understand script behavior
- Debugging script failures

### references/

Documentation and reference material loaded into context as needed.

**When to use references:**
- Domain knowledge needed during execution (schemas, APIs, policies)
- Content is too large for SKILL.md (>10k words)
- Information is conditional (only needed for specific variants)
- Content requires detailed explanation or examples

**Reference examples:**
```
bigquery-skill/
├── SKILL.md              # Query workflow + navigation
└── references/
    ├── finance.md        # Billing tables, revenue schemas
    ├── sales.md          # Opportunities, pipeline schemas
    ├── product.md        # API usage, feature tables
    └── marketing.md      # Campaigns, attribution schemas
```

**How references work:**
1. SKILL.md mentions the reference: "See [references/finance.md](references/finance.md) for billing queries"
2. User asks a billing question
3. Claude loads only finance.md into context
4. Other domain files remain unloaded, saving tokens

**Reference organization patterns:**

**By domain:**
```
company-data/
├── SKILL.md
└── references/
    ├── sales.md
    ├── marketing.md
    └── finance.md
```

**By feature:**
```
docx-skill/
├── SKILL.md
└── references/
    ├── tracked-changes.md
    ├── comments.md
    └── formatting.md
```

**By complexity:**
```
pdf-skill/
├── SKILL.md
└── references/
    ├── basic.md          # Simple extraction
    ├── advanced.md       # Forms, OCR
    └── edge-cases.md     # Encrypted, corrupted files
```

### assets/

Files used in output, not for context consumption.

**When to use assets:**
- Templates need to be included in final output
- Images or logos must be embedded
- Boilerplate code serves as starting point
- Fonts, styles, or other resources are needed

**Asset examples:**
```
report-generator/
├── SKILL.md
└── assets/
    ├── templates/
    │   ├── monthly-report.docx
    │   └── quarterly-report.pptx
    ├── logos/
    │   └── company-logo.png
    └── fonts/
        └── brand-font.ttf
```

**How assets differ from references:**
- Assets are copied/modified in output (e.g., template → report)
- References are read for information (e.g., schema → query)
- Assets may be binary (images, fonts)
- References are always text (markdown, code)

**Asset usage pattern:**
1. User: "Generate a monthly sales report"
2. Claude reads SKILL.md for workflow
3. Claude loads assets/templates/monthly-report.docx
4. Claude fills template with data from BigQuery
5. Claude outputs modified docx file
6. Template file never enters context (only file path is referenced)

## Frontmatter Deep Dive

### name

**Purpose:** Unique identifier for the skill

**Requirements:**
- Max 64 characters
- Must match directory name
- Use gerund form (`creating-skills`, not `skill-creator`)
- Use kebab-case (`pdf-processor`, not `PDFProcessor`)

**Examples:**
- ✅ `creating-skills`
- ✅ `pdf-processor`
- ✅ `bigquery-analytics`
- ❌ `skill_creator` (snake_case)
- ❌ `SkillCreator` (PascalCase)
- ❌ `create-a-new-thing` (not gerund)

### description

**Purpose:** Primary trigger mechanism for skill activation

**Requirements:**
- Max 500 characters
- Include both what and when
- High keyword density
- Describe specific triggers/use cases

**Good description:**
> "Process PDF documents with text extraction, form filling, and rotation. Use when Claude needs to: (1) Extract text from PDFs using pdfplumber, (2) Fill PDF forms programmatically, (3) Rotate or merge PDF pages, or any PDF manipulation tasks"

**Why it works:**
- Specific actions: extract, fill, rotate, merge
- Specific tools: pdfplumber
- Specific triggers: numbered list of use cases
- Comprehensive scope: "or any PDF manipulation tasks"

**Poor description:**
> "Guide for creating effective skills. This skill should be used when users want to create a new skill."

**Why it fails:**
- Passive opener: "Guide for" is documentary
- First-person: "This skill should be used" is meta-commentary
- Low keyword density: vague phrasing
- Missing triggers: doesn't say when to use

### license

**Purpose:** Legal terms for skill distribution

**Format:** `Complete terms in LICENSE.txt`

**Note:** Most skills use standard license files. Include LICENSE.txt in skill root if distributing.

## Hooks (Claude Code 2.1+)

Hooks control skill activation and execution flow.

### PreToolUse

Execute before tool calls.

**Use case:** Validate or prepare environment before execution

```yaml
---
hooks:
  PreToolUse:
    - matcher: Bash
      hooks:
        - type: command
          command: "npx block-no-verify"
---
```

**Example:** Block git commands with `--no-verify` flag

### PostToolUse

Execute after tool calls complete.

**Use case:** Clean up or log after execution

```yaml
---
hooks:
  PostToolUse:
    - matcher: Read
      hooks:
        - type: command
          command: "log-read-file.sh"
---
```

### PreResponse

Execute before Claude responds to user.

**Use case:** Modify or validate response content

### PostResponse

Execute after response is sent.

**Use case:** Trigger notifications or updates

## Context Forking (Claude Code 2.1+)

Isolate parallel operations to prevent context bloat.

**When to use:**
- Skill handles multiple independent tasks
- Tasks don't share context
- Parallel execution would duplicate context

**Example:**
```yaml
---
name: multi-file-processor
description: Process multiple files independently
forking:
  enabled: true
  maxForks: 5
---
```

**Behavior:**
- Each file processed in separate context fork
- No shared context between forks
- Reduces token usage for parallel operations
- Results merged after completion

## Token Efficiency Strategies

### Progressive Disclosure

Load information only when needed:

1. **Metadata** (always loaded): ~100 words
2. **SKILL.md** (when triggered): <5k words
3. **References** (as needed): unlimited but conditional

### Content Allocation

**Keep in SKILL.md:**
- Decision frameworks
- Execution patterns
- Resource references
- Critical domain knowledge

**Move to references/:**
- Detailed explanations
- Examples and patterns
- Schema documentation
- Variant-specific details

**Execute as scripts:**
- Repeated operations
- Deterministic logic
- Performance-critical code

### Line Limits

**SKILL.md:**
- Maximum: 500 lines
- Recommended: 150-250 lines
- Rationale: Context window is shared with everything else

**References/:**
- No strict limit
- Use grep patterns for files >10k words
- Organize into multiple files by domain/variant

**Scripts/:**
- No limit (executed, not loaded)
- Keep readable for debugging
- Include docstrings for maintainability

## Naming Conventions

### Directory Names

- Use kebab-case: `pdf-processor`, `creating-skills`
- Use gerunds for skills: `creating-skills`, `processing-pdfs`
- Be descriptive but concise: `docx-editor`, not `microsoft-word-document-editor`

### File Names

- SKILL.md (required, exact case)
- references/: descriptive, lowercase: `finance.md`, `workflows.md`
- scripts/: descriptive, snake_case: `extract_text.py`
- assets/: descriptive, lowercase with extensions: `logo.png`, `template.docx`

## Validation

Skills are validated automatically during packaging. The validator checks:

1. **Frontmatter:**
   - Valid YAML format
   - Required fields present (name, description, license)
   - Name matches directory name
   - Name max 64 characters, gerund form
   - Description max 500 characters

2. **File Organization:**
   - SKILL.md exists
   - No prohibited files (README.md, etc.)
   - Referenced files exist

3. **Description Quality:**
   - Not empty
   - Contains specific keywords
   - Describes when to use

4. **Line Limits:**
   - SKILL.md under 500 lines

Run validation manually: `scripts/validate_skill.py <skill-folder>`
