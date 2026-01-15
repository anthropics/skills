---
name: creating-skills
description: Create and iterate on Agent Skills with proper structure, frontmatter, progressive disclosure, and packaging. Use when building new skills, refactoring existing skills, or validating skill structure against specification. Covers SKILL.md frontmatter (name, description, hooks), body organization (scripts/, references/, assets/), token efficiency strategies, and .skill packaging requirements.
license: Complete terms in LICENSE.txt
---

# Creating Skills

Create modular, token-efficient skills that extend Claude's capabilities with specialized workflows, tools, and domain knowledge.

## Quick Start

1. **Gather examples** - Collect 3-5 concrete usage examples
2. **Plan resources** - Identify scripts, references, assets needed
3. **Initialize** - Run `scripts/init_skill.py <skill-name> --path <output-dir>`
4. **Implement** - Build resources and write SKILL.md
5. **Package** - Run `scripts/package_skill.py <skill-folder>` (REQUIRED - creates .skill file)
6. **Iterate** - Refine based on real usage

## Core Principles

### Token Efficiency

Minimize SKILL.md length. Claude already understands base behavior. Challenge each line: does this justify its token cost?

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

See [references/anatomy.md](references/anatomy.md) for detailed skill structure.

### Degrees of Freedom

Match specificity to task fragility:

| Freedom | When to Use | Example |
|---------|-------------|---------|
| **High** (text instructions) | Multiple valid approaches, context-dependent | "Choose appropriate chart type based on data distribution" |
| **Medium** (pseudocode + parameters) | Preferred pattern exists, some variation | "Use pandas groupby with agg() for aggregations" |
| **Low** (specific scripts) | Error-prone, consistency critical | `scripts/rotate_pdf.py` for PDF rotation |

## Skill Structure

### Required Files

```
skill-name/
├── SKILL.md          # Required: Metadata + instructions
└── (optional bundled resources)
```

### Optional Bundled Resources

**scripts/** - Executable code for repeated operations
- Use when: Same code rewritten repeatedly, deterministic reliability needed
- Example: `scripts/rotate_pdf.py`
- Benefit: Executed without loading into context

**references/** - Documentation for context loading
- Use when: Domain knowledge, schemas, API docs needed during execution
- Example: `references/finance.md` for billing schemas
- Benefit: Loaded only when needed
- Best practice: Keep SKILL.md lean, use grep patterns for large files (>10k words)

**assets/** - Files for output (not context)
- Use when: Templates, images, boilerplate code needed in final output
- Example: `assets/logo.png`, `assets/template.html`
- Benefit: Separated from documentation

**Include only files directly required for skill execution.** No README.md, INSTALLATION_GUIDE.md, CHANGELOG.md, or other auxiliary documentation.

## Frontmatter

### Required Fields

```yaml
---
name: skill-name              # Must match directory name
description: Your description  # Primary trigger mechanism
license: Complete terms in LICENSE.txt
---
```

**Name:**
- Use gerund form (e.g., `creating-skills`, not `skill-creator`)
- Max 64 characters
- Must match directory name

**Description:**
- Include what the skill does AND when to use it
- Max 500 characters
- High keyword density for discoverability
- Describe specific triggers/use cases

**Example description:**
> "Process PDF documents with text extraction, form filling, and rotation. Use when Claude needs to: (1) Extract text from PDFs using pdfplumber, (2) Fill PDF forms programmatically, (3) Rotate or merge PDF pages, or any PDF manipulation tasks"

### Optional Hooks (Claude Code 2.1+)

Control skill activation with hooks:

```yaml
---
hooks:
  PreToolUse:
    - matcher: Bash
      hooks:
        - type: command
          command: "validate-script.sh"
---
```

Available hooks: `PreToolUse`, `PostToolUse`, `PreResponse`, `PostResponse`.

## Progressive Disclosure

Organize content by when it's needed:

1. **Metadata (name + description)** - Always loaded (~100 words)
2. **SKILL.md body** - When skill triggers (<5k words, <500 lines)
3. **Bundled resources** - As needed (unlimited - scripts execute without context load)

### Patterns

**Variant separation:**
```
cloud-deploy/
├── SKILL.md              # Workflow + provider selection
└── references/
    ├── aws.md            # AWS patterns (loaded only for AWS)
    ├── gcp.md            # GCP patterns (loaded only for GCP)
    └── azure.md          # Azure patterns (loaded only for Azure)
```

**Domain separation:**
```
bigquery-skill/
├── SKILL.md              # Overview and navigation
└── references/
    ├── finance.md        # Revenue, billing metrics
    ├── sales.md          # Opportunities, pipeline
    └── product.md        # API usage, features
```

**Conditional details:**
```markdown
## PDF Text Extraction

Use pdfplumber for text extraction: [code example]

## Form Filling
See [FORMS.md](FORMS.md) for complete guide to form manipulation.

## OCR
See [OCR.md](OCR.md) for text extraction from image-based PDFs.
```

See [references/anatomy.md](references/anatomy.md) for detailed patterns and examples.

## Implementation Workflow

### 1. Understand Requirements

Gather 3-5 concrete examples. Ask:
- "What functionality should this skill support?"
- "Can you provide example usage scenarios?"
- "What would a user say that should trigger this skill?"

Avoid overwhelming users with multiple questions in a single message.

### 2. Plan Resources

Analyze each example:
1. Consider execution from scratch
2. Identify reusable scripts, references, assets

**Example:** PDF editor skill
- Query: "Rotate this PDF"
- Analysis: Same rotation code rewritten repeatedly
- Resource: `scripts/rotate_pdf.py`

### 3. Initialize Skill

Always run `init_skill.py` for new skills:

```bash
scripts/init_skill.py <skill-name> --path <output-directory>
```

This creates:
- Skill directory with SKILL.md template
- Example resource directories: `scripts/`, `references/`, `assets/`

### 4. Implement Resources

**Start with bundled resources:**
- Test scripts by running them
- Delete unused example directories
- Add user-provided assets/docs as needed

**Write SKILL.md:**
- Use imperative/infinitive form ("Create X", not "Creates X")
- Put all "when to use" information in description, not body
- Reference other files with clear guidance on when to read them
- Keep under 500 lines

**Consult design patterns:**
- [references/workflows.md](references/workflows.md) - Multi-step processes, conditional logic
- [references/output-patterns.md](references/output-patterns.md) - Output formats, templates

### 5. Package Skill (REQUIRED)

**Skills MUST be packaged into .skill files for use.**

```bash
scripts/package_skill.py <path/to/skill-folder>
```

Optional output directory:

```bash
scripts/package_skill.py <path/to/skill-folder> ./dist
```

The packaging script:
1. **Validates** the skill:
   - YAML frontmatter format
   - Required fields (name, description, license)
   - Naming conventions (max 64 chars, gerund form)
   - File organization
   - Description quality and completeness

2. **Creates** `.skill` file (zip archive) if validation passes

If validation fails, fix errors and re-run. The .skill file is what users install - distribution requires this step.

### 6. Iterate

Use on real tasks. Notice struggles. Update SKILL.md or resources. Test again.

## Context Forking (Claude Code 2.1+)

For skills with multiple independent tasks, use context forking to isolate work:

```yaml
---
name: multi-task-skill
description: ...
forking:
  enabled: true
  maxForks: 3
---
```

Each fork gets isolated context, preventing token bloat from parallel operations.
