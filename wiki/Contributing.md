# 🤝 Contributing

This page walks you through creating a new skill, testing it, and submitting it to the repository.

---

## Overview

A skill is just a folder with a `SKILL.md` file. The simplest possible skill is two files:

```
skills/my-skill/
└── SKILL.md
```

More capable skills also include scripts, templates, or reference documents — but those are optional.

---

## Step 1 — Copy the Template

The `template/SKILL.md` file is the canonical starting point:

```markdown
---
name: my-skill-name
description: Replace with description of the skill and when Claude should use it.
---

# Insert instructions below
```

Create your skill folder and copy it in:

```bash
mkdir skills/my-skill
cp template/SKILL.md skills/my-skill/SKILL.md
```

---

## Step 2 — Write the Frontmatter

Open `skills/my-skill/SKILL.md` and fill in the two required fields.

### `name`

- Lowercase, hyphens instead of spaces.
- Should match the folder name.
- Example: `name: my-skill`

### `description`

The `description` field is what Claude reads to decide whether to activate your skill. Write it as if you are answering the question *"When should Claude use this skill?"*.

**Structure that works well:**

```
description: >
  Use this skill when [primary trigger].
  Triggers include: [comma-separated list of keywords or phrases].
  Also use when [secondary trigger].
  Do NOT use for [exclusions — prevent false triggers].
```

**Full example (pdf skill):**

```yaml
description: >
  Use this skill whenever the user wants to read, create, merge, split,
  fill forms in, OCR, encrypt, or otherwise process PDF files.
  Triggers include: any mention of ".pdf", "PDF", "form filling",
  "document scanning", or "extract text from PDF".
  Do NOT use for Word documents, spreadsheets, or presentations.
```

**Tips:**
- Be specific about trigger keywords so the skill does not fire accidentally.
- List exclusions explicitly — they are as important as inclusions.
- Keep the description under 500 characters if possible; longer descriptions still work but may affect routing accuracy.

---

## Step 3 — Write the Instructions

The markdown body of `SKILL.md` (everything after the closing `---`) is the instructions Claude follows.

### Structure your instructions clearly

```markdown
# My Skill

## Overview
Brief description of what the skill does.

## When to Use
Restate trigger conditions with more context.

## Step-by-Step Workflow
1. Step one
2. Step two
3. Step three

## Output Format
Describe the expected deliverables.

## Quality Standards
List quality checks or constraints.

## Examples
Worked examples are very helpful.
```

### Instruction writing tips

| Do | Don't |
|----|-------|
| Use numbered steps for sequential workflows | Leave the workflow implicit |
| Define the expected output format explicitly | Assume Claude knows the format |
| Include worked examples | Skip examples to save space |
| Reference script paths as `scripts/my_script.py` | Use absolute paths |
| Describe error handling (`if the script fails…`) | Ignore error cases |
| Use headings and tables for scannability | Write dense paragraphs |

---

## Step 4 — Add Supporting Files (Optional)

### Scripts

Place Python or shell scripts in `scripts/`:

```
skills/my-skill/
├── SKILL.md
└── scripts/
    └── my_utility.py
```

Reference them in your instructions as `scripts/my_utility.py` — Claude will find them relative to the skill folder.

### Reference documents

Place reference documentation in `reference/`:

```
skills/my-skill/
└── reference/
    └── api_guide.md
```

Tell Claude in the instructions to read the reference doc: *"Load `reference/api_guide.md` before starting."*

### Templates

Place reusable templates in `templates/`:

```
skills/my-skill/
└── templates/
    └── base.html
```

Tell Claude to use the template as a starting point rather than generating from scratch.

---

## Step 5 — Add a Licence File

If your skill contains proprietary content, add a `LICENSE.txt` to the skill folder and reference it in the frontmatter:

```yaml
license: Proprietary. LICENSE.txt has complete terms.
```

If your skill is open source (Apache 2.0), you can omit the `license` field — Apache 2.0 is the repository default.

---

## Step 6 — Register in the Plugin Marketplace (Optional)

To make your skill installable via `/plugin install`, add it to `.claude-plugin/marketplace.json`:

```json
{
  "plugins": [
    {
      "name": "example-skills",
      "skills": [
        ...,
        "./skills/my-skill"
      ]
    }
  ]
}
```

Choose the existing group that best fits your skill (`document-skills`, `example-skills`, or `claude-api`), or propose a new group in your pull request.

---

## Step 7 — Test Your Skill

### Manual testing in Claude Code

```bash
# Install Claude Code, then:
/skill load ./skills/my-skill

# Ask Claude to perform the task the skill covers
```

### Manual testing in Claude.ai

1. Go to a project → Skills → + Add skill.
2. Upload your `SKILL.md` (zip the folder if you have supporting files).
3. Enable the skill and test with a few prompts.

### Scripted evaluation (skill-creator pattern)

If your skill has verifiable outputs, write an XML evaluation file and run it:

```xml
<!-- skills/my-skill/evaluation.xml -->
<evaluation>
  <test>
    <input>Create a simple my-skill example.</input>
    <expected>Output contains X and Y.</expected>
  </test>
</evaluation>
```

```bash
python skills/skill-creator/scripts/aggregate_benchmark.py \
  --skill skills/my-skill \
  --eval skills/my-skill/evaluation.xml
```

---

## Step 8 — Submit a Pull Request

1. Fork the repository and create a branch: `git checkout -b add-my-skill`.
2. Add your skill folder under `skills/`.
3. Update `.claude-plugin/marketplace.json` if you want the skill to be installable as a plugin.
4. Open a pull request against `main` with:
   - A description of what the skill does.
   - Example inputs and expected outputs.
   - Notes on any dependencies (system packages, Python libraries).

The wiki will update automatically once your PR is merged — no wiki edits needed.

---

## Skill Quality Checklist

Before submitting, verify:

- [ ] `name` field matches the folder name exactly.
- [ ] `description` includes clear trigger phrases and exclusions.
- [ ] Instructions have a logical structure (overview → workflow → output format).
- [ ] Any scripts are referenced by relative path from the skill folder.
- [ ] The skill works end-to-end in at least one Claude interface.
- [ ] Outputs meet a professional quality bar (not just functional — polished).
- [ ] Licence information is correct (`LICENSE.txt` present if proprietary).
- [ ] `.claude-plugin/marketplace.json` updated if applicable.

---

## Design Principles

The skills in this repository follow these principles:

**Craftsmanship** — Every output should look and feel professionally designed. Raise the quality bar explicitly in your instructions.

**Specificity** — A narrow skill that does one thing extremely well is more valuable than a broad skill that does many things adequately.

**Modularity** — Skills work independently. Do not rely on another skill being loaded.

**Repeatability** — The same prompt should produce consistent, predictable output quality.

**Actionable errors** — When scripts fail, the error message should tell the user (or Claude) what to do next.

---

## Getting Help

- Read the [Architecture](Architecture) page to understand how skills are loaded.
- Look at an existing skill that is similar to what you want to build.
- Open a GitHub issue if you have questions or want feedback before building.

---

*See also: [Architecture](Architecture) · [Getting Started](Getting-Started) · [Skills Overview](Skills-Overview)*
