# Writing Guidelines

Conventions for the content of the skill you're writing. SKILL.md covers structure and process; this file covers what goes inside.

## Contents
- Content
  - Match the degree of freedom to the task
  - Only add what Claude doesn't already know
  - Avoid time-sensitive wording
  - Use consistent terminology
  - Offer a default, not a menu
- Workflows
  - Checklists for complex tasks
  - Feedback loops
  - Plan, validate, then execute
- Scripts
  - Solve, don't defer
  - Justify every constant
  - Say whether to run or read
  - Declare dependencies
  - MCP tool names
  - Paths and file names

---

## Content

### Match the degree of freedom to the task

How specific to be depends on how fragile the task is. Think of Claude walking a path: on a narrow bridge with cliffs on both sides there's one safe way forward, so give exact guardrails. In an open field, give a direction and trust Claude to pick the route.

- **High freedom** (text heuristics): several approaches are valid and the right one depends on context. Example: "Check for edge cases and suggest readability improvements."
- **Medium freedom** (pseudocode or a parameterized script): a preferred pattern exists, but some variation is fine. Example: a `generate_report(data, format="markdown")` template to adapt.
- **Low freedom** (exact commands): the operation is error-prone, consistency is critical, or steps must happen in order. Example: "Run exactly `python scripts/migrate.py --verify --backup`. Don't add flags."

### Only add what Claude doesn't already know

Claude is already smart. Once the skill loads, every paragraph competes with the conversation for context, so each one should justify its token cost. Ask: does Claude really need this explanation?

```markdown
# Good
Use pdfplumber for text extraction:
    with pdfplumber.open("file.pdf") as pdf: text = pdf.pages[0].extract_text()

# Bad
PDF (Portable Document Format) files are a common format that contains text and images.
To extract text you'll need a library. There are many available, but pdfplumber is...
```

### Avoid time-sensitive wording

"If you're doing this before August 2025, use the old API" becomes wrong on a date nobody will remember to check. Describe the current method, and if the old one still matters, put it in a collapsible "Old patterns" section:

```markdown
## Old patterns
<details>
<summary>Legacy v1 API (deprecated)</summary>
The v1 API used `api.example.com/v1/messages`. It is no longer supported.
</details>
```

### Use consistent terminology

Pick one term per concept and use it everywhere. If the skill says "field" in one place and "box", "element", or "control" elsewhere, Claude has to guess whether they're the same thing.

### Offer a default, not a menu

"You can use pypdf, or pdfplumber, or PyMuPDF, or..." leaves Claude to choose with less context than you had. Give one default, plus an escape hatch for the case where it doesn't work: "Use pdfplumber for text extraction. For scanned PDFs that need OCR, use pdf2image with pytesseract instead."

---

## Workflows

### Checklists for complex tasks

For multi-step work, give Claude a checklist it can copy into its response and tick off. It keeps steps from being skipped and makes progress visible.

```markdown
Copy this checklist and check off items as you go:
- [ ] Step 1: Analyze the form (run scripts/analyze_form.py)
- [ ] Step 2: Create the field mapping (edit fields.json)
- [ ] Step 3: Validate the mapping (run scripts/validate_fields.py)
- [ ] Step 4: Fill the form (run scripts/fill_form.py)
```

### Feedback loops

Run the validator, fix what it reports, repeat, and only move on when validation passes. The validator can be a script or a reference document Claude checks against (a style guide, for example). Either way, the loop catches mistakes before they compound.

### Plan, validate, then execute

For batch, destructive, or high-stakes operations, have Claude write an intermediate plan file (e.g. `changes.json`), check it with a script, and only then apply it. Claude can iterate on the plan without touching the originals.

Make the validator's error messages specific enough to act on. "Field 'signature_date' not found. Available fields: customer_name, order_total, signature_date_signed" gets fixed on the next try; "invalid field" doesn't.

---

## Scripts

### Solve, don't defer

Scripts should handle the errors they can expect instead of failing and leaving Claude to recover. If a file might be missing, create it with a default or explain the alternative; don't just let `open()` raise.

### Justify every constant

If a script uses a timeout or retry count, say why it has that value. If you don't know the right number, Claude won't either.

```python
# HTTP requests typically finish within 30 seconds; the margin covers slow connections
REQUEST_TIMEOUT = 30

# Not this
TIMEOUT = 47  # why 47?
```

### Say whether to run or read

Be explicit about what Claude should do with a script:
- **Run it** (usually preferred, since only the output costs tokens): "Run `scripts/analyze_form.py` to extract the fields."
- **Read it** (when the logic itself is the point): "See `scripts/analyze_form.py` for the field extraction algorithm."

### Declare dependencies

List the packages a script needs with their install commands ("Install with `pip install pypdf`") rather than assuming they're present. Environments differ: claude.ai can install packages from PyPI and npm, but skills running through the Claude API have no network access and can't install packages at runtime.

### MCP tool names

When a skill uses MCP tools, use fully qualified names in the form `ServerName:tool_name` (e.g. `GitHub:create_issue`). Without the server prefix, Claude may fail to find the tool when several MCP servers are connected.

### Paths and file names

- Use forward slashes in every path (`scripts/helper.py`, never `scripts\helper.py`). Backslashes break on Unix systems.
- Name files after their content: `form_validation_rules.md`, not `doc2.md`.
