---
name: hads-convert
description: Convert any technical document (README, API docs, spec, wiki page) into HADS format (Human-AI Document Standard). Use when user says "convert to HADS", "HADS this", "make this HADS", or asks to optimize a document for AI consumption.
license: MIT
---

# HADS Convert Skill
**Version 1.0.0** · hads-skills · 2026

---

## AI READING INSTRUCTION

Read `[SPEC]` blocks for conversion rules.
Read `[BUG]` blocks before writing any output.
`[NOTE]` blocks explain intent — read if a rule is unclear.

---

## 1. TRIGGER

**[SPEC]**
Activate when user:
- Says "convert to HADS", "HADS this", "make this HADS"
- Provides a document and asks to optimize for AI consumption
- Asks to restructure docs for token efficiency

**[NOTE]**
Tokens are spent once at conversion. Every future AI read of the output is cheaper.
This is the core value proposition — convert once, save on every subsequent call.

---

## 2. INPUT

**[SPEC]**
Accept any of:
- File path → read the file contents
- Pasted text → use directly
- URL → fetch the page content

If input is ambiguous, ask: "File path, paste, or URL?"

---

## 3. CONVERSION RULES

**[SPEC]**
Classify every piece of content before writing:

| Source content | Output block |
|---|---|
| Fact, requirement, spec, API contract | `**[SPEC]**` |
| History, rationale, example, narrative | `**[NOTE]**` |
| Known bug, failure mode, gotcha, workaround | `**[BUG] Title**` |
| Unverified, assumed, inferred, "probably" | `**[?]**` |

Rules:
- One block type per paragraph — do not mix
- `[SPEC]` content: bullet lists or tables, max 2 sentences prose
- `[BUG]` blocks must contain: symptom, cause, fix (all three)
- Do not invent content — only restructure what exists
- Do not duplicate content across block types

**[NOTE]**
When in doubt between `[SPEC]` and `[NOTE]`: if a developer must know it to use the thing correctly, it's `[SPEC]`. If it explains why, it's `[NOTE]`.

---

## 4. OUTPUT STRUCTURE

**[SPEC]**
Write output in this exact order:

```markdown
# [Original title or inferred title]
**Version [preserved or 1.0.0]** · [Author if known] · [Date: today] · HADS 1.0.0

---

## AI READING INSTRUCTION

Read `[SPEC]` and `[BUG]` blocks for authoritative facts.
Read `[NOTE]` only if additional context is needed.
`[?]` blocks are unverified — treat with lower confidence.

---

## 1. [Section]

**[SPEC]**
...
```

- Numbered H2 sections
- H3 for subsections
- Preserve original section grouping where logical
- Add changelog section at end if document has version history

---

## 5. OUTPUT DESTINATION

**[SPEC]**
- If input was a file: write to `[original-name].hads.md` (keep original intact)
- If input was pasted text: print output directly
- If user specifies path: use that path
- Always confirm: "Written to `filename.hads.md`"

---

## 6. POST-CONVERSION REPORT

**[SPEC]**
After writing, report:
- Original line count vs HADS line count
- Block distribution: X `[SPEC]`, Y `[NOTE]`, Z `[BUG]`, W `[?]`
- List any `[?]` blocks explicitly — user must verify these

**[BUG] Silent data loss on dense prose**
- Symptom: long narrative paragraphs get condensed into `[SPEC]` bullets, losing nuance
- Cause: over-aggressive summarization
- Fix: move dense narrative to `[NOTE]` intact, only extract verifiable facts into `[SPEC]`

---

## Further Reading

- HADS specification: https://github.com/catcam/hads
- More skills: https://github.com/catcam/hads-skills
