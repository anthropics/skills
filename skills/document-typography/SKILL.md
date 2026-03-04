---
name: document-typography
description: "Typographic quality control for generated documents (.docx, .pptx, .pdf). Use this skill WHENEVER generating documents with text content — especially numbered lists, bullet points, rules, instructions, or any content where line-wrapping matters. This skill prevents orphan word wrap (1-6 words spilling onto the next line), widow/orphan paragraphs (section headers stranded at page bottom), and numbering alignment issues. Trigger this skill for: document generation, Word files, presentations, reports, letters, any docx/pptx/pdf creation, any list or numbered content, resumes, proposals, manuals, rulebooks, guides. Even if the user doesn't mention typography — use it. Layout quality is invisible when done right and painfully obvious when wrong."
---

# Document Typography Skill

## The Problem

LLMs generate documents without visual feedback. This leads to:
- **Orphan word wrap**: a line that's 1-6 words too long, causing an ugly short spillover
- **Widow paragraphs**: a section header with only 1-2 lines stranded at the bottom of a page
- **Numbering misalignment**: numbered lists that shift when going from 1-digit to 2-digit to 3-digit numbers
- **Quote overflow**: citations or quotes that don't fit on a single line

Users rarely ask for good typography — they expect it. These issues are invisible when done right and painfully obvious when wrong. This is the difference between "AI output" and publishable work.

## The Solution: Render-Check-Fix Cycle

After generating any document, ALWAYS run this cycle:

```
1. Generate the .docx / .pptx / .pdf
2. Convert to PDF via LibreOffice
3. Render pages as images (pdftoppm)
4. Visually inspect each page with the view tool
5. Identify problems
6. Fix text and regenerate
7. Repeat until clean
```

## Step 1: Measure Line Width (M-count method)

Before writing content, determine the safe character limit using the M-count method. The letter "M" is the widest character in virtually every font. Count how many M's fit on one line — that's your guaranteed safe maximum. Any real sentence with normal letters (which are narrower than M) will always fit.

```bash
python /path/to/skill/scripts/measure_m_count.py --font "Georgia" --size 11 --indent 620
```

This gives you two numbers:
- **M-count** (safe max): guaranteed to fit on one line. Use this as your hard limit.
- **Avg-count** (reference): what average text fits. Use this for two-line planning.

Example output for Georgia 11pt, A4, 1" margins, 620 DXA indent:
- M-count: 38 chars (any sentence ≤38 chars always fits on one line)
- Avg-count: 67 chars (typical text wraps around here)

The M-count is conservative but eliminates the danger zone entirely. No visual inspection needed for orphan detection — if your sentence is ≤ M-count, it fits. Period.

For two-line rules: keep the first sentence ≤ M-count (it becomes line 1), then the second sentence fills line 2. The sentence break falls naturally at the line wrap.

### Alternative: visual measurement

If you want to use the full line width (avg-count), use the render-check approach instead. Generate a test document with lines of known length:

```bash
python /path/to/skill/scripts/measure_line_width.py --font "Georgia" --size 11 --indent 620
node line_width_test.js
bash /path/to/skill/scripts/check_layout.sh line_width_test.docx
```

Then visually inspect to find the exact wrap point. This gives ~75% more characters per line but requires the render-check-fix cycle to catch edge cases.

## Step 2: Write Content Within Limits

For every line of text (rules, bullet points, numbered items), check its character count against the measured limit. Each line should be ONE of:

### Single line (best)
`length <= MAX_CHARS` — fits perfectly on one line.

### Two full lines (acceptable)
`length >= MAX_CHARS + 8` — fills two lines well. 
CRITICAL: the natural sentence break (period, comma) should fall near the MAX_CHARS position so the line wraps at a natural point.

### Danger zone (NEVER)
`MAX_CHARS < length <= MAX_CHARS + 6` — this wraps with 1-6 orphan words. ALWAYS rewrite these.

### Rewriting strategies for danger zone lines

**Too long for one line by a few words:**
- Shorten: remove filler words, use shorter synonyms
- Split into two sentences that each fit on one line

**Two short sentences that together spill over:**
- Combine with a comma instead of a period (saves ~1 char + allows reflow)
- Example: "Pf1 redt levens. Onderschat hem niet." → "Pf1 redt levens, onderschat hem niet."

**Needs two lines but second line is too short:**
- Rewrite so the sentence break falls at ~MAX_CHARS
- Add meaningful content to fill the second line
- Example: "Reken bij schaak, slag, dreiging. In rustige stellingen denk in plannen." (wraps with "plannen." orphaned) → "Reken bij forcerende zetten zoals schaak, slag of directe dreiging. In rustige stellingen denk je in plannen." (wraps cleanly at the period)

## Step 3: Check for Orphan Lines with Script

After writing all content, run the orphan checker:

```bash
python /path/to/skill/scripts/check_orphans.py rules.txt --max1 68 --max2 136
```

This reports every line in the danger zone. Fix all reported lines before generating the document.

## Step 4: Render and Visually Inspect

After generating the document:

```bash
bash /path/to/skill/scripts/check_layout.sh document.docx
```

Then inspect each page image with the `view` tool. Check for:

### Orphan word wrap
Lines where 1-4 words spill to the next line. Fix by rewriting the text shorter or longer.

### Widow paragraphs ("toilet paper effect")
A section header with only 1-2 lines at the bottom of a page, with the rest on the next page. Fix by:
- Adding `pageBreakBefore: true` to push the whole section to the next page
- Adding `keepNext: true` to headings so they stay with their first content paragraph
- Rebalancing content so at least 3-4 lines follow the header on the same page

### Numbering alignment
Numbers jumping from "9." to "10." or "99." to "100." causing indent shifts. Fix by using manual numbering with fixed-width indentation (e.g., 620 DXA) instead of auto-numbering.

### Quote overflow
Citations that wrap to a second line. Fix by shortening the attribution: "— Capablanca" instead of "— José Raúl Capablanca"

## Step 5: Iterate

Repeat steps 4-5 until all pages are clean. Typically takes 2-3 iterations.

## Layout Principles Summary

These principles apply universally — documents, presentations, emails, reports:

1. **Every line should either fit perfectly or fill two lines well.** No orphan spillover.
2. **Section headers never stand alone at the bottom of a page.** Always with 3+ lines of content.
3. **Sentence breaks should fall at natural line-wrap points.** Write to the grid.
4. **Two short sentences are better as one comma-sentence** if they'd otherwise create an orphan together.
5. **Numbering needs fixed-width indentation** to handle single, double, and triple digits without shifting.
6. **Measure first, write second.** Always know your character limit before composing content.
7. **Visual verification is mandatory.** Never ship a document without rendering and inspecting it.

## Integration with Other Skills

This skill complements the docx, pptx, and pdf skills. The workflow is:
1. Read the relevant creation skill (docx/pptx/pdf) for file format specifics
2. Read THIS skill for typographic quality rules
3. Generate content respecting both format requirements AND typography rules
4. Render-check-fix cycle until clean

---

*Typographic principles in this skill emerged from iterative human-AI collaboration between [@PGTBoos](https://github.com/PGTBoos) and Claude.   
The M-count formula and the render-check-fix cycle were born from a user who kept pointing out what the AI couldn't see.*
