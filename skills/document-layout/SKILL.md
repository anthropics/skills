---
name: document-layout
description: "Layout quality control for generated documents (.docx, .pptx, .pdf). Use this skill WHENEVER generating documents with text content -- especially numbered lists, bullet points, rules, instructions, or any content where line-wrapping matters. This skill prevents orphan word wrap (1-6 words spilling onto the next line), widow/orphan paragraphs (section headers stranded at page bottom), and numbering alignment issues. Trigger this skill for: document generation, Word files, presentations, reports, letters, any docx/pptx/pdf creation, any list or numbered content, resumes, proposals, manuals, rulebooks, guides. Even if the user does not mention layout -- use it. Layout quality is invisible when done right and painfully obvious when wrong."
---

# Document Layout Skill

## The Problem

LLMs generate documents without visual feedback. This leads to:
- **Orphan word wrap**: a line that is 1-6 words too long, causing an ugly short spillover
- **Widow paragraphs**: a section header with only 1-2 lines stranded at the bottom of a page
- **Numbering misalignment**: numbered lists that shift when going from 1-digit to 2-digit to 3-digit numbers
- **Quote overflow**: citations or quotes that do not fit on a single line

Users rarely ask for good layout -- they expect it. These issues are invisible when done right and painfully obvious when wrong. This is the difference between "AI output" and publishable work.

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

## Step 1: Measure Line Width (P-count method)

Before writing content, determine the safe character limit using the P-count method. The letter "P" is wider than most characters but not as extreme as "M" or "W". Count how many P's fit on one line -- that is your practical safe maximum. Real text with a normal mix of letters will almost always fit.

```bash
python scripts/measure_p_count.py --font "Georgia" --size 11 --indent 620
```

This gives you two numbers:
- **P-count** (safe max): practically guaranteed to fit on one line. Use this as your hard limit.
- **Avg-count** (reference): what average text fits. Use this for two-line planning.

Example output for Georgia 11pt, A4, 1" margins, 620 DXA indent:
- P-count: 52 chars (any sentence of 52 chars or fewer fits on one line)
- Avg-count: 67 chars (typical text wraps around here)

Why "P" and not "M"? M-count (38 chars) is ultra-conservative -- safe but wastes space. P-count (52 chars) is the practical sweet spot: wider than most letters (e, a, o, t, i, l), only M and W are wider, and those rarely dominate real text. The result is about 35% more usable space than M-count while staying safe.

For two-line rules: keep the first sentence at or under the P-count (it becomes line 1), then the second sentence fills line 2. The sentence break falls naturally at the line wrap.

### Alternative: visual measurement

If you want to use the full line width (avg-count), use the render-check approach instead. Generate a test document with lines of known length:

```bash
python scripts/measure_line_width.py --font "Georgia" --size 11 --indent 620
node line_width_test.js
bash scripts/check_layout.sh line_width_test.docx
```

Then visually inspect to find the exact wrap point. This gives about 30% more characters per line but requires the render-check-fix cycle to catch edge cases.

## Step 2: Write Content Within Limits

For every line of text (rules, bullet points, numbered items), check its character count against the measured limit. Each line should be ONE of:

### Single line (best)
`length <= P_COUNT` -- fits perfectly on one line.

### Two full lines (acceptable)
`length >= P_COUNT + 8` -- fills two lines well.
CRITICAL: the natural sentence break (period, comma) should fall near the P_COUNT position so the line wraps at a natural point.

### Danger zone (NEVER)
`P_COUNT < length <= P_COUNT + 6` -- this wraps with 1-6 orphan words. ALWAYS rewrite these.

### Rewriting strategies for danger zone lines

**Too long for one line by a few words:**
- Shorten: remove filler words, use shorter synonyms
- Split into two sentences that each fit on one line

**Two short sentences that together spill over:**
- Combine with a comma instead of a period (saves about 1 char + allows reflow)
- Example: "The knight retreat saves lives. Do not underestimate it." becomes "The knight retreat saves lives, do not underestimate it."

**Needs two lines but second line is too short:**
- Rewrite so the sentence break falls at approximately P_COUNT
- Add meaningful content to fill the second line

## Step 3: Check for Orphan Lines with Script

After writing all content, run the orphan checker:

```bash
python scripts/check_orphans.py rules.txt --max1 52 --max2 104
```

This reports every line in the danger zone. Fix all reported lines before generating the document.

## Step 4: Render and Visually Inspect

After generating the document:

```bash
bash scripts/check_layout.sh document.docx
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
Citations that wrap to a second line. Fix by shortening the attribution.

## Step 5: Iterate

Repeat steps 4-5 until all pages are clean. Typically takes 2-3 iterations.

## Layout Principles Summary

These principles apply universally -- documents, presentations, emails, reports:

1. **Every line should either fit perfectly or fill two lines well.** No orphan spillover.
2. **Section headers never stand alone at the bottom of a page.** Always with 3+ lines of content.
3. **Sentence breaks should fall at natural line-wrap points.** Write to the grid.
4. **Two short sentences are better as one comma-sentence** if they would otherwise create an orphan together.
5. **Numbering needs fixed-width indentation** to handle single, double, and triple digits without shifting.
6. **Measure first, write second.** Always know your character limit before composing content.
7. **Visual verification is mandatory.** Never ship a document without rendering and inspecting it.
8. **Avoid em-dashes in running text.** Regular human writing rarely uses them outside of scientific papers and formal citations. Replace with commas, semicolons, or separate sentences for natural-sounding text.

## Integration with Other Skills

This skill complements the docx, pptx, and pdf skills. The workflow is:
1. Read the relevant creation skill (docx/pptx/pdf) for file format specifics
2. Read THIS skill for layout quality rules
3. Generate content respecting both format requirements AND layout rules
4. Render-check-fix cycle until clean

---

*This skill emerged from iterative human-AI collaboration between [@PGTBoos](https://github.com/PGTBoos) and Claude. The P-count formula and the render-check-fix cycle were born from a developer who kept pointing out what the AI could not see.*
