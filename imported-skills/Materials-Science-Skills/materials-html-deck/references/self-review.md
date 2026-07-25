# Self-Review And Verification

Open this reference for the self-review/corrective revision loop and final
verification.

## The Loop

After creating the first HTML deck draft, run at least one explicit self-review
pass before declaring the deck final.

1. Inspect the generated screenshots and extracted assets.
2. Write a short defect list with severity (`high`, `medium`, `low`) and slide
   numbers.
3. Correct every high-severity issue and every medium-severity issue that can be
   fixed without expanding the task substantially.
4. Regenerate the HTML deck after edits.
5. Re-run verification and update `qa_report.md` with what was checked, what was
   fixed, and what remains.

## Self-Review Checklist

Check content and structure:

- slide order follows the paper's argument,
- each slide has one dominant claim,
- slide titles are conclusion-style where possible,
- no invented numbers, mechanisms, datasets, claims, or implications,
- result slides include source labels and preserve scientific labels,
- speaker notes exist when planned and are useful for oral explanation.

Check visual and layout quality:

- no cropped-off figure titles, axes, legends, panel labels, or annotations,
- no source figure is squeezed so far that evidence becomes unreadable,
- dense figures are split or cropped rather than placed as tiny full figures,
- text, figures, captions, source labels, and takeaway bands do not overlap,
- no text visually exceeds its area,
- layout rhythm feels intentional rather than repeated from one template,
- cards, metrics, and captions have consistent spacing and alignment.

## Severity Rules

Use `high` for defects that can mislead the audience or make the deck look
broken:

- clipped scientific evidence,
- unreadable main evidence,
- overlapping text/figures,
- missing central evidence,
- fabricated or unsupported quantitative statements.

Use `medium` for defects that reduce professionalism or comprehension:

- overly dense slides,
- repeated rigid layouts,
- weak crop margins,
- figure captions detached from visuals,
- missing or unhelpful speaker notes,
- ambiguous source attribution.

Use `low` for cosmetic issues that do not affect comprehension.

## Programmatic Checks

`scripts/verify_deck_html.mjs` opens each slide in Playwright, checks page
errors, console errors, missing local media, visible body content, screenshots,
and QA report output. These checks cannot prove visual perfection, but they
reliably catch many delivery-blocking failures.

## Final Verification

After revision, inspect the screenshot set and `qa_report.md`. Do not deliver a
deck with obvious visual defects merely because the files exist. Correct high
severity issues first, then verify again.
