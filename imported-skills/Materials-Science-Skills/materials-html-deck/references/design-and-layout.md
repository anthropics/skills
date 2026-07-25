# Design and layout

Open this reference when planning visual rhythm, writing slide content, or rendering the HTML academic deck. It holds the full composition, layout, typography, and anti-template rules.

## Plan the visual rhythm before authoring

Before creating slides, assign each slide a visual role and avoid repeating the same role too often. Use a rhythm such as: opener / conceptual claim, problem setup, mechanism or workflow, evidence slide, evidence slide with cropped subpanel, comparison or ablation, boundary / limitation, synthesis / discussion.

For each slide, choose one of these composition types:

- `figure-dominant`: figure owns most of the slide; text is a quiet margin note or bottom strip,
- `process-wide`: full-width workflow with small stage labels,
- `claim-led`: one strong sentence with 2-3 supporting fragments, no fake cards,
- `comparison`: table/chart or two evidence blocks with a single conclusion line,
- `discussion`: open layout with a few sharp prompts, not a dense bullet page.

Do not create the whole deck from one generic layout family. If the plan shows repeated `three cards + takeaway` or `figure left + rail right` slides, revise the plan before building.

## On-slide text budget

Write for the slide, not for the manuscript. Most explanation belongs in speaker notes. Use these default limits unless a user-provided template clearly supports more:

- title: one line preferred; two lines allowed only when the slide still has enough vertical space,
- normal slide: 2-3 bullets, each no more than about 18 Chinese characters or 8-10 English words,
- result slide: 1 short interpretation sentence plus at most 2 compact callouts,
- card body: 1 sentence, usually no more than 24 Chinese characters,
- metric label: 1 line whenever possible,
- source label: small and short; do not let source text compete with the figure.

If the point needs more words, split the slide or move the explanation to speaker notes. Do not rely on shrinking text below readable size to make an overfull slide work.

## Evidence hierarchy on a slide

For any result slide, order the visual logic: 1) hero figure or main table crop, 2) narrow interpretation rail or short annotation band, 3) only the minimum labels needed to read the evidence, 4) any deeper explanation moves to speaker notes or the next slide. Do not let the interpretation block become as large or louder than the evidence itself.

## Layout adaptation rule

Do not default to a fixed 50/50 left-right split. Choose the layout from the figure's aspect ratio, density, and role:

- full-width or near-full-width visual when the figure is wide, complex, or the main evidence,
- tall image with a narrow text rail when the figure is vertical or the caption is short,
- top/bottom stack when the figure needs horizontal room or the slide benefits from a short argument above and a visual below,
- asymmetric split such as 70/30, 75/25, or 65/35 when one side dominates,
- compact visual-plus-callout layout when the slide needs only a few annotations,
- a table or figure crop instead of shrinking a dense graphic into a small frame.

Treat equal-weight 1:1 layouts as the exception. In most result slides, one side should clearly dominate. Prefer the smallest text block that still makes the claim legible. For dense figures, crop to the most relevant panels; for sparse slides, do not pad with extra boxes.

## Anti-template design rule

Avoid layouts that look like generic AI-generated slides. Academic restraint does not mean mechanical repetition. Do not overuse: three equal cards with icon/number strips; rows of identical metric pills; the same right-hand interpretation rail on every figure slide; nested rectangles and fake dashboard cards; evenly spaced boxes that ignore the shape of the evidence; generic "problem / solution / impact" grids when the argument has a more specific structure.

Instead, vary the composition based on the evidence: let one figure own the page when it is the evidence; use a single large quote-like claim line only when the slide is conceptual; use small edge annotations or a narrow marginal note instead of big explanatory boxes; use full-width process diagrams for workflows; split a dense figure across two slides instead of adding a crowded rail; place summary text as a quiet bottom strip when the figure is dominant.

Before finalizing, scan the deck at slide-sorter scale. If five or more slides share the same composition, redesign at least some of them so the deck has a natural rhythm.

## Slide archetype defaults

Use these defaults unless the source strongly suggests otherwise:

- Cover slide: one dominant visual or typographic idea, no balanced split, no dashboard-like grid.
- Background/problem slide: short setup text plus one compact context visual or schematic.
- Workflow/method slide: full-width or top-to-bottom process diagram, not two equal text/figure columns.
- Result/evidence slide: one dominant figure or table crop with a narrow interpretation rail; avoid 1:1 layouts unless evidence and explanation truly balance.
- Comparison/table slide: full-width table or split table across slides if it becomes cramped.
- Model/summary slide: a large central model with a brief takeaway strip or short annotation band.
- Conclusion/discussion slide: text-led but open composition, with 2-4 bullets and no unnecessary containers.

## Title writing rule

Use conclusion-style titles whenever possible. A good title states the slide's point, not just its topic. Prefer "水性环氧树脂提升乳化沥青粘结强度" over labels like "Figure 3" or "Results".

## Visual density rule

Do not downscale a dense figure, table, or multi-panel graphic into a tiny slot just to preserve symmetry. If a visual cannot be read at presentation scale, crop it, split it, or give it its own slide. Prefer one legible visual over several cramped ones.

## Text-fitting implementation rules

When authoring browser-native HTML deck slides:

- Treat automatic text shrinking as a last resort, not the layout strategy. It can fail silently, behave differently across platforms, or make text too small.
- Prefer writing shorter text, increasing the text box, or splitting the slide.
- Use explicit line breaks for known long phrases, model names, and metric labels.
- Keep text box margins conservative; avoid tiny text boxes with long Chinese-English mixed strings.
- If using responsive fitting, still verify the rendered size in Playwright screenshots and document the fallback.
- Never accept a slide where text is expected to overflow, be clipped, or require manual resizing by the user.

## Style rules

Use a restrained academic presentation design: clean white or very light background; dark readable text; one or two muted accent colors; compact but not crowded layouts; figure-first result slides; concise captions; no decorative stock images; no decorative gradients; no exaggerated marketing-style section pages.

Use Chinese suitable for oral academic reporting: avoid rigid translation; avoid long paragraphs; avoid jargon stacking; preserve technical terms where Chinese translation would reduce precision; prefer evidence-based interpretation over vague praise.

Treat each slide like a publication figure page: one dominant idea, one clear evidence hierarchy, and asymmetry when the story needs it.

### Academic page composition

- Prefer one hero visual per slide when the evidence is complex or the claim is central.
- Use asymmetric layouts by default when the visual and the text are not equally important.
- Keep gutters real and tight. Use whitespace to separate roles, not to make a balanced grid.
- Use small panel labels (`a`, `b`, `c`) when a slide contains multiple visual subpanels.
- Use direct labels or a shared legend strip when categories repeat across panels.
- Reuse one restrained palette across the slide or slide family; reserve green/red for gains, drops, or directional change.
- If a slide has a schematic and data, let one dominate and the other validate.
- Use dark backgrounds only when the dominant visual is an image plate or benefits from it; keep normal chart slides light.
- Avoid decorative boxes, fake cards, and symmetrical two-column scaffolds unless the content truly calls for them.
- If a figure would become unreadable when scaled down, crop it, split it, or move it to its own slide.

### Typography system

- Build a clear three-level hierarchy: title, body, caption/source. Do not let every text block look like the same font at slightly different sizes.
- Use one Chinese sans-serif family for most copy and one English/number companion font for metrics, abbreviations, model names, DOI, and small metadata.
- Prefer title sizes roughly in the 24-32 pt range, body copy in the 12-16 pt range, and source/caption text in the 7-9 pt range unless the template clearly calls for something else.
- Let titles carry more weight than bullets. Large metrics may stand out but must not overpower the slide title or main figure.
- Keep captions and source labels lighter in color and smaller in size than the main argument text.
- Avoid mixing many font families on one slide. One Chinese family plus one English/numeric companion is the default maximum.

### Figure-text coordination

- Do not let figures look pasted onto the page. Pair them with a clear shared field: a tight frame, a caption edge, an interpretation rail, or a short takeaway strip.
- When a slide has one dominant figure, let the figure own about 55-75% of the slide area and keep explanatory text to a narrow rail or short band.
- Keep captions attached to the figure edge or inside a bottom caption band. Avoid detached caption text floating far from the visual.
- Use 1-3 metric callouts or a short interpretation strip to help read the figure; do not surround the figure with many equal-weight boxes.
- If the source figure is very dense, prefer a cropped hero panel plus one or two callouts over shrinking the entire figure and compensating with long bullets.
- Use text to guide the reading order and interpretation of the figure, not to repeat every panel label in prose.

### Page fullness rule

- Slides should feel complete rather than empty. Most slides should have a stable top anchor, a dominant middle block, and a bottom anchor such as a takeaway strip, source strip, or conclusion line.
- Add fullness through evidence-supporting elements: metric chips, compact interpretation bands, short source strips, or a narrow comparison block.
- Avoid large unstructured blank areas caused by tiny figures, short bullets marooned in one corner, or captions far from the visual.
- If a slide still feels sparse after placing the main claim and figure, add one concise support layer before adding more bullets.
- Do not fill space with decoration alone. Any added block should clarify hierarchy, guide reading order, or improve figure readability.

### Slide archetype recipes

- Hero figure result slide: 60-75% visual area, 20-30% interpretation rail, and a short takeaway band.
- Workflow slide: one full-width or near-full-width process visual plus a compact annotation strip, not two equal columns.
- Comparison slide: one chart or table block plus a slim metric or conclusion rail; split into two slides if the table becomes cramped.
- Text-led synthesis slide: 2-4 strong bullets or 3 compact claim cards, plus one summary sentence or discussion strip at the bottom.
- Cover slide: one dominant visual or typographic block, a small metadata band, and no dashboard-like grid of equally weighted mini-elements.
