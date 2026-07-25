---
name: create-academic-poster
description: "Create a professional academic research poster from a PDF paper and a PPTX template. Use this skill whenever the user wants to make a conference poster, workshop poster, or research poster from their paper — especially when they provide both a PDF of the paper and a .pptx file as a template or example. Triggers include: 'make a poster for my paper', 'create a poster from this PDF', 'conference poster', 'workshop poster', 'research poster', 'poster for NeurIPS/ICML/ICLR/CVPR/ECCV/ACL/EMNLP', or any mention of turning a paper into a poster. Also triggers when a user provides a .pptx poster file and asks to create a new poster in the same style. This skill governs the full pipeline from paper analysis through iterative visual QA."
---

# Create Academic Poster from Paper + Template

This skill turns a PDF research paper into a professional, conference-ready poster by modifying a PPTX template using `python-pptx`. The workflow is built around an iterative **build → render → inspect → fix** loop that catches overflow, overlap, and spacing issues that are invisible in code.

## When to Use This vs. Other Skills

| Situation | Use |
|-----------|-----|
| Paper PDF + PPTX template → poster | **This skill** |
| Create slides for a talk | `academic-pptx` + `pptx` |
| HTML-based poster (no PPTX template) | `pptx-posters` |
| Edit an existing PPTX | `pptx` |

## Dependencies

```bash
uv add python-pptx Pillow pymupdf   # or pip install
sudo apt-get install -y poppler-utils libreoffice-impress  # for rendering
```

## Bundled Scripts

These scripts automate the repetitive parts of poster creation. Run them directly — they handle their own imports.

| Script | Purpose | When to Use |
|--------|---------|-------------|
| `scripts/analyze_template.py` | Dump shape inventory, extract colors and logos | Phase 1: first thing after receiving the template |
| `scripts/extract_figures.py` | Render PDF pages at high DPI and crop figures | Phase 2: extract figures from the paper |
| `scripts/render_poster.py` | PPTX → PDF → high-res PNG with region crops | Phase 5: every iteration of the QA loop |
| `scripts/measure_text.py` | Measure actual rendered text heights | Phase 4/5: before setting Y allocations, or after overflow issues |

**The scripts eliminate the three biggest token sinks:**
1. Template analysis code (written once, not re-improvised each time)
2. The render pipeline (a single command instead of 15 lines of pymupdf)
3. Text height guessing (measure first, allocate with data)

---

## The Workflow

```
Phase 1: Understand  →  Phase 2: Extract  →  Phase 3: Design
    ↓                                            ↓
Phase 6: Deliver  ←  Phase 5: Iterate  ←  Phase 4: Build
                      (render → inspect
                       → fix → repeat)
```

### Phase 1: Understand Both Inputs

**Read the paper thoroughly.** Use `pymupdf` to extract text from all pages. Identify:
- The single core contribution (one sentence)
- 2-3 key innovations/methods
- The hero result (the number that makes the paper memorable)
- 3-5 key figures and tables worth including
- Author list, affiliations, venue/workshop name

**Analyze the template PPTX** using the bundled script:

```bash
python scripts/analyze_template.py template.pptx --outdir analysis/
```

This produces:
- `shapes.txt` — full shape inventory with positions, sizes, types, text content, font info, and colors
- `colors.json` — extracted color palette per shape
- `logos/` — embedded images (institutional logos)
- `template_render.png` — visual render of the template

Read `shapes.txt` to identify which shapes are **design elements to keep** (header bars, accent stripes, logos — the script suggests `keep_indices`) vs. **content to replace** (titles, authors, body text, figures). Read `template_render.png` to see the visual layout.

### Phase 2: Extract Figures from the Paper

Paper PDFs embed images at low resolution. Instead, render pages at high DPI and crop figures using the bundled script:

```bash
# Step 1: Render all pages to see where figures are
python scripts/extract_figures.py paper.pdf --render-pages --dpi 500

# Step 2: Visually inspect pages to determine crop coordinates (as 0.0-1.0 fractions)

# Step 3: Crop individual figures
python scripts/extract_figures.py paper.pdf --crop 2 0.18 0.07 0.92 0.27 --name fig1_method
python scripts/extract_figures.py paper.pdf --crop 4 0.15 0.05 0.90 0.35 --name fig2_arch

# Or batch crop from a JSON spec
python scripts/extract_figures.py paper.pdf --crop-spec figures.json
```

**Cropping rules:**
- Remove line numbers (left ~15-18% of page) from conference submissions
- Remove page headers ("Under review as..." etc.)
- Remove figure captions — you'll write poster-specific captions
- For tables: crop just the table rows and headers, not surrounding body text
- Always verify crops visually by reading the saved image files

### Phase 3: Design the Poster Layout

Plan the layout before writing any code. Academic posters follow a visual hierarchy:

**Header zone** (~15-20% of height): Title, authors, affiliations, logos, venue badge
**Content zone** (~60-70%): Two-column layout with methods, figures, results
**Footer zone** (~10-15%): Key takeaways, conclusions, QR codes

**Content selection — less is more:**
- One hero insight banner at the top of the content zone
- 3-4 key result metrics as highlight boxes
- 2-3 figures maximum (method diagram + results are essential)
- 1 results table (the most important one)
- Bullet text: short and punchy, not paper paragraphs

**What makes a poster stand out at a workshop:**
- Lead with the result, not the method — what's the takeaway from 6 feet away?
- The "core insight" banner should make the contribution unmissable
- Key result boxes with big numbers draw eyes
- The method figure tells the story; the table proves it

### Phase 4: Build with python-pptx

Read the reference guide at [references/build_guide.md](references/build_guide.md) for the full programmatic approach. The key principles:

1. **Preserve template design.** Keep header rectangles, accent bars, logos — remove only content shapes.
2. **Use the template's color palette.** Extract RGB values from the template's fills and fonts.
3. **Build incrementally.** Track Y positions for each column, advancing after each element.
4. **Never hardcode text heights.** This is the #1 source of bugs. See the text sizing section below.

### Phase 5: The Iteration Loop (Critical)

This is the most important phase. Poster text overflow is **invisible in code** — you can only catch it by rendering and inspecting. Every poster requires 3-6 iteration rounds.

#### The Loop

```
while not satisfied:
    1. Run the build script
    2. Convert PPTX → PDF via LibreOffice
    3. Render PDF → high-res PNG via pymupdf
    4. Crop and inspect specific regions
    5. Identify issues (overlaps, white space, sizing)
    6. Fix the build script
```

#### Rendering pipeline

```bash
# Build the poster
python build_poster.py

# Render + inspect in one command (produces PDF, full PNG, overview, and 6 region crops)
python scripts/render_poster.py poster.pptx --outdir figures/render
```

This produces `region_header.png`, `region_left_top.png`, `region_right_top.png`, etc. — read each one to check for overlaps. Also produces `poster.pdf` which is copied to the project root.

Always visually inspect by reading the cropped region images. Do NOT trust that text fits based on math alone.

#### Measuring text before allocating space

Before writing the build script (or after the first overflow), measure your actual bullet text:

```bash
python scripts/measure_text.py --texts texts.json --width 11.1 --template template.pptx
```

Where `texts.json` contains your bullet groups. The script creates a temporary PPTX, renders it, and measures actual pixel heights — outputting recommended Y allocations with a 15% safety margin. This eliminates the guess → overflow → fix cycle that dominated our first poster build.

#### What to look for in each round

| Issue | Symptom | Fix |
|-------|---------|-----|
| **Text overflow** | Text from one section overlaps the next section's header | Increase Y allocation or shorten text |
| **Box overflow** | Text extends past a background rectangle | Increase box height, reduce font, or shorten text |
| **Too much white space** | Large gaps between sections | Decrease Y allocation, increase figure sizes |
| **Unbalanced columns** | One column ends much lower than the other | Move content between columns |
| **Tiny figures** | Figures too small to read details | Increase figure height |
| **Cut-off elements** | Content extends past slide boundary | Reduce overall content or font sizes |

### Phase 6: Deliver

Provide both files:
- `poster.pptx` — editable in PowerPoint/Google Slides
- `poster.pdf` — rendered via LibreOffice for print/preview

Note that **LibreOffice and PowerPoint render text differently** — PowerPoint uses wider character spacing. If the user will open in PowerPoint, add a ~15% safety margin on all text allocations compared to what looks right in LibreOffice renders.

---

## The Text Sizing Problem

The single hardest part of poster creation is predicting how much vertical space text will consume. Bold text, bullet markers, and font rendering differences all cause text to wrap differently than expected.

### Why it's hard

- `python-pptx` has no text measurement API
- The same text renders at different widths in LibreOffice vs. PowerPoint vs. Google Slides
- Bold text is wider than regular text (same pt size, more pixels)
- Bullet markers ("▸ ") consume horizontal space, causing the actual text to start indented
- Line spacing compounds: 3 lines at 1.35 spacing ≈ 1.05in at 24pt, but add bold + bullets and it's ~1.25in

### Strategies

1. **Start with short bullets.** Write bullets that fit on 1-2 lines at your column width. Test, then add detail if there's room.

2. **Measure empirically.** After the first render, measure actual text heights from the rendered image and use those measurements for allocations.

3. **Trim from the end.** When a bullet overflows, remove trailing words first — "validating the design" → just "independently" still conveys the point.

4. **Safety margins.** Add 15-20% to your estimated text height. It's easier to tighten spacing than to fix overlaps.

5. **PowerPoint tax.** If the user opens in PowerPoint, every text element needs ~15% more space than LibreOffice shows. Use shorter text to compensate.

---

## Poster Design Principles

Read [references/design_principles.md](references/design_principles.md) for comprehensive guidance on:
- Visual hierarchy and font sizing for different viewing distances
- Color palette selection and contrast
- Figure annotation and layout
- Common mistakes to avoid
