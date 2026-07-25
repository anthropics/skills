# Poster Build Guide: python-pptx Programmatic Approach

## Architecture of the Build Script

Structure the build script as a single Python file with helper functions and a main `build_poster()` function. This makes iteration fast — edit the script, rerun, check the render.

```python
#!/usr/bin/env python3
"""Build poster by modifying template PPTX."""

from pptx import Presentation
from pptx.util import Inches, Pt
from pptx.enum.text import PP_ALIGN
from pptx.dml.color import RGBColor
from pptx.enum.shapes import MSO_SHAPE
import os

# ============================================================
# 1. Define colors extracted from the template
# ============================================================
# Run the template analysis first, then hardcode the palette:
ACCENT = RGBColor(0x61, 0xD8, 0x4E)   # from template header
DARK = RGBColor(0x33, 0x33, 0x33)
# ... etc

# ============================================================
# 2. Helper functions
# ============================================================

def add_textbox(slide, left, top, width, height, text, size, bold, color, align):
    """Add a simple text box. Always set word_wrap=True and auto_size=None."""
    shape = slide.shapes.add_textbox(left, top, width, height)
    tf = shape.text_frame
    tf.word_wrap = True
    tf.auto_size = None  # Critical: prevents auto-shrinking
    p = tf.paragraphs[0]
    p.alignment = align
    r = p.add_run()
    r.text = text
    r.font.size = Pt(size)
    r.font.bold = bold
    r.font.color.rgb = color
    r.font.name = "Calibri"  # Match template font
    return shape, tf, p

def add_rich_textbox(slide, left, top, width, height):
    """Add an empty text box for rich text (multiple runs/paragraphs)."""
    shape = slide.shapes.add_textbox(left, top, width, height)
    tf = shape.text_frame
    tf.word_wrap = True
    tf.auto_size = None
    return shape, tf

def add_run(paragraph, text, size, bold=False, color=DARK, italic=False):
    """Add a formatted run to a paragraph."""
    r = paragraph.add_run()
    r.text = text
    r.font.size = Pt(size)
    r.font.bold = bold
    r.font.color.rgb = color
    r.font.name = "Calibri"
    r.font.italic = italic

def add_paragraph(tf, align=PP_ALIGN.LEFT, space_before=0, line_spacing=1.15):
    """Add a new paragraph to a text frame."""
    p = tf.add_paragraph()
    p.alignment = align
    p.space_before = Pt(space_before)
    p.space_after = Pt(0)
    p.line_spacing = line_spacing
    return p

def add_rect(slide, left, top, width, height, fill_color, radius=0):
    """Add a rounded rectangle with solid fill, no outline."""
    shape = slide.shapes.add_shape(
        MSO_SHAPE.ROUNDED_RECTANGLE, left, top, width, height)
    shape.fill.solid()
    shape.fill.fore_color.rgb = fill_color
    shape.line.fill.background()
    shape.adjustments[0] = radius
    return shape

def section_header(slide, left, y, width, text):
    """Add a section header with accent bar. Returns height consumed."""
    add_rect(slide, left, y, width, Inches(0.06), ACCENT)
    add_textbox(slide, left, y + Inches(0.14), width, Inches(0.45),
                text, size=28, bold=True, color=DARK, align=PP_ALIGN.LEFT)
    return Inches(0.7)

def add_bullets(slide, left, y, width, items, size=24, line_spacing=1.35):
    """Add bulleted list with **bold** markup support."""
    shape, tf = add_rich_textbox(slide, left, y, width, Inches(12))
    for i, item in enumerate(items):
        p = tf.paragraphs[0] if i == 0 else add_paragraph(tf, space_before=5, line_spacing=line_spacing)
        p.line_spacing = line_spacing
        add_run(p, "▸ ", size, bold=True, color=ACCENT)
        # Parse **bold** markers
        parts = item.split("**")
        for j, part in enumerate(parts):
            add_run(p, part, size, bold=(j % 2 == 1), color=DARK)
    return shape

def caption(slide, left, y, width, text):
    """Add a figure caption."""
    add_textbox(slide, left, y, width, Inches(0.45),
                text, size=18, bold=False, color=RGBColor(0x66,0x66,0x66),
                align=PP_ALIGN.CENTER)

# ============================================================
# 3. Main build function
# ============================================================

def build_poster():
    prs = Presentation(TEMPLATE_PATH)
    slide = prs.slides[0]

    # --- Identify shapes to keep vs remove ---
    # Keep: design elements (header bars, logos, accent shapes)
    # Remove: all content (text, figures)
    keep_indices = {1, 3, 6, 15}  # Adjust per template!
    shapes = list(slide.shapes)
    for i, shape in enumerate(shapes):
        if i not in keep_indices:
            shape._element.getparent().remove(shape._element)

    # --- Layout constants ---
    LM = Inches(0.7)         # left margin
    FULL_W = Inches(22.6)    # full content width
    GAP = Inches(0.45)       # column gap
    cw = (FULL_W - GAP) // 2 # column width

    # --- Build content, tracking Y position ---
    y = Inches(8.0)  # start of content area

    y += section_header(slide, LM, y, cw, "Section Title")
    add_bullets(slide, LM, y, cw, [
        "First point with **bold emphasis**",
        "Second point",
    ])
    y += Inches(2.5)  # Measured allocation for this content

    # ... continue building ...

    prs.save(OUTPUT_PATH)
```

## Key Patterns

### Preserving Template Design

The template defines the poster's visual identity. Always preserve:
- Header/footer background shapes (rectangles, gradients)
- Accent bars and decorative elements
- Institutional logos (may be embedded PNGs or linked SVGs)
- Color palette

Extract colors from the template programmatically:
```python
from lxml import etree
import re

shape = slide.shapes[1]  # e.g., header rectangle
xml = etree.tostring(shape._element, pretty_print=True).decode()
colors = re.findall(r'srgbClr val="([^"]+)"', xml)
print(f"Colors: {colors}")  # e.g., ['000000', '61D84E']
```

### Two-Column Layout

Most poster content uses a two-column layout. Track Y position independently for each column:

```python
c1_left = LM                  # left column x
c2_left = LM + cw + GAP       # right column x

y_left = content_start         # left column Y tracker
y_right = content_start        # right column Y tracker

# Build left column
y_left += section_header(slide, c1_left, y_left, cw, "Problem")
# ...

# Build right column
y_right += section_header(slide, c2_left, y_right, cw, "Architecture")
# ...

# Full-width elements start at the max of both columns
bottom_y = max(y_left, y_right)
```

### Adding Images

```python
slide.shapes.add_picture(
    "figures/cropped/fig1.png",
    left, top, width, height  # all in EMU or Inches()
)
```

The image is scaled to fit the given width × height. Aspect ratio is NOT preserved automatically — calculate the correct height from the image's aspect ratio:

```python
from PIL import Image
img = Image.open("figures/cropped/fig1.png")
aspect = img.height / img.width
fig_width = cw
fig_height = int(fig_width * aspect)
slide.shapes.add_picture("figures/cropped/fig1.png", left, y, fig_width, fig_height)
```

### Highlight Boxes

Use colored background rectangles behind text for emphasis:

```python
# Background rect (add BEFORE the text so it's behind)
add_rect(slide, x, y, width, height, GREEN_BG, radius=0.02)

# Text on top
add_textbox(slide, x + Inches(0.2), y + Inches(0.1),
            width - Inches(0.4), height - Inches(0.2),
            text, size=22, ...)
```

### Rich Text (Mixed Formatting)

For text with mixed bold/italic/color within a single paragraph:

```python
shape, tf = add_rich_textbox(slide, left, top, width, height)
p = tf.paragraphs[0]
p.alignment = PP_ALIGN.CENTER
add_run(p, "Core Insight: ", 30, bold=True, color=GREEN)
add_run(p, "We transform ", 30, color=DARK)
add_run(p, "regression into retrieval", 30, bold=True, color=GREEN)
```

## Font Size Guidelines for Poster Scale

These sizes work for ~24×36 inch posters. Scale proportionally for other dimensions.

| Element | Size | Notes |
|---------|------|-------|
| Title | 54-60pt | Must read from 15+ feet |
| Authors | 28-32pt | Single line if possible |
| Affiliations | 22-24pt | |
| Section headers | 28-30pt | Bold, with accent bar |
| Body/bullets | 23-25pt | Main content text |
| Captions | 18-20pt | Below figures |
| Key result numbers | 34-36pt | In highlight boxes |
| Fine print | 14-16pt | Sublabels, metadata |

**PowerPoint renders text ~15% wider than LibreOffice.** If the user opens in PowerPoint, reduce font sizes by 1-2pt or shorten text.

## Common Pitfalls

1. **auto_size must be None.** If you don't set `tf.auto_size = None`, python-pptx may auto-shrink text to fit the box, making it unreadably small.

2. **word_wrap must be True.** Without this, long text runs off the edge instead of wrapping.

3. **Don't trust calculated heights.** A 24pt bullet with bold text in an 11-inch column may wrap to 2 or 3 lines. Always render and check.

4. **Shape z-order matters.** Background rectangles must be added BEFORE the text that sits on top of them. Shapes added later render on top.

5. **Linked images (SVG logos) can't be extracted.** If a template logo is linked rather than embedded, you'll get "no embedded image" errors. Keep the original shape rather than trying to extract and re-add it.

6. **EMU math.** python-pptx uses EMUs (English Metric Units): 1 inch = 914400 EMU. Use `Inches()`, `Pt()`, `Emu()` helpers rather than raw numbers.
