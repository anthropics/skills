# Direct PptxGenJS Reference

When html2pptx doesn't give you enough control, work directly with PptxGenJS coordinates.

## When to Use Direct Control

| Situation | Use html2pptx | Use Direct PptxGenJS |
|-----------|---------------|----------------------|
| Standard text layouts | ✓ | |
| Bullet lists, tables | ✓ | |
| Precise coordinate placement | | ✓ |
| Algorithmic/calculated positions | | ✓ |
| Collision detection needed | | ✓ |
| html2pptx fighting your layout | | ✓ |

## Core Principle: Object Minimization

**Prefer fewer, richer objects over layered simple objects.**

```javascript
// ✗ WORSE - two objects, alignment can drift
slide.addShape(pptx.shapes.ROUNDED_RECTANGLE, {
  x: 1, y: 1, w: 3, h: 1,
  fill: { color: 'FFFFFF' },
  line: { color: 'F5D76E', width: 0.75 }
});
slide.addText('Quote text', { x: 1, y: 1, w: 3, h: 1 });

// ✓ BETTER - single object with all properties
slide.addText('Quote text', {
  x: 1, y: 1, w: 3, h: 1,
  fill: { color: 'FFFFFF' },
  line: { color: 'F5D76E', width: 0.75 },
  rectRadius: 0.04,  // rounded corners
  inset: 0.08        // internal padding
});
```

One object means:
- User can select/edit as a unit in PowerPoint
- No alignment drift between layers
- Cleaner XML, smaller file
- Simpler to position programmatically

When you consolidate to a single object, ensure internal properties work together (e.g., `inset` keeps text from touching the border).

## API Gotchas

### Internal Padding: Use `inset`, Not `margin`

```javascript
// ✗ WRONG - fails silently, no padding applied
slide.addText(text, { margin: 0.1 });

// ✓ CORRECT - 0.1 inches padding on all sides
slide.addText(text, { inset: 0.1 });
```

PowerPoint UI calls these "internal margins" but PptxGenJS uses `inset`.

### Text AutoFit Options

| PowerPoint Setting | PptxGenJS Property | Behavior |
|-------------------|-------------------|----------|
| Do not Autofit | (default) | Text may overflow |
| Shrink text on overflow | `shrinkText: true` | Reduces font size to fit |
| Resize shape to fit text | `autoFit: true` | Expands box to fit content |

```javascript
// Shrink text if it overflows
slide.addText(longText, { shrinkText: true, ...position });

// Expand box to fit text
slide.addText(longText, { autoFit: true, ...position });
```

### Borders on Text Boxes

Use `line` property for borders, `rectRadius` for rounded corners:

```javascript
slide.addText('Bordered text', {
  x: 1, y: 1, w: 4, h: 1,
  fill: { color: 'FFFFFF' },
  line: { color: 'C5A880', width: 1 },  // 1pt gold border
  rectRadius: 0.05,                      // rounded corners (inches)
  inset: 0.1                             // keep text off the border
});
```

## Text Dimension Estimation

To size boxes before PowerPoint's autofit, estimate text dimensions:

```javascript
// Approximate character width (Georgia font)
const charWidth = fontSize * 0.007;  // inches per character

// Estimate lines needed
const charsPerLine = Math.floor(boxWidth / charWidth);
const linesNeeded = Math.ceil(text.length / charsPerLine);

// Line height
const lineHeight = fontSize * 0.017;  // inches per line
const estimatedHeight = linesNeeded * lineHeight;
```

These are rough estimates - use `autoFit: true` or `shrinkText: true` to let PowerPoint adjust.

## Visual Validation Workflow

Coordinates don't reveal overlap or cutoff problems. Always validate visually:

```bash
# Generate thumbnail grid
python scripts/thumbnail.py output.pptx workspace/check --cols 4

# Then read and inspect the image
```

The feedback loop: **code → render → look → adjust**

For complex coordinate work, prototype in SVG first (see below).

## SVG Prototyping Pattern

For algorithmic layouts, prototype in SVG before converting to PptxGenJS:

1. **Write algorithm generating SVG** - faster iteration than regenerating .pptx
2. **Render to PNG**: `rsvg-convert -w 1280 -h 720 input.svg -o /tmp/test.png`
3. **Inspect and iterate** until layout works
4. **Port to PptxGenJS** - convert pixels to inches: `px / 96`

SVG iteration is ~10x faster than PPTX generation. Once the algorithm works, translating to PptxGenJS is mechanical.

## Example: Calculated Placement with Collision Detection

```javascript
const pptxgen = require('pptxgenjs');
const pptx = new pptxgen();

// Track placed objects for collision detection
const placed = [];

function overlaps(a, b, padding = 0.1) {
  return !(a.x + a.w + padding < b.x ||
           b.x + b.w + padding < a.x ||
           a.y + a.h + padding < b.y ||
           b.y + b.h + padding < a.y);
}

function placeBox(slide, text, preferredX, preferredY, w, h) {
  const box = { x: preferredX, y: preferredY, w, h };

  // Adjust if overlapping existing boxes
  for (const existing of placed) {
    if (overlaps(box, existing)) {
      box.y = existing.y + existing.h + 0.2;  // Move below
    }
  }

  placed.push(box);

  slide.addText(text, {
    x: box.x, y: box.y, w: box.w, h: box.h,
    fill: { color: 'FFFFFF' },
    line: { color: 'F5D76E', width: 0.75 },
    inset: 0.08,
    fontSize: 10,
    valign: 'middle'
  });
}
```
