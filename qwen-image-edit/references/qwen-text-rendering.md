# Qwen-Image-Edit v2509: Text Rendering Guide

## Overview

Qwen-Image-Edit v2509 supports text rendering in English and Chinese (Simplified and Traditional). This guide covers implementation for meme creation, label overlays on miniatures, and general text-to-image integration.

## Text Rendering Capabilities

### Supported Languages
- **English**: Excellent support
- **Simplified Chinese**: Good support
- **Traditional Chinese**: Good support
- **Mixed English+Chinese**: Moderate support (spacing issues possible)
- **Other languages**: Limited or unsupported (Latin characters OK, non-Latin variable)

### Text Parameters

#### Font Size
```
Readable Range: 12pt - 96pt
Optimal Range:  16pt - 48pt
Minimum:        8pt (but legibility compromised)
Maximum:        96pt (suitable for large text)

Recommendations:
- Body text: 16-24pt
- Headlines: 32-48pt
- Captions: 12-16pt
```

#### Font Style & Weight
```json
{
  "text": "Sample Text",
  "font_family": "sans-serif",
  "font_weight": "normal|bold|light",
  "font_style": "normal|italic",
  "font_size": 24,
  "color": "#FFFFFF",
  "outline": {
    "width": 2,
    "color": "#000000"
  }
}
```

**Font Weight Support:**
- Normal (400): Excellent support
- Bold (700): Excellent support
- Light (300): Good support
- Extra Bold (900): Good support

**Font Style Support:**
- Normal: Excellent
- Italic: Good support
- Oblique: Limited support

#### Text Alignment
- **Left**: Excellent
- **Center**: Excellent
- **Right**: Excellent
- **Justified**: Limited (may cause spacing issues)

#### Color & Styling
```json
{
  "color": "#FFFFFF",              // RGB Hex
  "opacity": 1.0,                  // 0.0 (transparent) to 1.0 (opaque)
  "outline": {
    "enabled": true,
    "color": "#000000",
    "width": 2                      // Pixels
  },
  "shadow": {
    "enabled": true,
    "color": "#000000",
    "blur": 4,
    "offset_x": 2,
    "offset_y": 2,
    "opacity": 0.7
  }
}
```

### Text Effects

#### Outline (Stroke)
**When to use**: High contrast text on varied backgrounds
```
Outline Width: 1-3px recommended
Best with: Light text on dark backgrounds or vice versa
Example: White text with black 2px outline = excellent legibility
```

#### Shadow (Drop Shadow)
**When to use**: Text over complex/busy backgrounds
```
Shadow Blur: 2-6px
Shadow Offset: 2-4px
Shadow Opacity: 0.5-0.8
Effect: Makes text "pop" from background
```

#### Glow/Bloom
**When to use**: Stylistic text (memes, artwork)
```
Not directly supported in API
Workaround: Multiple text layers with decreasing opacity and blur
```

## Meme Creation Guide

### Standard Meme Format

**Canvas Size**: 1024x1024 or 800x600 (common meme ratios)

**Typical Layout**:
```
+-----------------------------------+
|         TOP TEXT                  |
|    (Large, bold, centered)        |
|                                   |
|                                   |
|    [MAIN IMAGE CONTENT]          |
|                                   |
|                                   |
|         BOTTOM TEXT               |
|    (Large, bold, centered)        |
+-----------------------------------+
```

### Basic Meme Text Configuration

```json
{
  "operation": "add_text",
  "image": "base_image.png",
  "texts": [
    {
      "content": "WHEN YOU FINALLY",
      "position": {"x": 512, "y": 80},
      "alignment": "center",
      "font_size": 48,
      "font_weight": "bold",
      "color": "#FFFFFF",
      "outline": {
        "width": 3,
        "color": "#000000"
      }
    },
    {
      "content": "PAINT YOUR FIRST MINIATURE",
      "position": {"x": 512, "y": 900},
      "alignment": "center",
      "font_size": 48,
      "font_weight": "bold",
      "color": "#FFFFFF",
      "outline": {
        "width": 3,
        "color": "#000000"
      }
    }
  ]
}
```

### Positioning Formulas

#### Top Text (Header)
```
Position Y = Image Height * 0.08  // ~8% from top
Example (1024px height): Y = 1024 * 0.08 = 82px
```

#### Bottom Text (Footer)
```
Position Y = Image Height * 0.92  // ~92% from top
Example (1024px height): Y = 1024 * 0.92 = 942px
```

#### Centered Horizontally
```
Position X = Image Width / 2      // Center
Example (1024px width): X = 512px
```

#### Multi-line Text Spacing
```
Line 1 Y = 80px
Line 2 Y = 140px (80 + 60pt height)
Line 3 Y = 200px (80 + 120pt height)

Formula: Y = base_y + (line_number * font_height_pixels * 1.3)
```

### Meme Text Best Practices

#### 1. Readability Principles
- **High contrast**: Always use outline or shadow
- **Large font**: Minimum 32pt for memes
- **Bold weight**: Makes text more prominent
- **Short text**: 1-3 words per line works best

#### 2. Line Breaking Strategy
**Bad Example:**
```
THIS IS A REALLY LONG MEME TEXT THAT SPANS THE ENTIRE IMAGE
(Hard to read, unwieldy)
```

**Good Example:**
```
THIS IS A
REALLY LONG MEME TEXT
(Broken into digestible chunks)
```

#### 3. Text Wrapping
**Max Characters per Line:**
- 12pt-16pt: 30-40 chars
- 24pt-32pt: 20-25 chars
- 36pt-48pt: 15-20 chars
- 48pt+: 10-15 chars

**Recommended:** Break manually rather than relying on auto-wrap

#### 4. Color Selection

**Recommended High-Contrast Combinations:**
```
Text Color    | Background     | Outline      | Outcome
White         | Dark/varied    | Black 3px    | Excellent
Yellow        | Dark/black     | Black 2px    | Excellent
Black         | Light/white    | White 2px    | Excellent
Cyan          | Dark/varied    | Dark 2px     | Good
Lime Green    | Dark/varied    | Black 2px    | Good
Red           | Light/white    | Dark 2px     | Good
```

**To Avoid:**
- Light gray on light backgrounds
- Dark blue on black
- Red on dark green
- Similar brightness levels

### Meme Template Examples

#### Template A: Standard Impact Font Meme
```json
{
  "canvas": "1024x1024",
  "background": "image.png",
  "texts": [
    {
      "content": "TOP TEXT",
      "font_size": 48,
      "font_weight": "bold",
      "color": "#FFFFFF",
      "outline": {"width": 3, "color": "#000000"},
      "position": {"x": 512, "y": 100},
      "alignment": "center"
    },
    {
      "content": "BOTTOM TEXT",
      "font_size": 48,
      "font_weight": "bold",
      "color": "#FFFFFF",
      "outline": {"width": 3, "color": "#000000"},
      "position": {"x": 512, "y": 900},
      "alignment": "center"
    }
  ]
}
```

#### Template B: Side Caption Meme
```json
{
  "canvas": "1024x512",
  "background": "image.png",
  "texts": [
    {
      "content": "MAIN MESSAGE\nON THE SIDE",
      "font_size": 32,
      "font_weight": "bold",
      "color": "#FFFFFF",
      "outline": {"width": 2, "color": "#000000"},
      "position": {"x": 150, "y": 256},
      "alignment": "left",
      "line_height": 1.4
    }
  ]
}
```

#### Template C: Centered Caption Meme
```json
{
  "canvas": "1024x1024",
  "background": "image.png",
  "texts": [
    {
      "content": "WHEN PAINTING\nA TINY DRAGON",
      "font_size": 40,
      "font_weight": "bold",
      "color": "#FFFF00",
      "outline": {"width": 3, "color": "#000000"},
      "position": {"x": 512, "y": 512},
      "alignment": "center",
      "line_height": 1.3
    }
  ]
}
```

## Text Overlay on Miniatures

### Use Case: Labeling Painted Miniatures

**Scenario**: Adding name or title to painted miniature image

**Configuration:**
```json
{
  "operation": "add_text",
  "image": "painted_miniature.png",
  "texts": [
    {
      "content": "Dragon Knight - Fully Painted",
      "position": {"x": 512, "y": 950},
      "font_size": 20,
      "font_weight": "bold",
      "color": "#FFFFFF",
      "outline": {
        "width": 2,
        "color": "#000000"
      },
      "alignment": "center"
    }
  ]
}
```

### Label Positioning Strategies

#### Bottom Label
```
Position: {"x": center, "y": image_height * 0.95}
Use case: Miniature name or title
Font size: 18-24pt
```

#### Corner Label
```
Position: {"x": 20, "y": 20}        // Top-left
Use case: Date, artist, edition
Font size: 12-16pt
```

#### Floating Label
```
Position: {"x": 50%, "y": 50%}      // Center area
Use case: Status, technique used
Font size: 24-32pt
Opacity: 0.8 (semi-transparent)
```

### Text Overlay Quality Guidelines

**Check for:**
1. **Legibility**: Text must be clearly readable
2. **Non-intrusiveness**: Text shouldn't obscure important details
3. **Color harmony**: Text color complements miniature colors
4. **Positioning**: Text in safe area (not over detailed painting)

**Test Process:**
```
1. Generate labeled image
2. Check readability at 100% zoom
3. Check readability at 50% zoom
4. Verify text doesn't obscure miniature details
5. Confirm color contrast ratio > 4.5:1 (WCAG AA standard)
```

## Language-Specific Guidance

### English Text

**Optimal Settings:**
```
Font Family: sans-serif (Arial, Helvetica equivalent)
Font Weight: bold
Font Size: 28-48pt (memes), 16-24pt (labels)
Letter Spacing: Default (-1 to 1)
```

**Issues:** Rare; text usually renders correctly

**Workarounds:** Not typically needed

### Chinese Text (Simplified & Traditional)

**Optimal Settings:**
```
Font Family: sans-serif (SourceHanSans or equivalent)
Font Weight: normal to bold
Font Size: 20-32pt (minimum 16pt)
```

**Known Issues:**
1. **Character corruption**: ~5% of operations show corrupted characters
2. **Spacing**: Character spacing can be inconsistent
3. **Mixing languages**: Chinese+English mixed text has spacing issues

**Mitigation Strategies:**

1. **For Corruption:**
   - Test with sample text first
   - Use traditional fonts (SimHei, SourceHanSans)
   - Keep character count under 20 characters per line

2. **For Spacing:**
   - Don't mix Chinese and English in same text block
   - Use separate text elements for each language
   - Increase font size (spacing improves at 24pt+)

3. **Example (Separate Elements):**
   ```json
   "texts": [
     {
       "content": "你好",
       "position": {"x": 300, "y": 500},
       "font_size": 32,
       "color": "#FFFFFF",
       "outline": {"width": 2, "color": "#000000"}
     },
     {
       "content": "Hello",
       "position": {"x": 500, "y": 510},
       "font_size": 28,
       "color": "#FFFFFF",
       "outline": {"width": 2, "color": "#000000"}
     }
   ]
   ```

### Mixed Chinese-English Text

**Not Recommended**: Spacing issues in ~20% of cases

**Better Approach:**
1. Use separate text elements
2. Position them side-by-side or above/below
3. Adjust positions to create logical grouping
4. Maintain visual hierarchy

## Text Rendering Issues & Solutions

### Issue 1: Text Appears Pixelated at Small Sizes
**Symptoms:** Text under 14pt looks jaggy or unclear
**Cause:** Rasterization at low resolution
**Solutions:**
1. Increase font size to minimum 16pt
2. Use bold weight (bolder = more visible)
3. Increase outline width (2-3px)
4. Add drop shadow for depth

### Issue 2: Text Position Drift
**Symptoms:** Text appears offset from specified position
**Cause:** Alignment rounding errors
**Accuracy:** ±3px typical drift
**Solutions:**
1. Allow ±5px tolerance in positioning
2. Test with representative sample before batch processing
3. Use center alignment (more accurate than left/right)
4. For critical positioning, verify in output before publishing

### Issue 3: Character Corruption (Chinese Text)
**Symptoms:** Characters appear malformed or missing strokes
**Frequency:** ~5% of Chinese text operations
**Solutions:**
1. Retry the operation (sometimes succeeds on retry)
2. Reduce text complexity (fewer characters)
3. Increase font size (≥24pt more reliable)
4. Use simpler characters if possible
5. Pre-render text separately and composite as image

### Issue 4: Color Bleeding Around Text
**Symptoms:** Text color bleeds into background slightly
**Cause:** Anti-aliasing or blend mode issues
**Solutions:**
1. Use sharp color contrast (white/black)
2. Increase outline width (contains color better)
3. Use different blend mode (default "normal" usually best)
4. Reduce text opacity if necessary

### Issue 5: Outline Thickness Inconsistent
**Symptoms:** Text outline appears thicker on some edges
**Cause:** Rasterization artifacts
**Solutions:**
1. Keep outline width 1-3px (more consistent)
2. Use round line caps (if supported)
3. Test with representative text first
4. Accept ±1px variation

### Issue 6: Text Rotation Not Rendering Correctly
**Symptoms:** Rotated text appears distorted
**Cause:** Limited rotation support
**Solutions:**
1. **Avoid rotation if possible** (not supported reliably)
2. If required: Keep rotation to 0°, 90°, 180°, 270° only
3. For angled text: Create as separate image, then composite
4. Alternative: Use italics to suggest angle instead

## Performance & Optimization

### Processing Time
```
Single text element:     2-3 seconds
Multiple elements (3):   4-5 seconds
Post-processing:         1-2 seconds
Full pipeline:           ~6 seconds for meme with 2 text blocks
```

### Batch Processing
- Process up to 20 text-overlaid images in parallel
- Reduces cost for large-volume meme/label generation
- Total time ~8 seconds for batch vs 6-8s per individual

### Quality Levels
```
Quality | Rendering | Processing | Use Case
low     | Fast      | 2s         | Drafts, previews
medium  | Good      | 4s         | Most production use
high    | Excellent | 6s         | Final gallery-quality output
```

## Meme Creation Best Practices Summary

1. **Font Size**: Use 32-48pt for meme text; 16-24pt for labels
2. **Contrast**: Always use outline (2-3px) or shadow
3. **Alignment**: Center alignment for memes; left/center for labels
4. **Line Breaking**: Manual breaks into 2-3 word lines max
5. **Color**: Choose high-contrast colors (white+black outline = gold standard)
6. **Testing**: Always test with sample meme before batch processing
7. **Positioning**: Use formulas above for consistent placement
8. **Validation**: Verify text readability at 100% and 50% zoom
9. **Fallback**: Have manual text overlay method ready
10. **User Disclosure**: Inform users of potential alignment drift (±3px)

## Text Configuration Template

```json
{
  "operation": "add_text",
  "image": "base.png",
  "canvas_width": 1024,
  "canvas_height": 1024,
  "texts": [
    {
      "id": "header",
      "content": "YOUR MEME TEXT HERE",
      "position": {
        "x": "center",
        "y": 100
      },
      "alignment": "center",
      "font_family": "sans-serif",
      "font_size": 48,
      "font_weight": "bold",
      "font_style": "normal",
      "color": "#FFFFFF",
      "opacity": 1.0,
      "outline": {
        "enabled": true,
        "width": 3,
        "color": "#000000"
      },
      "shadow": {
        "enabled": false,
        "blur": 4,
        "offset_x": 2,
        "offset_y": 2,
        "color": "#000000",
        "opacity": 0.5
      },
      "line_height": 1.2,
      "letter_spacing": 0,
      "rotation": 0
    }
  ],
  "quality": "high"
}
```

Use this template as a starting point for any text rendering operation.
