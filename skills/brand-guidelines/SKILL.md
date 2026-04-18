---
name: brand-guidelines
description: Applies Anthropic's official brand colors and typography to any sort of artifact that may benefit from having Anthropic's look-and-feel. Use it when brand colors or style guidelines, visual formatting, or company design standards apply.
license: Complete terms in LICENSE.txt
---

# Anthropic Brand Styling

## Overview

To access Anthropic's official brand identity and style resources, use this skill.

**Keywords**: branding, corporate identity, visual identity, post-processing, styling, brand colors, typography, Anthropic brand, visual formatting, visual design

## Brand Guidelines

### Colors

**Main Colors:**

- Dark: `#141413` - Primary text and dark backgrounds
- Light: `#faf9f5` - Light backgrounds and text on dark
- Mid Gray: `#b0aea5` - Secondary elements
- Light Gray: `#e8e6dc` - Subtle backgrounds

**Accent Colors:**

- Orange: `#d97757` - Primary accent
- Blue: `#6a9bcc` - Secondary accent
- Green: `#788c5d` - Tertiary accent

### Typography

- **Headings**: Poppins (with Arial fallback)
- **Body Text**: Lora (with Georgia fallback)
- **Note**: Fonts should be pre-installed in your environment for best results

## Features

### Smart Font Application

- Applies Poppins font to headings (24pt and larger)
- Applies Lora font to body text
- Automatically falls back to Arial/Georgia if custom fonts unavailable
- Preserves readability across all systems

### Text Styling

- Headings (24pt+): Poppins font
- Body text: Lora font
- Smart color selection based on background
- Preserves text hierarchy and formatting

### Shape and Accent Colors

- Non-text shapes use accent colors
- Cycles through orange, blue, and green accents
- Maintains visual interest while staying on-brand

## Technical Details

### Font Management

- Uses system-installed Poppins and Lora fonts when available
- Provides automatic fallback to Arial (headings) and Georgia (body)
- No font installation required - works with existing system fonts
- For best results, pre-install Poppins and Lora fonts in your environment

### Color Application

- Uses RGB color values for precise brand matching
- Applied via python-pptx's RGBColor class
- Maintains color fidelity across different systems

## Implementation Guide

### HTML/CSS Usage

```html
<!-- Applying brand colors in HTML -->
<style>
  body { background-color: #faf9f5; color: #141413; }
  h1, h2, h3 { font-family: Poppins, Arial, sans-serif; }
  p, body { font-family: Lora, Georgia, serif; }
  
  /* Accent color usage */
  .accent-orange { color: #d97757; }
  .accent-blue { color: #6a9bcc; }
  .accent-green { color: #788c5d; }
  
  /* Dark background variant */
  .dark-bg { background-color: #141413; color: #faf9f5; }
  
  /* Mid gray for secondary elements */
  .secondary { color: #b0aea5; }
  .subtle-bg { background-color: #e8e6dc; }
</style>
```

### Python Usage (python-pptx)

```python
from pptx.util import Pt
from pptx.dml.color import RGBColor

# Brand colors as RGBColor objects
BRAND_DARK = RGBColor(0x14, 0x14, 0x13)      # #141413
BRAND_LIGHT = RGBColor(0xfa, 0xf9, 0xf5)     # #faf9f5
BRAND_MID_GRAY = RGBColor(0xb0, 0xae, 0xa5)  # #b0aea5
BRAND_ORANGE = RGBColor(0xd9, 0x77, 0x57)    # #d97757
BRAND_BLUE = RGBColor(0x6a, 0x9b, 0xcc)      # #6a9bcc
BRAND_GREEN = RGBColor(0x78, 0x8c, 0x5d)     # #788c5d
```

### Accent Color Usage Table

| Color | Hex | Use Case | Pairing |
|-------|-----|----------|---------|
| Orange | `#d97757` | Primary accent, CTAs, highlights | Dark or Light bg |
| Blue | `#6a9bcc` | Secondary accent, links, info | Light bg |
| Green | `#788c5d` | Tertiary accent, success states | Light bg |

### Accessibility Contrast Ratios

For WCAG 2.1 AA compliance (minimum 4.5:1 for body text):

| Combination | Ratio | WCAG Level |
|-------------|-------|-----------|
| `#141413` on `#faf9f5` | 17.7:1 | AAA |
| `#faf9f5` on `#141413` | 17.7:1 | AAA |
| `#d97757` on `#faf9f5` | 3.1:1 | Fail (use for decorative only) |
| `#b0aea5` on `#141413` | 7.3:1 | AA |
| `#788c5d` on `#faf9f5` | 4.6:1 | AA |

**Recommendation**: Always use `#141413` on `#faf9f5` for body text to ensure AAA compliance.

### Font Fallback Chains

**Headings** (Poppins → Arial → sans-serif):
```
Poppins, Arial, Helvetica, sans-serif
```

**Body Text** (Lora → Georgia → serif):
```
Lora, Georgia, "Times New Roman", serif
```

### Dark Mode Guidance

When applying brand styling in dark contexts:
- Use `#faf9f5` as text color on dark backgrounds
- Use `#e8e6dc` for subtle backgrounds in dark mode
- Avoid pure black (`#000000`); use `#141413` for softer contrast
- Test all accent color combinations for sufficient contrast in both light and dark modes
