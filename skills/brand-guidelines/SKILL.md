---
name: brand-guidelines
description: Applies Anthropic's official brand colors and typography to any sort of artifact that may benefit from having Anthropic's look-and-feel. Use it when brand colors or style guidelines, visual formatting, or company design standards apply.
license: Complete terms in LICENSE.txt
---

# Anthropic Brand Styling

## Overview

Use this skill as a reference for applying Anthropic's official brand identity, colors, and typography. These are styling instructions only; this skill does not bundle scripts, fonts, or automated formatting.

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

## Styling Guidelines

### Font Selection

- Use Poppins for headings (24pt and larger)
- Use Lora for body text
- Fall back to Arial (headings) and Georgia (body) when Poppins or Lora are unavailable to preserve readability across systems

### Text Styling

- Headings (24pt+): Poppins font (Arial fallback)
- Body text: Lora font (Georgia fallback)
- Choose Dark (`#141413`) text on light backgrounds and Light (`#faf9f5`) text on dark backgrounds for contrast
- Maintain clear text hierarchy and formatting

### Shape and Accent Colors

- Use accent colors for non-text shapes
- Cycle through orange (`#d97757`), blue (`#6a9bcc`), and green (`#788c5d`) accents to maintain visual interest while staying on-brand

## Technical Details

### Font Management

- Use system-installed Poppins and Lora fonts when available
- Fall back to Arial (headings) and Georgia (body) when Poppins or Lora are unavailable
- Pre-install Poppins and Lora in your environment for best results; if they are not installed, use the system fallback fonts above

### Color Application

- Use the exact hex color values above (or their equivalent RGB values where a tool or format requires RGB) for precise brand matching
- Keep color values consistent across different systems and output formats
