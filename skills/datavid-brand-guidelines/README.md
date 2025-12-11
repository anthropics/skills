# Datavid Brand Guidelines Skill

A Claude skill for applying Datavid's official brand identity to any content creation task.

## Purpose

This skill provides comprehensive brand guidelines for Datavid (https://datavid.com/), including:
- Official color palettes with hex codes
- Typography specifications (Ubuntu font family)
- Logo usage guidelines
- Button and UI element styling
- Design principles and best practices

## Quick Reference

### Primary Colors
- **Pink Coral** `#FF2E5F` - Primary CTAs and attention elements
- **Dark Blue** `#0A377D` - Secondary CTAs, headings, body text
- **Happy Blue** `#46C3D7` - Tertiary CTAs, icons, subtitles

### Typography
- **Ubuntu** (Regular, Bold) - Headings and body text
- **Ubuntu Condensed** (Regular) - Buttons and UI elements

## Directory Structure

```
datavid-brand-guidelines/
├── SKILL.md              # Main skill documentation
├── LICENSE.txt           # Apache 2.0 License
├── README.md            # This file
├── assets/
│   ├── logos/           # Logo files in various formats
│   │   ├── logo-datavid-colors.svg
│   │   ├── logo-datavid.pdf
│   │   ├── logo-datavid-rgb-60.png
│   │   ├── logo-dark-bg.png
│   │   └── logo-light-bg.png
│   ├── backgrounds/     # Background graphics and patterns
│   │   └── background-swirl.png
│   └── fonts/          # Ubuntu font family
│       └── Ubuntu/     # Complete Ubuntu font set
├── reference/          # Source documentation
│   ├── Datavid-Style-guide-2023.pdf
│   └── stem-trust-signals-screenshot.pdf
```

## Usage

When creating content for Datavid, reference this skill to ensure:

1. **Color Accuracy**: Use exact hex codes from the palette
2. **Typography**: Apply Ubuntu fonts with proper hierarchy
3. **Logo Usage**: Maintain clearspace and minimum sizes
4. **Design Elements**: Follow button styles, corner treatments, and layout principles
5. **Brand Consistency**: Apply color hierarchy (Pink Coral > Dark Blue > Happy Blue)

## Assets

### Logos
- **SVG**: Vector format for web use
- **PDF**: Vector format for print
- **PNG**: Raster formats for specific backgrounds
  - `logo-dark-bg.png` - White logo for dark backgrounds
  - `logo-light-bg.png` - Dark logo for light backgrounds

### Fonts
Complete Ubuntu font family included with Regular, Bold, Light, Medium, and Italic variants, plus Ubuntu Condensed.

**Note**: Fonts are licensed under the Ubuntu Font Licence (UFL). See `assets/fonts/Ubuntu/UFL.txt` for details.

### Backgrounds
Subtle swirl pattern for creating branded background elements.

## Implementation Examples

### Web/Digital
```css
/* Primary colors */
--pink-coral: #FF2E5F;
--dark-blue: #0A377D;
--happy-blue: #46C3D7;

/* Typography */
font-family: 'Ubuntu', sans-serif;
```

### Button Hierarchy
1. Pink Coral filled - Most important actions
2. Pink Coral outline - Secondary actions
3. Dark Blue filled - Alternative primary when context has pink
4. Happy Blue - Tertiary or dark background actions

### Logo Clearspace
Always maintain 0.5x clearspace (half logo height) on all sides. Minimum print size: 25mm width.

## License

This skill is licensed under the Apache License 2.0. See [LICENSE.txt](LICENSE.txt) for details.

The Ubuntu fonts are licensed under the Ubuntu Font Licence (UFL).

## References

- Official Datavid Website: https://datavid.com/
- Ubuntu Fonts: Google Fonts (open source)
- Brand Guidelines: See `reference/Datavid-Style-guide-2023.pdf`

## Version History

- **2023**: Original style guide created
- **2025-10**: Restructured as Claude skill with proper asset organization
