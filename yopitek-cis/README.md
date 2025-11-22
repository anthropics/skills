# Yopitek Corporate Identity System (CIS)

Welcome to the Yopitek Corporate Identity System documentation. This repository contains all brand guidelines, visual identity standards, and design resources for Yopitek.

## 📁 Contents

### Core Documentation

1. **[BRAND_GUIDELINES.md](BRAND_GUIDELINES.md)** - Complete brand guidelines
   - Brand colors and color usage
   - Typography system
   - Logo guidelines
   - Visual identity elements
   - Marketing materials
   - Digital guidelines
   - Brand voice and messaging

2. **[COLOR_PALETTE.md](COLOR_PALETTE.md)** - Detailed color specifications
   - Color codes (HEX, RGB, CMYK, HSL)
   - Color accessibility guidelines
   - Product line color associations
   - CSS color variables
   - Print color specifications

3. **[QUICK_REFERENCE.md](QUICK_REFERENCE.md)** - Quick reference guide
   - Essential brand elements
   - Common use cases
   - Typography cheat sheet
   - Common mistakes to avoid

## 🎨 About Yopitek

**Yopitek** is a technology company specializing in:
- 📡 Wireless Routers
- 🎮 Graphic Cards
- 💳 NFC Card Readers

Our brand represents innovation, connectivity, and cutting-edge technology solutions.

## 🚀 Quick Start

### For Designers

1. Read the [Quick Reference Guide](QUICK_REFERENCE.md) for immediate needs
2. Review [Brand Guidelines](BRAND_GUIDELINES.md) for complete specifications
3. Check [Color Palette](COLOR_PALETTE.md) for precise color values

### For Developers

1. Use CSS color variables from [COLOR_PALETTE.md](COLOR_PALETTE.md)
2. Follow typography specifications in [BRAND_GUIDELINES.md](BRAND_GUIDELINES.md)
3. Implement UI components per digital guidelines

### For Marketing

1. Reference brand voice guidelines for messaging
2. Use approved color combinations for campaigns
3. Follow social media templates and specifications

## 🎯 Brand Essentials

### Primary Brand Color
**Tech Blue:** `#0066CC`

### Typography
- **Headings:** Inter (Bold/Semi-Bold)
- **Body Text:** Inter (Regular/Medium)
- **Technical:** JetBrains Mono

### Tagline
"Connecting Innovation"

## 📊 Product Line Visual Identity

| Product | Primary Color | Accent | Theme |
|---------|--------------|--------|-------|
| Wireless Routers | Tech Blue | Electric Cyan | Connectivity |
| Graphic Cards | Circuit Orange | Electric Cyan | Performance |
| NFC Readers | Signal Green | Tech Blue | Security |

## 📐 Key Guidelines

### Logo Usage
- Minimum size: 120px (digital) / 30mm (print)
- Clear space: Height of letter "Y"
- Never distort, rotate, or add effects

### Color Accessibility
- All primary colors meet WCAG AA standards
- Deep Navy + White: AAA compliant (13.5:1)
- Tech Blue + White: AA compliant (5.9:1)

### Typography Scale
```
H1: 48pt | H2: 36pt | H3: 28pt
Body: 16pt | Small: 14pt
```

## 🛠️ Implementation

### CSS Variables
```css
:root {
  --yopitek-tech-blue: #0066CC;
  --yopitek-deep-navy: #1A2332;
  --yopitek-electric-cyan: #00D4FF;
  --yopitek-signal-green: #00E676;
  --yopitek-circuit-orange: #FF6B35;
}
```

### Font Stack
```css
/* Headings */
font-family: 'Inter', Arial, Helvetica, sans-serif;
font-weight: 600 | 700;

/* Body */
font-family: 'Inter', Arial, Helvetica, sans-serif;
font-weight: 400 | 500;

/* Technical */
font-family: 'JetBrains Mono', 'Courier New', monospace;
```

## 📦 Brand Asset Organization

```
/brand-assets
  /logos
    /primary
    /monochrome
    /icon
  /colors
    /swatches
  /fonts
    /inter
    /jetbrains-mono
  /patterns
  /photography
  /templates
```

## ✅ Checklist for Brand Compliance

- [ ] Using approved color palette
- [ ] Following typography guidelines
- [ ] Logo sized correctly with clear space
- [ ] Text meets accessibility contrast ratios
- [ ] Maintaining consistent brand voice
- [ ] Using approved imagery style

## 🤝 Contributing

When proposing changes to brand guidelines:

1. Document the rationale for changes
2. Provide visual examples
3. Ensure accessibility compliance
4. Get approval from brand custodian

## 📧 Contact

**Brand Guidelines Custodian:** Marketing Team
**Email:** brand@yopitek.com
**Questions:** See "Contact & Questions" section in BRAND_GUIDELINES.md

## 📄 License

This Corporate Identity System is proprietary and confidential. Use of these guidelines is restricted to authorized Yopitek personnel and approved partners.

---

**© 2025 Yopitek. All rights reserved.**

*Last Updated: November 22, 2025*
*Version: 1.0*
