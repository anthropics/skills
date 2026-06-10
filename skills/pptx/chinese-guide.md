# 中文 PPT 制作指南

This guide extends the main PPTX skill with Chinese-specific recommendations for creating professional Chinese presentations.

## 中文字体 (Chinese Fonts)

### Recommended Fonts

| Use Case | Windows | macOS | Fallback |
|----------|---------|-------|----------|
| Headings | Microsoft YaHei Bold | PingFang SC Bold | Arial Bold |
| Body Text | Microsoft YaHei | PingFang SC Regular | Arial |
| Numbers/English | Arial, Calibri | Helvetica | - |

**Important**: Always specify Chinese fonts explicitly in pptxgenjs:

```javascript
slide.addText("中文文字", {
  fontFace: "Microsoft YaHei"  // Must specify!
});
```

##Font Sizing for Chinese

Chinese characters appear smaller than English at the same point size. Recommended adjustments:

| Element | English | Chinese | Adjustment |
|---------|---------|---------|------------|
| Slide Title | 36pt | 38-40pt | +2-4pt |
| Section Header | 20pt | 22-24pt | +2-4pt |
| Body Text | 14pt | 15-16pt | +1-2pt |
| Large Display | 60pt | 56pt | OK as-is |

## Line Spacing

Chinese text requires more generous line spacing:

```javascript
slide.addText("多行中文文本", {
  lineSpacing: 18-20,  // vs. 14-16 for English
  fontFace: "Microsoft YaHei"
});
```

## Color Schemes for Chinese Audiences

Theme-specific palettes that resonate with Chinese cultural preferences:

### Business & Finance (商务金融)
```javascript
const colors = {
  primary: "1E2761",    // Deep blue - trust
  secondary: "CADCFC",  // Light blue
  accent: "B8860B"      // Gold - prosperity
};
```

### Health & Wellness (健康医疗)
```javascript
const colors = {
  primary: "028090",    // Teal - health
  secondary: "00A896",  // Seafoam
  accent: "02C39A"      // Mint
};
```

### Technology (科技创新)
```javascript
const colors = {
  primary: "5B4B8A",    // Tech purple
  secondary: "A99BBD",
  accent: "E8DFF5"
};
```

### Traditional/Government (传统政务)
```javascript
const colors = {
  primary: "8B0000",    // Dark red
  secondary: "2F4F4F",  // Dark gray-green
  accent: "CD853F"      // Sand/gold
};
```

## Layout Considerations

### Safe Coordinate Boundaries

**Critical**: PPT slides are 10 x 7.5 inches, but usable area is smaller:

- **X range**: 0.5 - 9.5 (max width: 9 inches)
- **Y range**: 0.5 - 7.0 (max height: 6.5 inches)

**Always check**: `y + height ≤ 7.0` and `x + width ≤ 9.5`

```javascript
// ❌ BAD: Exceeds bottom boundary
slide.addShape({
  x: 0.5, y: 6.5, w: 9, h: 1.0  // 6.5 + 1.0 = 7.5 ✗
});

// ✅ GOOD: Within safe zone
slide.addShape({
  x: 0.5, y: 6.1, w: 9, h: 0.5  // 6.1 + 0.5 = 6.6 ✓
});
```

### Recommended Layout Grid

```
y: 0.0-0.5   Header bar
y: 1.0-3.0   Main content area 1
y: 3.2-5.5   Main content area 2
y: 6.0-6.5   Footer/summary (last element)
```

## Common Mistakes & Fixes

### Issue: Text appears too cramped
**Fix**: Increase `lineSpacing` to 18-20 for Chinese

### Issue: Font appears as system default
**Fix**: Always set `fontFace: "Microsoft YaHei"` or `"PingFang SC"`

### Issue: Content cut off at bottom
**Fix**: Ensure all `y + h ≤ 7.0`

### Issue: Numbers look disconnected from Chinese text
**Fix**: Use Arial/Calibri for numbers with Chinese text font for labels:

```javascript
// Number
slide.addText("85", {
  fontSize: 56,
  fontFace: "Arial"  // Clean, modern numbers
});

// Label
slide.addText("公斤", {
  fontSize: 12,
  fontFace: "Microsoft YaHei"  // Chinese label
});
```

## Complete Example

```javascript
const pptxgen = require("pptxgenjs");
let pres = new pptxgen();

const colors = {
  primary: "028090",
  secondary: "00A896",
  accent: "02C39A",
  white: "FFFFFF",
  text: "1A3A3A"
};

let slide = pres.addSlide();
slide.background = { fill: colors.white };

// Header bar (y: 0-0.5)
slide.addShape(pres.ShapeType.rect, {
  x: 0, y: 0, w: "100%", h: 0.5,
  fill: { color: colors.primary }
});

slide.addText("演示文稿标题", {
  x: 0.5, y: 0.1, w: 9, h: 0.3,
  fontSize: 32,
  bold: true,
  color: colors.white,
  fontFace: "Microsoft YaHei"  // Explicit Chinese font
});

// Content card (y: 1.2-3.4)
slide.addShape(pres.ShapeType.roundRect, {
  x: 0.5, y: 1.2, w: 9, h: 2.2,
  fill: { color: "F0F8F7" },
  line: { color: colors.secondary, width: 2 }
});

slide.addText(
  "• 第一个要点说明\n" +
  "• 第二个要点说明\n" +
  "• 第三个要点说明",
  {
    x: 0.8, y: 1.5, w: 8.4, h: 1.6,
    fontSize: 14,
    color: colors.text,
    fontFace: "Microsoft YaHei",
    lineSpacing: 18  // Generous spacing for Chinese
  }
);

// Footer (y: 6.0-6.5)
slide.addShape(pres.ShapeType.roundRect, {
  x: 0.5, y: 6.0, w: 9, h: 0.5,  // Safe: 6.0 + 0.5 = 6.5
  fill: { color: colors.accent }
});

slide.addText("总结说明文字", {
  x: 0.7, y: 6.05, w: 8.6, h: 0.4,
  fontSize: 12,
  color: colors.white,
  fontFace: "Microsoft YaHei",
  valign: "middle"
});

pres.writeFile({ fileName: "中文演示文稿.pptx" });
```

## Design Principles

1. **Font First**: Always specify Chinese fonts explicitly
2. **Line Spacing**: 18-20pt for Chinese (vs. 14-16 for English)
3. **Safe Coordinates**: Keep all elements with `y + h ≤ 7.0`
4. **Cultural Colors**: Choose palettes appropriate for Chinese audiences
5. **Number Fonts**: Use Arial/Calibri for numbers with Chinese labels
6. **Test Early**: Generate and visually inspect slides frequently

## Quality Checklist

- [ ] All Chinese text has `fontFace` specified
- [ ] Line spacing is 18-20 for multi-line Chinese text
- [ ] All elements satisfy `y + h ≤ 7.0` and `x + w ≤ 9.5`
- [ ] Color scheme matches presentation theme
- [ ] Numbers use Arial/Calibri, labels use Chinese font
- [ ] Generated slide viewed in PowerPoint/Keynote

## Resources

- [pptxgenjs Documentation](https://gitbrent.github.io/PptxGenJS/)
- [Chinese Typography Guidelines](https://github.com/sparanoid/chinese-copywriting-guidelines)
- Main PPTX Skill: See [SKILL.md](./SKILL.md)

---

**Note**: This guide supplements the main PPTX skill with Chinese-specific recommendations. For general pptxgenjs usage, refer to the main [SKILL.md](./SKILL.md) file.
