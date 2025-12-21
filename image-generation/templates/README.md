# Image Generation Templates

This directory contains starter templates for common image generation tasks.

## Available Templates

### 1. chart-template.html
**Use for:** Creating charts and graphs using Chart.js library

**Features:**
- Bar, line, pie, doughnut, radar, scatter, and polar charts
- Professional styling and customization options
- Built-in download as PNG functionality
- Responsive and configurable
- Multiple datasets support

**Best for:**
- Business dashboards and reports
- Data visualization for presentations
- Statistical charts
- Trend analysis graphics

**Quick Start:**
1. Open the template file
2. Modify the `data.labels` array with your categories
3. Modify the `data.datasets[0].data` array with your values
4. Customize colors, title, and axis labels
5. Export as PNG

---

### 2. canvas-template.html
**Use for:** Custom drawings, infographics, and technical diagrams

**Features:**
- HTML5 Canvas API for complete drawing control
- Helper functions for common shapes and text
- Download as both PNG and JPG
- Example drawings included
- Commented code for easy customization

**Best for:**
- Custom infographics
- Technical diagrams and flowcharts
- Visual hierarchies
- Unique layouts and compositions
- Anything requiring precise control

**Quick Start:**
1. Open the template file
2. Find the "DRAWING CODE" section
3. Replace example shapes with your design
4. Use helper functions for common patterns
5. Export as PNG or JPG

---

## Usage in Claude

When using these templates with Claude:

1. **Request the specific type**: "Use the chart template to create a bar chart of..."
2. **Provide your data**: Share the numbers, labels, and categories
3. **Specify styling**: Mention colors, dimensions, or style preferences
4. **Choose format**: PNG for sharp graphics, JPG for photos/complex images

## Common Modifications

### Changing Dimensions
Both templates use `width` and `height` attributes on the canvas:

```html
<canvas id="canvas" width="1920" height="1080"></canvas>
```

Common sizes:
- **1920×1080** - Full HD presentation (16:9)
- **1080×1080** - Instagram square
- **1200×630** - Social media preview
- **1280×720** - HD presentation (16:9)

### Changing Colors
Look for `fillStyle`, `backgroundColor`, or color arrays:

```javascript
ctx.fillStyle = '#2563EB'; // Canvas API
backgroundColor: '#2563EB'  // Chart.js
```

### Changing Fonts
Look for `font` properties:

```javascript
ctx.font = 'bold 48px sans-serif'; // Canvas API
font: { size: 24, weight: 'bold' }  // Chart.js
```

## Tips for Best Results

### For Charts (chart-template.html)
- Keep data sets focused (max 7-10 categories)
- Use consistent color schemes
- Always label axes clearly
- Consider your audience when choosing chart type
- Test readability at intended display size

### For Canvas Drawings (canvas-template.html)
- Plan your layout before coding
- Use helper functions to avoid repetition
- Keep coordinate math simple with variables
- Test different canvas sizes
- Add adequate padding/margins

## Export Quality

### PNG
- Best for: Text, diagrams, charts, anything with sharp edges
- Lossless compression
- Supports transparency
- Larger file size

### JPG
- Best for: Photos, gradients, complex color images
- Lossy compression
- Smaller file size
- No transparency
- Quality parameter: 0.0 (worst) to 1.0 (best), typically use 0.9-0.95

## Troubleshooting

**Text appears blurry:**
- Increase canvas dimensions
- Use whole pixel coordinates
- Check display scaling

**Colors look different after export:**
- Ensure consistent color space
- Test on target platform
- Use web-safe colors

**File size too large:**
- Use JPG instead of PNG for complex images
- Reduce canvas dimensions
- Simplify graphics

**Elements cut off:**
- Add margins to your design
- Check coordinate calculations
- Test at target dimensions

## Additional Resources

- [Chart.js Documentation](https://www.chartjs.org/docs/latest/)
- [Canvas API Reference](https://developer.mozilla.org/en-US/docs/Web/API/Canvas_API)
- [Color Palette Tools](https://coolors.co/)
- [Web Content Accessibility Guidelines (WCAG)](https://www.w3.org/WAI/WCAG21/quickref/)
