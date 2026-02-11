---
name: image-generation
description: Create data visualizations, infographics, charts, and technical diagrams as PNG or JPG images. Use this skill when users need professional images for presentations, reports, documentation, or social media. Focuses on clarity, data accuracy, and visual communication rather than artistic expression.
license: Complete terms in LICENSE.txt
---

# Image Generation

Create clear, professional images for data visualization, infographics, charts, diagrams, and technical illustrations. This skill focuses on practical visual communication - outputting PNG and JPG files optimized for presentations, reports, documentation, and digital media.

## When to Use This Skill

Use this skill when the user requests:
- **Data visualizations**: Bar charts, line graphs, pie charts, scatter plots, heatmaps
- **Infographics**: Visual representations of information, statistics, or processes
- **Technical diagrams**: Flowcharts, system architecture, network diagrams, org charts
- **Comparison images**: Before/after, feature comparisons, product matrices
- **Social media graphics**: Quote cards, statistics, announcement images
- **Reference images**: Quick visual guides, cheat sheets, visual summaries

**Do NOT use this skill for:**
- Artistic or abstract visual art (use `canvas-design` instead)
- Interactive or generative art (use `algorithmic-art` instead)
- Animated content (use `slack-gif-creator` instead)

## Output Requirements

Generate images in the following formats:
- **PNG**: For images with transparency, sharp text, diagrams, or screenshots
- **JPG/JPEG**: For photographs, complex images, or when smaller file size is needed

### Image Specifications

**Standard Dimensions:**
- Presentation slide: 1920×1080px (16:9) or 1280×720px
- Social media (Instagram square): 1080×1080px
- Social media (Instagram story): 1080×1920px (9:16)
- Social media (Twitter/X): 1200×675px
- Blog header: 1200×630px
- Print (300 DPI): Calculate based on physical size
- Custom: As requested by user

**Quality Guidelines:**
- Use high resolution (minimum 72 DPI for web, 300 DPI for print)
- Ensure text is crisp and readable at intended viewing size
- Optimize file size without sacrificing quality
- Include proper margins and padding

## Creation Process

Follow this systematic approach:

### Step 1: Understand the Requirements

Clarify with the user:
- **Purpose**: What will this image be used for?
- **Content**: What data, information, or concept needs to be visualized?
- **Format**: PNG or JPG? What dimensions?
- **Style**: Professional corporate, modern minimal, colorful casual, technical/academic?
- **Branding**: Any specific colors, fonts, or style guidelines?

### Step 2: Plan the Visual Structure

Before creating, plan:
- **Layout**: How to organize information spatially
- **Hierarchy**: What's most important? What grabs attention first?
- **Color scheme**: Choose 2-5 colors that work together
- **Typography**: Select readable fonts appropriate for the content
- **Data accuracy**: Verify all numbers, labels, and information

### Step 3: Create the Image

Use HTML Canvas API or similar tools to generate the image:

```html
<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <title>Image Generation</title>
</head>
<body>
    <canvas id="canvas" width="1920" height="1080"></canvas>
    <script>
        const canvas = document.getElementById('canvas');
        const ctx = canvas.getContext('2d');

        // Set background
        ctx.fillStyle = '#FFFFFF';
        ctx.fillRect(0, 0, canvas.width, canvas.height);

        // Add your visualization code here
        // - Draw shapes, text, charts
        // - Use proper fonts and colors
        // - Ensure proper spacing and alignment

        // Export as image
        // PNG: canvas.toDataURL('image/png')
        // JPG: canvas.toDataURL('image/jpeg', 0.95)
    </script>
</body>
</html>
```

**Technical Implementation Options:**
1. **HTML Canvas**: Draw shapes, text, and graphics programmatically
2. **SVG to Raster**: Create SVG, then convert to PNG/JPG
3. **HTML Rendering**: Style HTML/CSS, then capture as image
4. **Chart Libraries**: Use Chart.js, D3.js, or similar (loaded via CDN)

### Step 4: Quality Check

Before delivering, verify:
- ✅ All text is readable and properly aligned
- ✅ Colors have sufficient contrast
- ✅ Data is accurate and properly labeled
- ✅ Image dimensions match requirements
- ✅ File format is appropriate (PNG vs JPG)
- ✅ File size is reasonable for intended use
- ✅ No elements are cut off at edges

### Step 5: Provide the Image

Output:
1. The final image file (PNG or JPG)
2. Brief description of what was created
3. Technical details (dimensions, format, file size if available)

## Chart Types and When to Use Them

**Bar Chart**: Comparing quantities across categories
**Line Graph**: Showing trends over time
**Pie Chart**: Showing proportions of a whole (use sparingly, max 5-7 slices)
**Scatter Plot**: Showing correlation between two variables
**Heatmap**: Showing intensity across two dimensions
**Flowchart**: Showing process steps and decision points
**Org Chart**: Showing hierarchical relationships
**Timeline**: Showing chronological events
**Comparison Table**: Side-by-side feature or option comparison

## Design Best Practices

### Typography
- Use sans-serif fonts for clarity (Arial, Helvetica, Roboto, Open Sans)
- Font sizes: Title 32-48px, Headings 24-32px, Body 16-20px, Labels 12-16px
- Ensure adequate line spacing (1.4-1.6x font size)
- Use font weight for hierarchy (bold for emphasis)

### Color
- Limit palette to 2-5 colors plus neutrals
- Ensure sufficient contrast (WCAG AA: 4.5:1 for text)
- Use color purposefully (not decoratively)
- Consider colorblind accessibility (avoid red/green alone)
- Recommended palettes:
  - Professional: Blues and grays (#2563EB, #475569, #F1F5F9)
  - Warm: Oranges and browns (#EA580C, #78350F, #FED7AA)
  - Vibrant: Multiple bright colors (#EF4444, #F59E0B, #10B981, #3B82F6)

### Layout
- Use consistent margins (minimum 40-60px from edges)
- Align elements to a grid
- Group related information together
- Use whitespace to separate sections
- Maintain visual balance

### Data Visualization Principles
- Always label axes and provide units
- Start Y-axis at zero for bar charts (unless showing small variations)
- Order categories logically (alphabetical, by value, or chronological)
- Use consistent scales when comparing multiple charts
- Highlight the key insight or finding
- Keep it simple - remove unnecessary elements

## Examples

### Example 1: Bar Chart
```
User: "Create a bar chart showing Q1-Q4 sales: Q1=$45K, Q2=$62K, Q3=$58K, Q4=$71K"

Response: Create a clean horizontal or vertical bar chart with:
- Title: "2024 Quarterly Sales"
- 4 bars representing each quarter
- Y-axis labeled "Sales (USD)" with scale 0-80K
- X-axis with Q1, Q2, Q3, Q4
- Values displayed on or above bars
- Professional color scheme
- Output as PNG 1920×1080px
```

### Example 2: Infographic
```
User: "Make an infographic showing our app has 1M users, 4.8★ rating, available in 12 countries"

Response: Create a visually appealing infographic with:
- Eye-catching header: "Our App by the Numbers"
- Three key statistics prominently displayed with icons
- Visual hierarchy emphasizing the numbers
- Brand colors if provided
- Clean, modern design
- Output as PNG 1080×1080px for social media
```

### Example 3: Flowchart
```
User: "Create a flowchart for our customer support process"

Response: Create a clear flowchart with:
- Standard flowchart symbols (rectangles for process, diamonds for decisions)
- Logical flow from top to bottom (or left to right)
- Clear, concise labels
- Arrows showing direction
- Consistent spacing and alignment
- Output as PNG with appropriate dimensions
```

## Technical Notes

### Creating Effective Charts with Chart.js

If using Chart.js (loaded via CDN):

```html
<script src="https://cdn.jsdelivr.net/npm/chart.js"></script>
<canvas id="myChart"></canvas>
<script>
const ctx = document.getElementById('myChart');
new Chart(ctx, {
    type: 'bar',
    data: {
        labels: ['Q1', 'Q2', 'Q3', 'Q4'],
        datasets: [{
            label: 'Sales',
            data: [45, 62, 58, 71],
            backgroundColor: '#2563EB'
        }]
    },
    options: {
        responsive: false,
        plugins: {
            legend: { display: false },
            title: {
                display: true,
                text: '2024 Quarterly Sales',
                font: { size: 24 }
            }
        }
    }
});
</script>
```

### Exporting Canvas to Image

```javascript
// PNG (lossless, larger file)
const pngDataUrl = canvas.toDataURL('image/png');

// JPG (lossy, smaller file)
const jpgDataUrl = canvas.toDataURL('image/jpeg', 0.92); // quality 0-1

// To download (in browser context)
const link = document.createElement('a');
link.download = 'chart.png';
link.href = pngDataUrl;
link.click();
```

## Common Pitfalls to Avoid

❌ **Don't**: Use too many colors (creates visual chaos)
✅ **Do**: Stick to a limited, cohesive color palette

❌ **Don't**: Cram too much information into one image
✅ **Do**: Focus on one key message or dataset per image

❌ **Don't**: Use decorative fonts that hurt readability
✅ **Do**: Choose clear, professional fonts

❌ **Don't**: Forget to label axes, provide legends, or show units
✅ **Do**: Make data self-explanatory

❌ **Don't**: Use default colors without consideration
✅ **Do**: Choose colors intentionally for clarity and brand

❌ **Don't**: Create images with poor resolution or wrong dimensions
✅ **Do**: Match specifications to the intended use case

## Accessibility Considerations

- Use sufficient color contrast (test with tools)
- Don't rely on color alone to convey meaning
- Include text labels and descriptions
- Use patterns or shapes in addition to colors when possible
- Ensure text is large enough to read

## File Format Decision Guide

**Choose PNG when:**
- Image contains text or sharp lines
- Transparency is needed
- Image will be edited or resized later
- Maximum quality is required
- File size is not a concern

**Choose JPG when:**
- Image is photographic or has many colors/gradients
- Smaller file size is important
- Transparency is not needed
- Image is final and won't be edited

## Final Checklist

Before delivering any image, confirm:
- [ ] Purpose and use case are clear
- [ ] Data accuracy is verified
- [ ] Dimensions match requirements
- [ ] Text is readable and properly sized
- [ ] Colors are appropriate and accessible
- [ ] Layout is balanced and professional
- [ ] File format (PNG/JPG) is correct
- [ ] Image is properly exported and ready to use

---

**Remember**: The goal is clear visual communication. Prioritize readability, accuracy, and professionalism over decorative elements. Every design choice should serve the purpose of helping the viewer understand the information quickly and accurately.
