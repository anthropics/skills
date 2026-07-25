# Academic Poster Design Principles

## Visual Hierarchy (Distance-First Design)

Conference attendees scan 100+ posters in an hour. Design for three viewing distances:

| Distance | What's visible | Requirements |
|----------|---------------|--------------|
| 15+ feet | Title + hero result | 54-60pt, bold, high contrast |
| 6-8 feet | Section headers + key figures | 28-30pt headers, large annotated figures |
| 3-4 feet | Body text + details | 23-25pt bullets, table data |

## Content Strategy

### The One-Sentence Test
If you can't state the poster's message in one sentence, the content isn't focused enough. Everything on the poster either supports that sentence or should be cut.

### Word Budget
- **Total poster**: 300-600 words maximum
- **Per section**: 50-100 words (3-4 bullets)
- Posters are conversation starters, not papers

### What to Include
- **Always**: Method diagram, key results table/chart, core insight statement
- **Usually**: Problem motivation (brief), ablation/analysis, takeaway boxes
- **Sometimes**: QR code to paper/code, qualitative examples
- **Never**: Full related work, complete equations, dense paragraphs

### Creative Elements That Make a Poster Stand Out
- **Hero insight banner**: A full-width highlighted box at the top of the content area that states the core contribution in one compelling sentence. Uses color to draw the eye.
- **Key result boxes**: 2-3 metric highlights (e.g., "+7.5%", "<1% overhead") with big numbers and short labels. These are what people photograph.
- **Annotated figures**: Don't just paste figures — add callout arrows, highlight boxes, bold annotations directly on charts.
- **"How it works" explanation box**: A colored background box that explains the mechanism in plain language, separate from the technical bullets.

## Layout Patterns

### Standard Two-Column (Most Common)
```
┌──────────────────────────────────┐
│  HEADER: Title, Authors, Logos   │
│  HERO: Core insight banner       │
│  KEY RESULTS: 2-3 metric boxes   │
├────────────────┬─────────────────┤
│  Problem       │  Architecture   │
│  Method 1      │  How It Works   │
│  Figure 1      │  Results Table  │
│  Method 2      │  Observations   │
│  Ablation Fig  │                 │
├────────────────┴─────────────────┤
│  KEY TAKEAWAYS: 3 summary boxes  │
└──────────────────────────────────┘
```

### Balancing Columns
- Track Y position independently for each column
- Full-width sections (hero, takeaways) start at max(left_y, right_y)
- Aim for columns within 1-1.5 inches of each other
- If one column is much longer, move content (e.g., ablation chart) to the shorter column

## Color and Typography

### Color Rules
- **2-3 colors maximum** for the theme (extract from template)
- One dominant color (headers, accents), one for emphasis, one neutral
- **High contrast**: dark text on white/light backgrounds
- **Color-blind safe**: avoid red-green encoding; blue-orange is universally safe
- Use colored background boxes sparingly for emphasis — if everything is highlighted, nothing is

### Typography
- **Single font family** (whatever the template uses — usually Calibri, Arial, or Helvetica)
- Use **weight** (bold/regular) and **size** for hierarchy, not multiple typefaces
- Bold for: key terms in bullets, section-specific terminology, numbers that matter
- Italic for: emphasis in the hero banner, technical terms on first use

## Figure Guidelines

### Resolution
- Render PDF pages at 400-500 DPI for cropping
- Never copy-paste from the paper PDF directly (72 DPI → blurry at poster scale)
- Verify the cropped figure is readable when the poster is viewed at 25% zoom

### Cropping
- Remove: line numbers, page headers, figure numbers, captions
- Keep: all axes labels, legends, annotations
- For tables: crop only the data rows and column headers

### Sizing
- Method/architecture diagram: at least 4-5 inches tall on the poster
- Results table: large enough to read individual numbers (5-6 inches)
- Ablation charts: 3-4 inches tall
- Never shrink a figure below the point where its text becomes unreadable

## Common Mistakes

1. **Too much text** → Nobody reads walls of text. Use 3-4 bullet points per section.
2. **Paper figures at paper resolution** → Blurry at poster scale. Re-render at 400+ DPI.
3. **No visual hierarchy** → Everything same size = nothing stands out.
4. **Missing method diagram** → The architecture figure is what people remember.
5. **Bare results without annotation** → Add callout boxes, highlight best numbers.
6. **Inconsistent spacing** → Use a grid system (same margins, same column gap).
7. **Forgetting the "so what"** → Lead with the result, not the method.
8. **Ending with "Thank You"** → Use a Conclusions/Takeaways box instead.
