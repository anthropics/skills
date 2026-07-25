# Flowchart Layout

## Shape Vocabulary

| Shape | Meaning | SVG Element |
|-------|---------|-------------|
| Rounded rect (large radius) | Start / End | `<rect rx="25">` |
| Rectangle | Process / Action | `<rect rx="6">` |
| Diamond | Decision | `<polygon>` rotated 45° |
| Parallelogram | Input / Output | `<polygon>` with skew |
| Cylinder | Data store | Ellipse + rect combo |

## Flow Direction

Primary flow: **top to bottom**. Branch flows go left/right from decisions.

## Layout Algorithm

1. **Identify the main path** (happy path / most common flow) — this runs straight down the center
2. **Branch from decisions:** "Yes" continues down center, "No" branches right (or left if space is tight)
3. **Merge paths:** Route branches back to the main path using L-shaped connectors
4. **Loop-backs:** Route upward on the far left/right side of the diagram with curved paths

## Spacing

- Step-to-step vertical gap: 60-80px (enough for arrow + optional label)
- Decision diamond height: 70px (point to point)
- Decision diamond width: 100px (point to point)
- Branch horizontal offset: 200px from center
- Merge connector clearance: 20px from any box

## Decision Labels

Place "Yes" / "No" (or "True" / "False", "是" / "否") labels directly on the exit arrows, 10px from the diamond edge:

```svg
<!-- Decision diamond at center (400, 200) -->
<!-- Yes: downward -->
<line x1="400" y1="235" x2="400" y2="300" stroke="#64748b" marker-end="url(#arrow)"/>
<text x="412" y="260" fill="#34d399" font-size="8">Yes</text>

<!-- No: rightward -->
<line x1="450" y1="200" x2="550" y2="200" stroke="#64748b" marker-end="url(#arrow)"/>
<text x="480" y="193" fill="#fb7185" font-size="8">No</text>
```

## Coloring Strategy

- **Start/End nodes:** Highlight color (blue)
- **Process steps:** Primary (cyan) or Secondary (emerald)
- **Decision diamonds:** Accent (amber) — they draw the eye naturally
- **Error/exception paths:** Alert (rose) dashed arrows
- **Happy path arrows:** Slightly brighter than branch arrows (`stroke-opacity` difference)

## Complex Flowcharts

For flowcharts with 10+ steps:
- Group related steps into swim lanes (vertical columns with header bars)
- Add a "phase" row header at the top of each swim lane
- Use the region boundary pattern from Architecture for swim lanes
