# Figma MCP Workflow Reference

## Overview

The Figma MCP gives Claude direct read and write access to Figma files. This reference covers how to use it safely and effectively during design audits.

---

## Reading a Design

### Tool: `resolve_shortlink`
Use when the user shares a short Figma URL (e.g. `fig.com/abc123`).
```
input: { shortlink: "https://fig.com/abc123" }
output: { nodeId: "123:456", fileKey: "AbCdEfGh" }
```
Use the returned nodeId for all subsequent calls.

### Tool: `get_design_context`
The primary tool for reading design data. Call on any frame, component, or layer.

**What it returns:**
- Layer tree (names, types, parent-child relationships)
- Typography: fontFamily, fontSize, fontWeight, lineHeight, letterSpacing
- Colors: fills (hex + opacity), strokes, background colors
- Layout: width, height, x, y, padding (top/right/bottom/left), gap (auto-layout)
- Component info: which components are used, their names, any overrides

**Best practices:**
- Start with the top-level frame, not individual layers
- If the frame is very complex (100+ layers), request specific sections
- Component names are a signal of design system health — look for names like "Button/Primary/Default" (good) vs "Rectangle 42" (bad)

### Tool: `get_screenshot`
Always call this alongside `get_design_context`. The visual rendering catches issues that data alone misses:
- Visual density and crowding
- Color contrast as it actually appears
- Alignment issues
- Overall hierarchy and balance

```
input: { nodeId: "123:456" }
output: { imageUrl: "..." }
```

### Tool: `get_design_pages`
Use to see all pages in a Figma file. Helpful if the user says "check my whole file" — you can list pages and ask which to audit.

### Tool: `get_metadata`
Returns file-level info: title, last modified, owner. Use to confirm you're in the right file.

---

## Auditing from Context Data

When you have the `get_design_context` output, check these specific fields:

### Typography Checks
```
Look for in context data:
- fontFamily → Are there more than 2 distinct families?
- fontSize → Any below 12? Body text below 14?
- lineHeight → Calculate ratio: lineHeight / fontSize. Should be 1.4–1.6 for body.
- fontWeight → Does weight vary meaningfully across hierarchy levels?
- letterSpacing → Negative on body text? (bad)
```

### Color Checks
```
Look for:
- fills[].color → Convert to hex, check contrast against background
- opacity → Low opacity text is a common contrast failure
- Multiple fills → Complex blending may affect contrast
```

### Spacing Checks
```
Look for:
- paddingTop, paddingRight, paddingBottom, paddingLeft → Are they consistent? Multiples of 8?
- itemSpacing (gap) → Multiple of 8?
- x, y positions → Do sibling elements align to shared values?
```

### Component Health Checks
```
Look for:
- Layer names like "Frame 12", "Group 7", "Rectangle" → Red flag: not using components
- Layer names like "Button/Primary/Hover" → Green flag: proper component system
- Detached instances → Components used inconsistently
```

---

## Making Edits in Figma

### Tool: `perform_editing_operations`
Use this to fix issues directly. **Always follow the safety rules below.**

### Safety Rules for Editing

**Rule 1: Always confirm before editing**
Never apply edits without asking:
> "I can fix [specific issue] on the [element name] layer. Want me to go ahead?"

**Rule 2: Target specific node IDs**
Get node IDs from `get_design_context` output. Never guess or construct IDs.

**Rule 3: One change at a time for critical properties**
For risky changes (colors, layout, component swaps), do one edit and check the result before continuing.

**Rule 4: Never bulk-edit without confirmation**
Don't say "I'll fix all the spacing issues" and run 20 operations. List what you'll change, confirm, then execute.

**Rule 5: Take a screenshot after editing**
After each batch of edits, call `get_screenshot` to verify the result looks correct.

---

### Common Edit Patterns

#### Fix a text color for contrast
```
operation: "SET_FILL_COLOR"
nodeId: "[text layer node ID]"
color: { r: 0.2, g: 0.2, b: 0.2, a: 1.0 }  // #333333 — passes 4.5:1 on white
```

#### Fix font size
```
operation: "SET_FONT_SIZE"
nodeId: "[text layer node ID]"
fontSize: 16
```

#### Fix padding on a frame
```
operation: "SET_PADDING"
nodeId: "[frame node ID]"
paddingTop: 16
paddingRight: 16
paddingBottom: 16
paddingLeft: 16
```

#### Fix spacing between auto-layout items
```
operation: "SET_ITEM_SPACING"
nodeId: "[auto-layout frame node ID]"
itemSpacing: 8
```

#### Rename a layer (for component hygiene)
```
operation: "RENAME_LAYER"
nodeId: "[layer node ID]"
name: "Button/Primary/Default"
```

---

## Reading Component Structure

Well-structured Figma files use a naming convention like:
```
ComponentName/Variant/State
Button/Primary/Default
Button/Primary/Hover
Button/Secondary/Disabled
Icon/Arrow/Right
```

When auditing, note if components follow this pattern. If they don't, flag it as a 🟡 Warning — it means the design won't scale well and handoff to developers will be harder.

---

## Common Figma-Specific Issues to Flag

| Issue | Figma Signal | Severity |
|---|---|---|
| No components used | All layers are "Frame", "Rectangle", "Group" | 🟡 |
| Detached components | Layer shows "⚠ Detached" | 🟡 |
| Inconsistent text styles | No shared text styles defined | 🟡 |
| Inconsistent color styles | No shared color styles defined | 🟡 |
| Missing auto-layout | Fixed-position elements that should flex | 🟢 |
| No grids defined | Layout grid not applied to frames | 🟢 |
| Unlabeled frames | Frames named "Frame 1", "Frame 2" | 🟢 |
| Missing variants | Component has no hover/disabled states | 🟡 |
| Images not masked | Raw image fills without mask shapes | 🟢 |

---

## When Figma MCP Isn't Available

If Figma MCP tools aren't connected, ask the user to:
1. Export a screenshot (PNG) and share it
2. Or share specific values they see in Figma's right panel (colors, font sizes, spacing)
3. Or copy-paste the CSS Figma generates (right panel → Inspect → CSS)

The CSS export from Figma is particularly useful — it contains exact font sizes, colors, and spacing values that can be checked programmatically.
