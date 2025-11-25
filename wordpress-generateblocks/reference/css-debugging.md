  - responsive
  - lighthouse
  - accessibility audit
---

# CSS Debugging & Browser DevTools

## Opening DevTools

```
Chrome/Edge: F12 or Ctrl+Shift+I (Cmd+Opt+I Mac)
Firefox: F12 or Ctrl+Shift+I
Safari: Cmd+Opt+I (Enable in Preferences first)
```

## Key Shortcuts

```
Ctrl+Shift+C    - Inspect element mode
Ctrl+Shift+M    - Toggle device toolbar
Ctrl+Shift+P    - Command palette
Ctrl+Shift+F    - Search all files
```

## Inspecting Elements

1. Click inspect icon (top-left) or Ctrl+Shift+C
2. Hover over element on page
3. Click to select

**Panels:**
- **Styles** - CSS rules by specificity
- **Computed** - Final computed values
- **Layout** - Box model visualization

## CSS Debugging

### Check Applied Styles
- Inline styles: `element.style`
- CSS rules: In order of specificity
- Inherited: Grayed out
- Overridden: Strikethrough

### Edit Styles Live
1. Click any CSS property/value
2. Edit in place
3. Press Enter to apply
4. Reload to reset

### Force Element States
1. Select element
2. Click `:hov` button
3. Check: `:hover`, `:active`, `:focus`, `:focus-visible`

## Layout Debugging

### Flexbox Inspector
- Look for "flex" badge next to `display: flex`
- Click to see visual overlay
- Shows direction, justify, align

### Grid Inspector
- Click "grid" badge
- Shows grid lines, gaps, tracks
- Firefox has best grid tools

### Box Model
```
┌─────────────────────┐
│      Margin         │
├─────────────────────┤
│      Border         │
├─────────────────────┤
│      Padding        │
├─────────────────────┤
│    Content (WxH)    │
└─────────────────────┘
```

## Common Issues

### Element Not Visible
Check:
1. `display: none`
2. `visibility: hidden`
3. `opacity: 0`
4. `z-index` (behind other elements)
5. `overflow: hidden` on parent
6. `width/height: 0`

### Layout Not Working
**Flexbox:**
- Check `display: flex` on parent
- Verify `flex-direction`
- Check `flex-wrap`

**Grid:**
- Check `display: grid` on parent
- Verify `grid-template-columns/rows`
- Check `gap`

### Spacing Problems
Check:
1. `box-sizing` (should be `border-box`)
2. Margin collapse (vertical margins)
3. Padding vs Margin
4. Absolute positioning

### Text Overflow
```css
/* Truncate with ellipsis */
text-overflow: ellipsis;
overflow: hidden;
white-space: nowrap;

/* OR break words */
overflow-wrap: break-word;
```

## Responsive Testing

### Device Emulation
1. Toggle device toolbar: Ctrl+Shift+M
2. Select preset or custom dimensions
3. Test touch events

**Breakpoints to test:**
- Mobile: 320px, 375px, 414px
- Tablet: 768px, 834px, 1024px
- Desktop: 1280px, 1440px, 1920px

### Media Queries
- Blue bar = active
- Gray bar = inactive
- Click to see conditions

## Performance

### Network Panel
- Check total requests, size, load time
- Filter: CSS, Images, JS, Fonts
- Look for: >100KB files, >1s requests, red (failed)

### Coverage Tool
1. Cmd+Shift+P → Show Coverage
2. Reload page
3. Red = unused, Green = used

### Lighthouse Audit
1. Lighthouse panel
2. Check: Performance, Accessibility, Best Practices, SEO
3. Click "Analyze page load"

**Targets:**
- LCP ≤ 2.5s
- INP ≤ 200ms
- CLS ≤ 0.1

## Accessibility

### Color Contrast
1. Select text element
2. Styles → Color picker
3. Shows contrast ratio
4. ✓ passes WCAG AA

**Targets:**
- Normal text: 4.5:1
- Large text: 3:1
- UI components: 3:1

### Accessibility Panel
Elements → Accessibility shows:
- Accessibility tree
- ARIA properties
- Computed name

## WordPress/GenerateBlocks

### Check GenerateBlocks CSS
```
View Source (Ctrl+U) → Search: gb-element-
Should find: <style id="generateblocks-style-css">
```

### Find Conflicting CSS
1. Inspect element
2. Look for strikethrough (overridden)
3. Trace to source file
4. Fix with specificity or `!important`

### Test Full-Width Sections
1. Inspect section
2. Computed width should be `100vw`
3. Check `margin-left: calc(50% - 50vw)`
4. Verify no `max-width` on parents

## Console Utilities

```javascript
$0                    // Selected element
$('selector')         // querySelector
$$('selector')        // querySelectorAll
copy($0)              // Copy to clipboard
getEventListeners($0) // Get event listeners
```

## Quick Checklist

### GenerateBlocks Debug
- [ ] Element has unique ID (gb-element-xxxxx)
- [ ] CSS generated in page source
- [ ] No conflicting theme styles
- [ ] Full-width uses gbp-section class
- [ ] Two-layer structure (outer + inner)
- [ ] Page meta: _generate-full-width-content = true

### Performance
- [ ] LCP < 2.5s
- [ ] INP < 200ms
- [ ] CLS < 0.1
- [ ] Images lazy loaded
- [ ] CSS minified
- [ ] No console errors
