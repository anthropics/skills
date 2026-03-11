# Audit Protocol — Full Checklist for Existing Design Systems
<!-- dischromatopsy-color-skill v1.0.0 | references/audit-protocol.md -->

## PHASE 1: INVENTORY

### Step 1.1 — Extract all color values
- [ ] List all CSS custom properties (variables)
- [ ] Find all hardcoded color literals (search for: #, rgb(, hsl(, rgba()
- [ ] List all background/foreground pairings from the DOM structure
- [ ] Document each pair: (foreground, background, element type, font size)

### Step 1.2 — Categorize elements
For each color-bearing element, classify as:
- TEXT — body, labels, descriptions, placeholders, values
- STATE — error, warning, success, info, disabled, active badges
- INTERACTIVE — buttons, links, toggles, checkboxes, radio buttons
- STRUCTURAL — borders, dividers, focus rings
- DECORATIVE — backgrounds, illustrations, icons without text equivalent
- DATA VIZ — chart series, graph lines, heatmaps

Decorative elements are exempt from contrast requirements.
ALL other categories must pass.

---

## PHASE 2: CONTRAST AUDIT

### Step 2.1 — Calculate all text/background pairs

Use formula from references/contrast-math.md.
Or use: https://webaim.org/resources/contrastchecker/

For each TEXT pair, record:
- Hex foreground
- Hex background
- Computed ratio
- Pass/fail vs. 4.5:1 (AA normal text)
- Pass/fail vs. 7:1 (AAA normal text — SKILL TARGET)
- Pass/fail vs. 3:1 (AA large text, UI elements)

### Step 2.2 — Red flags to check first

Priority audit sequence:
1. Any gray text (#555–#888) on any dark surface → almost always fails
2. Badge/pill OFF states → frequently use dim text on mid-gray backgrounds
3. Footer / metadata text → commonly deprioritized, often dim
4. Placeholder text → typically intentionally dim, often too dim
5. Disabled state text → legally exempt but review for usability
6. Any element using `opacity` to dim color → can push passing color to failing

### Step 2.3 — State indicator check

For every state indicator (status dots, badge labels, icon states, progress):
- [ ] Does it pass luminance contrast test?
- [ ] Is it distinguishable from adjacent states in GRAYSCALE?
- [ ] Does it use only color to convey state? (If yes: add redundant icon/label)
- [ ] Is red/green the differentiator? (FORBIDDEN as sole differentiator)
- [ ] Is blue/yellow the differentiator? (FORBIDDEN as sole differentiator)

---

## PHASE 3: CVD SIMULATION

### Step 3.1 — Visual simulation

Run the UI through ALL of these simulations (use DaltonLens / Chrome DevTools):
- [ ] Protanopia (no red cones)
- [ ] Deuteranopia (no green cones)
- [ ] Tritanopia (no blue cones)
- [ ] Achromatopsia (no color — pure grayscale)

### Step 3.2 — Simulated view checklist

Under each simulation:
- [ ] Can all text be read?
- [ ] Can all states be distinguished from each other?
- [ ] Does the UI hierarchy make sense (primary > secondary > muted)?
- [ ] Are buttons distinguishable from non-interactive surfaces?
- [ ] Are error/warning/success states distinguishable from each other?
- [ ] Are active/inactive states distinguishable?

### Step 3.3 — Achromatopsia test (ultimate luminance test)

If the UI is usable in full grayscale (achromatopsia simulation),
it will be usable for all CVD types. This is the strictest possible test.
Use it as the final gate.

---

## PHASE 4: REMEDIATION

### Priority order for fixes:

1. **CRITICAL:** Text below 4.5:1 — fix immediately
2. **HIGH:** Text 4.5:1–7:1 (AA pass, AAA fail) — fix next sprint
3. **MEDIUM:** State indicators using color as sole differentiator — add redundancy
4. **MEDIUM:** Forbidden color pairs (R/G, B/Y) as sole differentiators
5. **LOW:** Non-text UI elements below 3:1

### Remediation approach:

**For failing text colors:**
- Calculate minimum passing text color (see references/contrast-math.md Section 4)
- Lighten the text color (on dark backgrounds) until 7:1 achieved
- Prefer using CSS variables — change the variable, not the usage sites

**For state indicator color issues:**
- Option A: Add icon/glyph alongside color indicator
- Option B: Add text label alongside color indicator
- Option C: Adjust colors to luminance-unique values (see SKILL.md Section 4.3)
- Do ALL THREE for critical indicators

**For hardcoded color literals bypassing the variable system:**
- Replace all literals with variable references
- Audit with: `grep -rE '#[0-9a-fA-F]{3,6}' src/` or similar
- Zero hardcoded color literals should remain after remediation

---

## PHASE 5: VALIDATION

### Step 5.1 — Re-run contrast calculations on all fixed pairs
### Step 5.2 — Re-run all four CVD simulations
### Step 5.3 — Update CSS header comment to reflect:
```css
/* Contrast compliance: WCAG AAA (7:1) — HARD REQUIREMENT
 * All pairs verified: [DATE]
 * CVD target: protan + deutan + tritan simultaneously
 * NEXT review: [DATE + 1 year or on any palette change] */
```
### Step 5.4 — Lock the palette
- Document the palette version
- Lock date
- Require changelog entry for any color change
- State clearly: "Any color change requires contrast re-verification"

---

## PHASE 6: ONGOING

### Prevent regression:
- Add contrast check to CI/CD pipeline (tools: axe-core, Pa11y, Deque axe DevTools)
- Add lint rule prohibiting hardcoded color literals outside the token file
- Run CVD simulation on any new component before merge
- Include CVD simulation step in design review checklist

### Tools for automated contrast checking:
| Tool | Type | URL |
|------|------|-----|
| axe-core | JS library / CI | https://github.com/dequelabs/axe-core |
| Pa11y | CLI / CI | https://pa11y.org |
| Lighthouse | Chrome built-in | chrome://settings/help → DevTools |
| WAVE | Browser extension | https://wave.webaim.org |
| axe DevTools | Figma + browser | https://www.deque.com/axe/ |
