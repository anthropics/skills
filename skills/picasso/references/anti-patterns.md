# Anti-Patterns Reference

This is the most important reference file. These are the patterns that make AI-generated interfaces immediately recognizable. Avoid all of them.

---

## Typography Anti-Patterns

- **Inter everywhere.** The default safe choice. It signals "I did not think about fonts."
- **Roboto, Arial, Helvetica, system-ui as primary.** Same problem.
- **Space Grotesk on repeat.** Overused in AI/crypto contexts. Pick something else.
- **Light (300) weight for body text.** Hard to read on most screens.
- **Centered paragraphs.** Center alignment works for 1-2 lines (headings, quotes). Never for body text.
- **No max-width on text.** Lines spanning 1400px are unreadable. Cap at 600-750px for body text.
- **All caps without letter-spacing.** All-caps text needs 0.08-0.15em spacing to be legible.
- **More than 3 font families.** Two is ideal. Three is the maximum.
- **Font size under 14px for body text.** Especially on mobile.

---

## Color Anti-Patterns

- **Purple gradient on white background.** The signature AI slop aesthetic.
- **Pure black text (#000000).** Always use tinted near-black (e.g., oklch(0.15 0.02 260)).
- **Pure gray (#808080, #cccccc).** Always tint neutrals toward the palette hue.
- **Gray text on colored backgrounds.** Creates low contrast and looks washed out.
- **Full-saturation brand colors for large surfaces.** Reserve maximum chroma for small accents. Large areas need reduced saturation.
- **Too many accent colors.** One primary, one secondary maximum. More creates visual chaos.
- **Using opacity instead of actual color values.** opacity:0.5 on colored elements creates inconsistent results depending on background.
- **No dark mode consideration.** Even if not implementing dark mode, design with the possibility in mind.

---

## Layout Anti-Patterns

- **Everything centered vertically and horizontally.** Creates a lifeless vertical highway. Use left-aligned content with intentional centering for specific elements.
- **Cards nested inside cards.** One level of card is usually enough. Nesting creates visual confusion about hierarchy.
- **Wrapping everything in cards.** Not every piece of content needs a container with rounded corners and a shadow. Sometimes flat sections, dividers, or whitespace work better.
- **Uniform rounded corners on everything.** Vary border-radius by context: pills for tags (999px), subtle rounding for cards (8-12px), sharper for data elements (4px).
- **Equal spacing everywhere.** Groups need tighter internal spacing and wider external spacing. Without this, there is no visual structure.
- **Three or four equal columns at every breakpoint.** Asymmetric grids (2:1, 3:2) are more interesting and create clearer hierarchy.
- **Content that could belong to any product.** If the layout has no personality, the design is not done.

---

## Motion Anti-Patterns

- **Bounce/elastic easing.** Feels dated and gimmicky. Use ease-out curves.
- **Animating everything on the page.** Creates visual noise. Animate the important moments.
- **transition: all 0.3s.** Animates properties you did not intend. Be specific: `transition: opacity 0.2s, transform 0.3s`.
- **No loading feedback.** User clicks a button and nothing happens for 2 seconds. Always show progress.
- **Spinner for content areas.** Use skeleton screens instead. Spinners should be reserved for small inline actions.
- **Animation without prefers-reduced-motion handling.** Always provide a reduced-motion path.

---

## Interaction Anti-Patterns

- **Placeholder text as the only label.** Disappears on focus. Inaccessible.
- **outline: none without replacement.** Keyboard users lose all orientation.
- **Hover-only interactions.** Must have keyboard and touch equivalents.
- **Custom scrollbars that break native behavior.** Users expect scrolling to work natively.
- **Toast notifications for errors.** They disappear. Use inline error messages instead.
- **Alert/confirm dialogs for minor actions.** Blocking the entire page for "Are you sure?" on non-destructive actions.
- **No focus trapping in modals.** Tab key escapes the modal and the user gets lost.
- **Links that look like buttons and buttons that look like links.** Use the correct element for the correct purpose.

---

## Code Anti-Patterns

- **div soup.** Use semantic HTML: nav, main, section, article, aside, header, footer.
- **Inline styles for everything.** Use CSS variables, modules, or Tailwind. Inline styles cannot be overridden or themed.
- **!important everywhere.** If specificity requires !important, the CSS architecture is broken.
- **z-index: 9999.** Use a z-index scale (1, 10, 20, 30...) with named CSS variables.
- **Fixed pixel values for everything.** Use rem for typography and spacing, em for component-internal sizing, px only for borders and shadows.
- **console.log left in production.** Clean it up.

---

## Content Anti-Patterns

- **"Lorem ipsum" in final deliverables.** Use real or realistic content. Design without content is decoration.
- **Stock photo people smiling at laptops.** If using imagery, make it contextual.
- **"Click here" link text.** Links should describe their destination: "View documentation" not "Click here".
- **"Submit" button text.** Use the specific action: "Create account", "Send message", "Save changes".
- **Walls of text without hierarchy.** Break content with headings, spacing, and visual rhythm.

---

## The Overall Pattern to Avoid

The "AI slop" aesthetic is recognizable by its combination of: Inter/Roboto font, purple/blue gradient accents, evenly spaced centered layouts, uniform card grids with identical rounded corners, and generic stock imagery. Any single element might be fine in isolation. Together, they signal "an AI made this with zero human judgment."

The antidote is intentionality. Every choice (font, color, spacing, layout, animation) should be a conscious decision tied to the specific context of what you are building.
