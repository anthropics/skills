---
name: frontend-design-pro
description: Production-grade frontend design skill with anti-convergence patterns, visual iteration workflows, and test-driven UI development. Extends official frontend-design with community-tested improvements. Use when building any web UI, component, dashboard, landing page, React component, or HTML/CSS layout. Generates distinctive, memorable interfaces that avoid generic AI aesthetics.
---

# Frontend Design Pro

This skill creates distinctive, production-grade frontend interfaces that avoid generic "AI slop" aesthetics. It extends Anthropic's official frontend-design approach with battle-tested community improvements.

## Design Thinking

Before coding, commit to a **BOLD** aesthetic direction:

1. **Purpose**: What problem does this interface solve? Who uses it?
2. **Tone**: Pick an extreme - brutally minimal, maximalist chaos, retro-futuristic, organic/natural, luxury/refined, playful/toy-like, editorial/magazine, brutalist/raw, art deco/geometric, soft/pastel, industrial/utilitarian
3. **Constraints**: Framework, performance, accessibility requirements
4. **Differentiation**: What's the ONE thing someone will remember?

**CRITICAL**: Choose a clear conceptual direction and execute it with precision.

## Frontend Aesthetics Guidelines

### Typography
- Choose fonts that are beautiful, unique, and interesting
- **NEVER** use: Inter, Roboto, Arial, Open Sans, Lato, system fonts
- **PREFER**: JetBrains Mono, Fira Code (code aesthetic); Playfair Display, Crimson Pro (editorial); IBM Plex family (technical); Bricolage Grotesque, Newsreader (distinctive)
- Use high-contrast pairing: Display + monospace, serif + geometric sans
- Apply extreme weights (100/200 vs 800/900) and size jumps of 3x+

### Color & Theme
- Commit to a cohesive aesthetic using CSS variables
- Dominant colors with sharp accents outperform evenly-distributed palettes
- Draw inspiration from IDE themes (VSCode, Sublime) and cultural aesthetics
- **NEVER** use: purple gradients on white, safe neutral palettes

### Motion & Micro-interactions
- CSS-only for HTML; Motion library for React
- One well-orchestrated page load with staggered reveals (animation-delay) > scattered micro-interactions
- Scroll-triggering and hover states that surprise

### Spatial Composition
- Unexpected layouts: asymmetry, overlap, diagonal flow
- Grid-breaking elements
- Generous negative space OR controlled density

### Backgrounds & Visual Details
- Create atmosphere and depth (never solid colors by default)
- Gradient meshes, noise textures, geometric patterns
- Layered transparencies, dramatic shadows, grain overlays

---

## Enhanced Guidelines

For detailed guidance on anti-convergence, visual iteration, and test-driven patterns, see [references/extensions.md](references/extensions.md).

### Anti-Convergence Protocol

**CRITICAL**: Claude tends to converge on new defaults even when avoiding old ones.

For EACH generation, actively vary:
- **Theme**: Alternate between light and dark
- **Typography**: Never use the same font family twice in a row (track: Space Grotesk, Syne, Outfit are common convergence targets)
- **Color Temperature**: Rotate through warm palettes → cool palettes → earth tones
- **Layout Paradigm**: Cycle through asymmetric → grid-based → overlap → diagonal flow

Before finalizing, ask yourself: "Have I used this combination before? If yes, change it."

### Visual Iteration Workflow

For complex interfaces, use screenshot-driven refinement:

1. Generate initial implementation
2. Take screenshot via Puppeteer/Playwright MCP or manual capture
3. Compare screenshot to requirements/mockup
4. Identify discrepancies in spacing, alignment, color, typography
5. Iterate until visual match achieved

\`\`\`
Prompt: "Take a screenshot of the current state and compare to requirements"
\`\`\`

### Test-Driven UI Development

Before implementing complex UIs:

1. Write Playwright/Vitest tests for expected behavior:
   - Layout responsiveness across breakpoints
   - Animation timing and easing
   - Color contrast for accessibility (WCAG AA minimum)
   - Typography rendering

2. Implement UI to pass tests

3. Use tests as regression guard

\`\`\`
Prompt: "Write failing Playwright tests for this UI, then implement to pass them"
\`\`\`

### Progressive Disclosure for Large UIs

For dashboards and complex applications:

1. Design information hierarchy first
2. Implement above-the-fold with full detail
3. Use progressive loading for secondary content
4. Test on multiple viewport sizes before declaring complete

---

## Implementation Checklist

Before submitting any frontend code, verify:

- [ ] No generic fonts (Inter, Roboto, Arial, system-ui)
- [ ] No purple gradients on white backgrounds
- [ ] CSS variables used for colors
- [ ] At least one distinctive visual element
- [ ] Animations are purposeful, not decorative
- [ ] Layout has intentional asymmetry or interesting composition
- [ ] Background has depth/texture (not solid color unless intentional minimalism)

---

Remember: Claude is capable of extraordinary creative work. Don't hold back—show what can truly be created when thinking outside the box and committing fully to a distinctive vision.
