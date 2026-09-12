---
name: cloning
description: |
  Clone any website to 100% fidelity — not 90%, not "close enough", 100%.
  Generates with Gemini 3.1 Pro, then pushes relentlessly through a self-healing visual loop
  until every section, every badge color, every animation, every pixel matches the original.
  Playwright-only deterministic pipeline. Never stops until the clone is indistinguishable.
  Use when user says "clone this website", "/cloning [URL]", "perfect clone this design",
  or wants to replicate any website's visual design. Also use when the user mentions
  "website cloning", "copy this design", "replicate this UI", "match this site exactly",
  "keep fixing", "push to 100%", or "refine the clone".
model: opus
context: fork
effort: max
---

# Website Cloning Skill v6.0

Clone any website with **100% fidelity**. Not 90%. Not "close enough." 100%.

**THE GOAL IS ALWAYS 100%.** Generate the first draft with Gemini, then push relentlessly — comparing every section, fixing every difference, iterating until the clone is indistinguishable from the original. The skill is not done when the code compiles. It's done when a human cannot tell which is the original and which is the clone.

**BEHAVIOR RULES:**
- `effort: max` — ALWAYS Maximum Effort. Never suggest simplifying. Never ask "Option A/B/C."
- **Never declare done early.** Keep comparing, keep fixing, keep iterating.
- **The visual comparison is the source of truth** — not your memory, not the quality gate, not the SSIM score. If the screenshots don't match, you're not done.
- **Preserve previous fixes.** In Refine Mode, NEVER regenerate from Gemini. Work with existing code.

**Architecture:** Playwright-only. No Chrome extension. Deterministic orchestrator + self-healing visual loop.

---

## API Key Setup (Required)

```bash
export GEMINI_API_KEY="your-key-here"
source ~/.zshrc
```

Get a key: [Google AI Studio](https://aistudio.google.com/apikey)

---

## Quick Start

```
/cloning https://example.com          # Full clone: extract + generate + refine
/cloning --refine ~/Desktop/my-clone  # Refine mode: skip generation, go straight to visual fix loop
```

---

## Workflow

Two modes: **Full Clone** (3 steps) and **Refine** (step 3 only).

### Mode Detection

If the user provides a URL → **Full Clone** (Steps 1-3)
If the user provides `--refine` + a directory path → **Refine Mode** (Step 3 only on existing clone)
If the user says "keep fixing", "push to 100%", "refine the clone" → **Refine Mode** on the most recent clone

**CRITICAL:** When in Refine Mode, NEVER regenerate the codebase from Gemini. Work with the existing code. Compare against original, fix differences, iterate. Regeneration destroys previous fixes.

### Step 1: Run Orchestrator (automated extraction)

```bash
python scripts/clone_orchestrator.py {url} /tmp/claude/cloning-{timestamp}
```

The orchestrator runs ALL extraction phases automatically:
- Multi-viewport screenshots (mobile, tablet, desktop, wide) at 2x DPI
- Section-level close-up screenshots (auto-detected, up to 15)
- 3 video recordings (scroll, interactions, hover) via Playwright
- All 9 extraction scripts (frameworks, tokens, layout, components, SVGs, HTML, measurements, fonts, animations)
- Asset downloading (images + fonts via same-origin browser requests)
- Full page HTML extraction
- Clone contract generation

Output: structured directory with screenshots/, videos/, extraction/, assets/, clone-contract.json

If Playwright is not installed, run: `pip install playwright && playwright install chromium`

### Step 2: Generate Code (Gemini)

```bash
python scripts/gemini_api_v4.py --artifacts /tmp/claude/cloning-{timestamp} --output ~/Desktop/{site}-clone
```

The `gemini_api_v4.py` script automatically:
- Assembles the prompt from all extraction data
- Attaches all 3 videos (scroll, interactions, hover) as inline video/webm
- Attaches screenshots (viewport + section close-ups)
- Includes all extraction data (tokens, layout, measurements, fonts, etc.)
- Sends to Gemini 3.1 Pro with optimal parameters

Then run mandatory post-processing:
- Deploy downloaded assets to `public/images/`
- Self-host fonts in `public/fonts/` (rewrite @font-face)
- Enforce measurements against extracted data
- Verify content against extracted HTML

### Step 3: Push to 100% — Section-by-Section Visual Loop (MANDATORY)

This is where fidelity goes from 80% to 100%. The Gemini output is a FIRST DRAFT — it always needs polish. Your job is to compare every section of the clone against the original and fix every difference until they're indistinguishable.

**3a. Start the dev server:**
```bash
cd ~/Desktop/{site}-clone && npm install && npm run dev
```

**3b. Missing section audit (FIRST — before any detail work):**

Screenshot the FULL PAGE of both original and clone. Count the major sections:
- Original sections: header, hero, marquee, manifesto, transition, timeline, feature-tabs, use-cases, stats, testimonials, CTA, footer
- Clone sections: count what exists

If ANY section from the original is MISSING in the clone, build it FIRST:
1. Read the extraction data for that section (html-content.json, components.json)
2. Look at the original screenshot to understand the visual design
3. Create the missing component file
4. Add it to page.tsx in the correct position

**Do NOT proceed to detail polish until all sections exist.** Missing sections are the #1 source of fidelity loss.

**3c. Open the original site in Playwright MCP:**
```
browser_navigate → {original-url}
```

**3d. Section-by-section comparison loop:**

For EACH viewport-height section (scroll down one viewport at a time on BOTH sites):

1. **Screenshot the original** at current scroll position using `browser_take_screenshot`
2. **Navigate to the clone** → `browser_navigate → http://localhost:{port}`
3. **Scroll to the same position** → `browser_evaluate → window.scrollTo(0, {same_y})`
4. **Screenshot the clone** at the same scroll position
5. **Read BOTH screenshots** using the Read tool and compare pixel-by-pixel
6. **List EVERY difference** — be exhaustive, not just "looks close enough":

**Detail Checklist (check ALL of these for each section):**
- [ ] Badge/pill colors match? (not gray defaults — check extraction for exact hex)
- [ ] Active indicators sized correctly? (oversized active vs small inactive, not all same size)
- [ ] Decorative SVGs present? (timeline connectors, dividers — not replaced with simple lines)
- [ ] Background colors exact? (check extraction design tokens for exact hex)
- [ ] Font sizes match? (check extraction measurements, not Gemini's guess)
- [ ] Spacing/padding match? (check extraction computed measurements)
- [ ] Images loading? (check public/images/ for the file, fix `<Image>` props if needed)
- [ ] Hover states work? (hover on buttons, cards, links — do they match original?)
- [ ] Auto-cycling/timer animations running? (tabs, carousels — use GSAP pattern from gsap-patterns.md)
- [ ] Scroll animations firing? (scroll the clone — do elements reveal/highlight like the original?)
- [ ] Floating UI elements present? (tooltips, dropdowns, suggestion popups in hero)
- [ ] Border styles match? (rounded corners, border colors, shadow styles)
- [ ] Text content exact? (line breaks, em dashes, special characters)

7. **Fix each difference** by editing the component code directly:
   - Wrong badge color → `style={{ backgroundColor: "#exact-hex" }}`
   - Missing decorative SVG → extract from original HTML or create matching path
   - Wrong indicator size → adjust w-/h- classes (active should be 3-4x inactive)
   - Static grid should be auto-cycling → implement GSAP pattern from gsap-patterns.md
   - Missing hover image preview → add `useState` + `onMouseEnter` + `<Image>`
   - Missing floating UI → add positioned absolute element with proper content

8. **Scroll to next section** and repeat

**3e. Full-page verification pass:**

After fixing all sections, do ONE final full-page comparison:
1. Screenshot original full-page
2. Screenshot clone full-page
3. Read both and confirm overall match

**3f. REPEAT the entire page scan if needed (up to 3 full passes):**
```
Pass 1: Fix major structural differences (layout, missing sections, broken components)
Pass 2: Fix detail differences (colors, sizes, spacing, badges, indicators)
Pass 3: Fix micro differences (shadows, borders, font weights, hover states)
```

**3g. EXIT criteria — declare done ONLY when:**
- Every section has been compared side-by-side with screenshots
- No visible differences remain (or only dynamic content like dates/counters)
- All scroll animations fire at the correct positions
- All hover states match
- All auto-cycling components cycle with correct timing

**CRITICAL:** The goal is 100%. Not 90%. Not "close enough." 100%.
- Do NOT declare "done" after just one pass.
- Do NOT say "looks close enough" or "high fidelity" when differences remain.
- If the original has a rotated orange badge, the clone MUST have a rotated orange badge — not a gray pill.
- If the original has auto-cycling tabs with a progress bar, the clone MUST have auto-cycling tabs — not a static grid.
- If the original has 70%/40/20% stats with testimonials, the clone MUST have them — not just a headline.
- Keep fixing. Keep comparing. Keep iterating. The skill is not done until you cannot tell the difference.

**3h. After visual loop exits, run code quality gate:**
Phase 9.5 automated checks (TypeScript compilation, no placeholders, etc.)

---

## Implementation Quality Rules

These rules are injected into every Gemini prompt. Full details: [implementation-quality.md](references/implementation-quality.md)

### Forbidden in Generated Output

- Emoji as image/icon placeholders → use downloaded assets or extracted SVGs
- Placeholder URLs (unsplash, picsum, placehold.co) → all assets local in public/images/
- Lorem ipsum text → use extracted real content
- Wireframe gray boxes → use real images from asset manifest
- Gratuitous effects not in original (neon glows, gradient text, extra shadows)
- Default shadcn styling without customization to match original
- External font CDN URLs → self-host in public/fonts/
- Hardcoded #000000 unless original uses it

### Animation Implementation (CRITICAL for fidelity)

**When the orchestrator detects GSAP/ScrollTrigger on the original site, the Gemini prompt MUST demand GSAP implementation — NOT CSS + IntersectionObserver substitutes.** This is the #1 source of fidelity loss.

Ready-to-use GSAP code templates for the 3 most common patterns: [gsap-patterns.md](references/gsap-patterns.md)

| Pattern | Template | When to Use |
|---------|----------|-------------|
| Word-by-word scroll reveal | `gsap.fromTo(words, {opacity: 0.15}, {opacity: 1, scrub: 0.5})` | Manifesto/statement sections |
| Auto-cycling tabs + timer bar | `gsap.to({value:0}, {value:100, duration:6, onComplete: cycle})` | Tab systems with progress |
| Sticky scroll timeline | `ScrollTrigger.create({onEnter/onEnterBack: setActive})` | Process/workflow sections |

**CONFLICT RULE:** Never mix GSAP + Framer Motion in the same component.
CSS is acceptable ONLY for: hover transitions, continuous loops, and sites with NO animation library detected.

### Performance Guardrails

- **GPU-only animation:** transform, opacity, filter, clip-path. NEVER animate width/height/top/left/margin
- **prefers-reduced-motion:** Add to globals.css
- **Mobile (pointer: coarse):** Disable parallax, cap particles
- **Cleanup:** Every useEffect with GSAP/IntersectionObserver MUST return cleanup function

### Accessibility Minimum

- prefers-reduced-motion media query in globals.css
- Visible focus rings (never outline: none without replacement)
- aria-live="polite" on dynamically updating regions
- Keyboard-reachable interactive elements

---

## Code Quality Gate (Phase 9.5)

After evaluator passes, run automated code checks. Full details: [verification-phases.md](references/verification-phases.md#phase-95)

### Hard Gate (auto-fix, blocks delivery)

| # | Check | Command | Fix |
|---|-------|---------|-----|
| 0 | TypeScript compiles | `npx tsc --noEmit` | Fix type annotations |
| 1 | No placeholder URLs | `grep -r "unsplash\|picsum\|placeholder" src/` | Replace with assets |
| 2 | No emoji placeholders | `grep -rP '[\x{1F300}-\x{1FFFF}]' src/` | Replace with <img> or SVG |
| 3 | All image assets exist | Verify each `<img src="/images/...">` file | Copy from downloads |

### Soft Gate (warnings in report)

| # | Check | Command | Recommendation |
|---|-------|---------|----------------|
| 4 | Animation tool consistency | No dual gsap + framer-motion imports | Refactor per matrix |
| 5 | prefers-reduced-motion | `grep -r "prefers-reduced-motion" src/` | Add to globals.css |
| 6 | GPU-only properties | No animate width/height/top/left | Use transform |
| 7 | Fonts self-hosted | No fonts.googleapis.com | Download to public/fonts/ |

---

## Reference Files

| When you need... | Read this file | ~Tokens |
|-----------------|----------------|---------|
| Detailed extraction procedures | [extraction-phases.md](references/extraction-phases.md) | ~4K |
| Verification + evaluator details | [verification-phases.md](references/verification-phases.md) | ~3K |
| Implementation quality rules | [implementation-quality.md](references/implementation-quality.md) | ~2K |
| Gemini prompt template | [gemini-prompt-template-v4.md](references/gemini-prompt-template-v4.md) | ~2K |
| GSAP code templates (when GSAP detected) | [gsap-patterns.md](references/gsap-patterns.md) | ~1.5K |

---

## Known Limitations

- **WebGL/Three.js:** 3D elements not fully captured
- **Custom cursors:** Detected but not always replicated
- **Sound/Video:** Media files not cloned (only poster images)
- **Server-side behavior:** Only client-side appearance cloned
- **Authentication flows:** Login screens captured but not functional
- **Dynamic content:** Real-time data shows snapshot values

---

## Usage Examples

### Basic Clone
```
User: /cloning https://stripe.com
Claude: [Runs orchestrator → all phases automated]
        [Sends to Gemini with 3 videos + section close-ups]
        [Spawns evaluator subagent → scores per dimension]
        [Phase 9.5: All checks pass]
        Done! cd ~/Desktop/stripe-clone && npm install && npm run dev
```
