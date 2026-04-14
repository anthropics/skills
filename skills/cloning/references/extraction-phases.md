# Extraction Phases Reference (v6.0)

Detailed procedures for Phases 0 through 6.5 of the website cloning pipeline.

## Table of Contents
- [Phase 0: Framework Detection](#phase-0-framework-detection)
- [Phase 0.5: Interactive Exploration](#phase-05-interactive-exploration)
- [Phase 1: Enhanced Screenshot Capture](#phase-1-enhanced-screenshot-capture)
- [Phase 1.5: Asset Download & Cataloging](#phase-15-asset-download--cataloging-new)
- [Phase 2: Confidence-Scored Design Tokens](#phase-2-confidence-scored-design-tokens-enhanced)
- [Phase 3: Layout Analysis](#phase-3-layout-analysis-enhanced)
- [Phase 4: Component Semantic Analysis](#phase-4-component-semantic-analysis)
- [Phase 5: SVG & Icon Extraction](#phase-5-svg--icon-extraction-enhanced)
- [Phase 6: Animation Mapping (Runtime Recording)](#phase-6-animation-mapping-rewritten)
- [Phase 6.5: Content & Measurement Extraction](#phase-65-content--measurement-extraction)
- [Appendix: Scripts Reference](#scripts-reference)
- [Appendix: Error Handling](#error-handling)
- [Appendix: v5.0 Extraction Limit Changes](#v50-extraction-limit-changes)

---

## Phase 0: Framework Detection

**Why:** Knowing the framework BEFORE extraction dramatically improves Gemini's output quality.

### 0.1 Run Detection Script

Inject `scripts/detect_frameworks.js` to identify:

**CSS Frameworks:**
- Tailwind CSS (looks for `flex-`, `grid-`, `tw-` classes)
- Bootstrap (looks for `col-`, `btn-`, `container` classes)
- Bulma (looks for `is-primary`, `columns`, `box`)
- Custom (fallback)

**JS Animation Libraries:**
- GSAP + ScrollTrigger (premium sites)
- Framer Motion (React apps)
- AOS - Animate On Scroll (simple reveals)
- Lenis/Locomotive Scroll (smooth scrolling)

**Icon Libraries:**
- Heroicons
- Lucide
- Font Awesome
- Phosphor
- Inline SVGs

**Component Libraries:**
- Radix UI (shadcn)
- Headless UI
- Chakra UI

### 0.2 Use Detection Results

Include in Gemini prompt:
```markdown
### Frameworks Detected:
- CSS: Tailwind CSS
- Animation: GSAP + ScrollTrigger
- Icons: Heroicons + inline SVGs
- Components: Radix UI
```

This tells Gemini exactly what to generate.

---

## Phase 0.5: Interactive Exploration

**Why:** Content hidden behind clicks (dropdowns, modals, accordions, tabs, carousels, mobile menus) is invisible to screenshot capture and JS extraction. This phase uses Playwright's accessibility tree to discover ALL interactive elements, click them open, and screenshot each state.

**Tools Used:** Playwright MCP tools (no custom scripts needed).

### 0.5.1 Navigate + Snapshot Accessibility Tree

1. Use `mcp__plugin_playwright_playwright__browser_navigate` to open the target URL
2. Use `mcp__plugin_playwright_playwright__browser_snapshot` to get the full accessibility tree

The accessibility tree returns every interactive element with its **role**, **label**, and **state**:
- `button[aria-expanded="false"]` = collapsed accordion/FAQ
- `tab` + `tabpanel` = tab system with hidden panels
- `combobox` / `button[aria-haspopup]` = dropdown menus
- `button` labeled "menu"/"hamburger" = mobile navigation
- `button` triggering `dialog` = modal triggers

### 0.5.2 Classify Interactive Elements

From the accessibility tree, identify elements worth exploring:

| Element Type | What to Look For | Action |
|---|---|---|
| Dropdowns/Menus | `combobox`, `menuitem`, `button[aria-haspopup]` | Click to open, screenshot |
| Accordions/FAQs | `button[aria-expanded="false"]` | Click each to expand, screenshot |
| Tabs | `tab` role elements | Click each tab, screenshot each panel |
| Mobile nav | `button` with "menu"/"hamburger"/"nav" label | Resize to mobile, click, screenshot |
| Modals/Dialogs | `button` that triggers `dialog` role | Click trigger, screenshot modal |
| Carousels | `button` with "next"/"previous"/"slide" labels | Click through slides, screenshot each |

### 0.5.3 Interact + Capture States

For each discovered interactive element:

1. `mcp__plugin_playwright_playwright__browser_click` the element
2. `mcp__plugin_playwright_playwright__browser_wait_for` the state change (expanded content, modal fade-in)
3. `mcp__plugin_playwright_playwright__browser_take_screenshot` the new state
4. Save to `/tmp/claude/cloning-{timestamp}/screenshots/interactive/`

**Important:** After capturing each state, click the element again to collapse/close it before moving to the next.

### 0.5.4 Mobile Menu Discovery

1. `mcp__plugin_playwright_playwright__browser_resize` to `{"width": 375, "height": 812}` (iPhone viewport)
2. `mcp__plugin_playwright_playwright__browser_snapshot` to find the hamburger/menu button
3. `mcp__plugin_playwright_playwright__browser_click` the menu button
4. `mcp__plugin_playwright_playwright__browser_take_screenshot` the open mobile nav
5. `mcp__plugin_playwright_playwright__browser_resize` back to `{"width": 1440, "height": 900}` (desktop)

### 0.5.5 Output: Interactive States Manifest

Produce a JSON summary for use in Phase 7 (Gemini Prompt):

```json
{
  "interactive_states": [
    {"type": "dropdown", "trigger": "nav > .dropdown-btn", "screenshot": "interactive/01-dropdown-open.png"},
    {"type": "accordion", "trigger": ".faq-item:nth-child(1)", "screenshot": "interactive/02-faq-1-open.png"},
    {"type": "mobile-menu", "trigger": ".hamburger", "screenshot": "interactive/03-mobile-nav-open.png"},
    {"type": "tab", "trigger": ".pricing-tab-annual", "screenshot": "interactive/04-annual-pricing.png"}
  ]
}
```

### 0.5.6 How This Feeds Downstream

| Downstream Phase | What Phase 0.5 Provides |
|---|---|
| Phase 1 (Screenshots) | Interactive state screenshots supplement the multi-viewport set |
| Phase 6.5a (HTML Content) | Hidden content is now visible for extraction |
| Phase 7 (Gemini Prompt) | Interactive screenshots + manifest attached |
| Phase 9 (Verification) | Can verify interactive states work in the clone too |

### 0.5.7 Skip Conditions

Skip Phase 0.5 if:
- The accessibility tree shows NO interactive elements beyond basic links
- User explicitly requests static-only clone
- Site requires authentication to access interactive features

---

## Phase 1: Enhanced Screenshot Capture

### 1.1 Retina Resolution (2x DPI)

```python
page = browser.new_page(
    viewport={'width': 1440, 'height': 900},
    device_scale_factor=2  # Retina quality
)
```

**Why:** Higher resolution captures subtle gradients, shadows, and text details.

### 1.2 Multi-Viewport Capture

Capture at 4 viewports:

```python
VIEWPORTS = [
    {'name': 'mobile', 'width': 375, 'height': 812},   # iPhone
    {'name': 'tablet', 'width': 768, 'height': 1024},  # iPad
    {'name': 'desktop', 'width': 1440, 'height': 900}, # Standard
    {'name': 'wide', 'width': 1920, 'height': 1080},   # Full HD
]
```

**Why:** Gemini sees responsive behavior and generates proper breakpoints.

### 1.3 Full-Page Screenshot

Use Playwright's native full-page option:

```python
page.screenshot(path='full.png', full_page=True)
```

**Why:** Gemini sees complete layout in ONE image.

### 1.4 Save Structure

```
/tmp/claude/cloning-{timestamp}/screenshots/
  mobile/
    01-full.png
    02-nav-open.png
    03-hover-states.png
  tablet/
    ...
  desktop/
    01-full.png
    02-dropdown-open.png
    03-button-hover.png
    ...
  wide/
    ...
  interactive/
    (from Phase 0.5)
```

---

## Phase 1.5: Asset Download & Cataloging (NEW)

**Why:** Every `<img>`, company logo, avatar photo, and background image is LOST without this phase. Gemini cannot generate real images — it substitutes emoji and wireframe placeholders. This single fix recovers ~20% of fidelity.

### 1.5.1 Extract All Image URLs

Inject via `browser_evaluate` or `evaluate_script`:

```js
(() => {
  const assets = {
    imgs: [...document.querySelectorAll('img')].map(el => ({
      src: el.src,
      alt: el.alt,
      width: el.naturalWidth,
      height: el.naturalHeight,
      context: el.closest('section')?.id ||
               el.closest('[class]')?.className?.split(' ')[0] ||
               'unknown'
    })).filter(img => img.width > 50 || img.height > 50), // Skip tracking pixels

    bgImages: [...document.querySelectorAll('*')].filter(el => {
      const bg = getComputedStyle(el).backgroundImage;
      return bg && bg !== 'none';
    }).map(el => ({
      url: getComputedStyle(el).backgroundImage.match(/url\(['"]?(.*?)['"]?\)/)?.[1],
      element: el.tagName + (el.className ? '.' + el.className.split(' ')[0] : '')
    })).filter(bg => bg.url && !bg.url.startsWith('data:')),

    svgLogos: [...document.querySelectorAll('svg')].filter(el => {
      const rect = el.getBoundingClientRect();
      return rect.width > 20 && rect.width < 200; // Logo-sized SVGs
    }).map((el, i) => ({
      html: el.outerHTML,
      width: el.getBoundingClientRect().width,
      height: el.getBoundingClientRect().height,
      context: el.closest('section')?.id ||
               el.closest('[class]')?.className?.split(' ')[0] ||
               'logo-' + i
    }))
  };
  return JSON.stringify(assets);
})()
```

### 1.5.2 Download Assets to Project Directory

Using Bash `curl` commands:

```bash
ASSET_DIR="/tmp/claude/cloning-{timestamp}/assets"
mkdir -p "$ASSET_DIR/images" "$ASSET_DIR/backgrounds" "$ASSET_DIR/svgs"

# Download each image (1 req/sec to respect rate limits)
# For each img URL from step 1:
curl -sL "https://cdn.example.com/hero-mockup.png" \
  -o "$ASSET_DIR/images/hero-product-mockup.png"
sleep 1

curl -sL "https://cdn.example.com/logo-fedex.svg" \
  -o "$ASSET_DIR/images/logo-fedex.svg"
sleep 1

# For background images:
curl -sL "https://cdn.example.com/orange-swirl.webp" \
  -o "$ASSET_DIR/backgrounds/orange-swirl.webp"
sleep 1
```

**Naming convention:** Use descriptive names based on `alt` text and `context` from extraction:
- `hero-product-mockup.png` (not `img_001.png`)
- `logo-fedex.svg` (not `svg_003.svg`)
- `avatar-gareth-brinn.jpg` (not `photo_007.jpg`)

### 1.5.3 Save SVG Logos as Files

For inline SVGs captured as `outerHTML`:

```bash
# Write each SVG directly to a file
echo '<svg viewBox="0 0 120 30">...</svg>' > "$ASSET_DIR/svgs/logo-company.svg"
```

### 1.5.4 Generate Asset Manifest

Create `asset-manifest.json` mapping original URLs to local paths:

```json
{
  "images": [
    {
      "original_url": "https://cdn.gitbook.com/hero-mockup.png",
      "local_path": "images/hero-product-mockup.png",
      "alt": "GitBook product interface",
      "width": 1200,
      "height": 800,
      "context": "hero-section"
    },
    {
      "original_url": "https://cdn.gitbook.com/logo-fedex.svg",
      "local_path": "images/logo-fedex.svg",
      "alt": "FedEx",
      "width": 80,
      "height": 24,
      "context": "logo-bar"
    }
  ],
  "backgrounds": [
    {
      "original_url": "https://cdn.example.com/orange-swirl.webp",
      "local_path": "backgrounds/orange-swirl.webp",
      "element": "DIV.hero-bg"
    }
  ],
  "svgs": [
    {
      "local_path": "svgs/logo-company.svg",
      "width": 120,
      "height": 30,
      "context": "header"
    }
  ]
}
```

### 1.5.5 How This Feeds Downstream

| Downstream Phase | What Phase 1.5 Provides |
|---|---|
| Phase 7 (Gemini Prompt) | Asset manifest section telling Gemini to use local paths |
| Phase 8 (Post-Processing) | Assets copied to `public/images/` in generated project |
| Phase 9 (Verification) | Real images visible in clone for SSIM comparison |

### 1.5.6 Key Rules

- **Minimum size filter:** Only download images >50px in either dimension (skip tracking pixels, spacers)
- **Rate limiting:** 1 request per second, respect robots.txt
- **Skip data: URIs:** Already inline, no download needed
- **CORS workaround:** If `curl` fails (403/CORS), try fetching through Playwright's page context (same-origin)
- **Deduplication:** If multiple `<img>` tags point to the same URL, download once
- **Max assets:** Cap at 200 total downloads per site (prevent runaway on image-gallery pages)
- **Timeout:** 10 seconds per download, skip on failure (don't block pipeline)

---

## Phase 2: Confidence-Scored Design Tokens (ENHANCED)

**Why:** Not all colors are equally important. Brand colors matter more than generic grays.

### 2.1 Run Enhanced Extraction

Inject `scripts/extract_design_tokens_v4.js`

### 2.2 Confidence Scoring

| Confidence | What It Captures | Example |
|------------|------------------|---------|
| HIGH | Logo, brand, primary CTA, hero elements | `#3b82f6` from `.btn-primary` |
| MEDIUM | Interactive elements, navigation, icons | `#64748b` from `nav a:hover` |
| LOW | Generic UI, backgrounds, subtle borders | `#f1f5f9` from `border-color` |

### 2.3 Use HIGH + MEDIUM Confidence in Prompt

```markdown
### Colors (HIGH + MEDIUM CONFIDENCE):
- Primary: #3b82f6 (from .btn-primary) [HIGH]
- Background: #0f172a (from body) [HIGH]
- Text: #f8fafc (from p, h1-h6) [HIGH]
- Nav hover: #64748b (from nav a:hover) [MEDIUM]
- Card bg: #1e293b (from .card) [MEDIUM]
```

**v5.0 change:** Include LOW confidence colors too (up to 20). Many sites intentionally use pure black/white.

### 2.4 v5.0 Script Enhancements

**Do NOT exclude pure black/white:**
- `rgb(0,0,0)` and `rgb(255,255,255)` are valid design tokens
- Many sites intentionally use pure black text on white backgrounds
- Previous exclusion caused incorrect color reproduction

**Extract additional CSS properties:**
- `text-shadow` (glow effects, depth)
- `filter` (blur, brightness, contrast, saturate)
- `backdrop-filter` (glass morphism effects)
- `mix-blend-mode` (overlay, multiply, screen effects)
- `clip-path` (shape masking, diagonal sections)
- `border-width` + `border-style` (not just border-color)
- `text-decoration-thickness` + `text-underline-offset` (custom link styling)
- `aspect-ratio` (image/card proportions)

---

## Phase 3: Layout Analysis (ENHANCED)

**Why:** Without knowing Grid vs Flexbox, Gemini might generate the wrong layout.

### 3.1 Run Layout Script

Inject `scripts/analyze_layout.js`

### 3.2 What It Captures

**Grid Usage:**
```json
{
  "selector": ".features-grid",
  "columns": "repeat(3, 1fr)",
  "rows": "auto",
  "gap": "24px"
}
```

**Flexbox Usage:**
```json
{
  "selector": ".nav",
  "direction": "row",
  "justify": "space-between",
  "align": "center",
  "gap": "16px"
}
```

**Z-Index Stacking Contexts:**
```json
{
  "selector": ".nav-sticky",
  "zIndex": "50",
  "position": "sticky",
  "reason": "position + z-index"
}
```

**Responsive Breakpoints:**
- Extracts all `@media` queries from stylesheets

### 3.3 v5.0 Enhancement: Lower Spacing Threshold

**Changed:** Section gap detection threshold from >30px to >8px.

Modern designs use 8px, 12px, 16px, 20px, 24px gaps that were previously missed. The old 30px threshold was too aggressive and lost subtle spacing relationships.

---

## Phase 4: Component Semantic Analysis

**Why:** Proper ARIA structure and component patterns improve accessibility and maintainability.

### 4.1 Run Component Script

Inject `scripts/analyze_components.js`

### 4.2 What It Captures

**ARIA Landmarks:**
- header, nav, main, footer, aside
- Elements with explicit `role` attributes

**Component Patterns:**
```json
[
  { "type": "modal", "count": 1, "sample_classes": "fixed inset-0" },
  { "type": "accordion", "count": 1, "sample_classes": "faq-item" },
  { "type": "tabs", "count": 1, "sample_classes": "pricing-tabs" },
  { "type": "carousel", "count": 1, "sample_classes": "testimonials" }
]
```

**Section Structure:**
- Identifies major page sections by ID or `<section>` tags
- Captures headings for context

---

## Phase 5: SVG & Icon Extraction (ENHANCED)

**Why:** Icons are often lost or approximated without explicit extraction.

### 5.1 Run SVG Script

Inject `scripts/extract_svgs.js`

### 5.2 What It Captures

**Inline SVGs (Icons):**
- Only small SVGs (<100px)
- Includes viewBox, paths, fill/stroke
- Stores complete HTML for reproduction

**Icon Library Detection:**
- Identifies icon class patterns
- Notes which library is used

**Sprite References:**
- Captures `<use href="#icon-name">` patterns

### 5.3 v5.0 Enhancement: Raised Limits

**Changed:** Inline SVG capture limit from 30 to 100.

Sites like GitBook, Notion, and Linear have 50+ unique icons. The old 30-icon cap silently discarded icons from later sections of the page.

---

## Phase 6: Animation Mapping (REWRITTEN)

**Why:** The previous approach (`map_animations_v4.js`) used static analysis — parsing source code with regex. This fails on ~70% of modern sites that bundle GSAP/Framer as ES modules (window.gsap is undefined). The new approach records what animations actually DO at runtime, regardless of library.

### 6.1 Strategy: Runtime Recording

Instead of parsing source code, **instrument the page to record animations as they execute**. This captures animations from ANY library (GSAP, Framer Motion, CSS, Web Animations API) because we intercept at the browser API level.

### 6.2 Inject Runtime Recorder

Inject this script BEFORE page load (via `addInitScript` or `browser_evaluate` before navigation):

```js
(() => {
  const recorder = {
    animations: [],
    styleChanges: new Map(),
    scrollSamples: [],

    init() {
      // 1. Intercept Element.animate() (Web Animations API)
      const origAnimate = Element.prototype.animate;
      Element.prototype.animate = function(keyframes, options) {
        recorder.recordAnimation('web-animation', this, keyframes, options);
        return origAnimate.call(this, keyframes, options);
      };

      // 2. Observe style mutations (catches CSS transitions + JS-driven changes)
      this.observer = new MutationObserver(mutations => {
        for (const m of mutations) {
          if (m.type === 'attributes' &&
              (m.attributeName === 'style' || m.attributeName === 'class')) {
            recorder.recordStyleChange(m.target, m.attributeName);
          }
        }
      });
      this.observer.observe(document.body, {
        attributes: true,
        attributeFilter: ['style', 'class'],
        subtree: true
      });

      // 3. Sample scroll-linked state periodically
      const origRAF = window.requestAnimationFrame;
      let frameCount = 0;
      window.requestAnimationFrame = function(cb) {
        return origRAF.call(window, (t) => {
          if (frameCount++ % 10 === 0) {
            recorder.sampleScrollState();
          }
          cb(t);
        });
      };

      // 4. Intercept GSAP if it loads (covers both global and module)
      this.interceptGSAP();
    },

    interceptGSAP() {
      // Watch for gsap being assigned to window
      let _gsap = window.gsap;
      Object.defineProperty(window, 'gsap', {
        get() { return _gsap; },
        set(val) {
          _gsap = val;
          if (val && val.to) {
            const origTo = val.to;
            val.to = function(targets, vars) {
              recorder.recordAnimation('gsap-to', null, vars, {
                targets: String(targets),
                duration: vars.duration,
                ease: vars.ease,
                scrollTrigger: vars.scrollTrigger
              });
              return origTo.apply(val, arguments);
            };
            const origFrom = val.from;
            val.from = function(targets, vars) {
              recorder.recordAnimation('gsap-from', null, vars, {
                targets: String(targets),
                duration: vars.duration,
                ease: vars.ease,
                scrollTrigger: vars.scrollTrigger
              });
              return origFrom.apply(val, arguments);
            };
          }
        },
        configurable: true
      });
    },

    recordAnimation(type, element, keyframes, options) {
      this.animations.push({
        type,
        selector: element ? this.cssPath(element) : (options?.targets || 'unknown'),
        keyframes: JSON.parse(JSON.stringify(keyframes || {})),
        duration: options?.duration,
        easing: options?.easing || options?.ease,
        delay: options?.delay,
        fill: options?.fill,
        scrollTrigger: options?.scrollTrigger || null,
        timestamp: performance.now()
      });
    },

    recordStyleChange(element, attr) {
      const key = this.cssPath(element);
      const current = {
        transform: element.style.transform,
        opacity: element.style.opacity,
        visibility: element.style.visibility,
        clipPath: element.style.clipPath
      };
      // Only record if meaningful animation properties changed
      const hasAnimation = current.transform || current.opacity ||
                           current.clipPath;
      if (hasAnimation) {
        if (!this.styleChanges.has(key)) this.styleChanges.set(key, []);
        this.styleChanges.get(key).push({
          ...current,
          timestamp: performance.now()
        });
      }
    },

    sampleScrollState() {
      const scrollY = window.scrollY;
      if (this.scrollSamples.length === 0 ||
          Math.abs(scrollY - this.scrollSamples[this.scrollSamples.length - 1].y) > 10) {
        this.scrollSamples.push({ y: scrollY, t: performance.now() });
      }
    },

    cssPath(el) {
      if (!el || el === document.body) return 'body';
      const parts = [];
      while (el && el !== document.body) {
        let selector = el.tagName.toLowerCase();
        if (el.id) { selector += '#' + el.id; parts.unshift(selector); break; }
        if (el.className && typeof el.className === 'string') {
          const cls = el.className.trim().split(/\s+/)[0];
          if (cls) selector += '.' + cls;
        }
        parts.unshift(selector);
        el = el.parentElement;
      }
      return parts.join(' > ');
    },

    getResults() {
      // De-duplicate and categorize
      const results = {
        webAnimations: this.animations.filter(a => a.type === 'web-animation'),
        gsapAnimations: this.animations.filter(a => a.type.startsWith('gsap')),
        styleTransitions: Object.fromEntries(
          [...this.styleChanges.entries()]
            .filter(([k, v]) => v.length > 1) // Only elements that changed multiple times
            .map(([k, v]) => [k, { changes: v.length, first: v[0], last: v[v.length - 1] }])
        ),
        scrollLinked: this.scrollSamples.length > 10,
        totalAnimationsRecorded: this.animations.length,
        totalStyleChanges: this.styleChanges.size
      };
      return JSON.stringify(results);
    }
  };

  recorder.init();
  window.__animationRecorder = recorder;
})()
```

### 6.3 Trigger Animations

After the page loads, trigger all animation types:

1. **Scroll animations:** Slowly scroll from top to bottom using Playwright
   ```
   browser_evaluate: window.scrollTo({ top: document.body.scrollHeight, behavior: 'smooth' })
   ```
   Wait 3-5 seconds for scroll to complete.

2. **Hover animations:** Hover key interactive elements identified in Phase 0.5
   ```
   browser_hover on buttons, cards, nav items
   ```

3. **Entrance animations:** Most fire on page load — already captured by the recorder.

### 6.4 Collect Results

```
browser_evaluate: window.__animationRecorder.getResults()
```

This returns a structured JSON with all recorded animations categorized by type.

### 6.5 Categorize for Gemini

Group animations into implementation categories:

| Category | Examples | Implementation |
|----------|----------|----------------|
| Entrance | Fade-in, slide-up on load | CSS @keyframes + animation-delay |
| Scroll-triggered | Elements appearing on scroll | IntersectionObserver + CSS classes |
| Scroll-linked (scrub) | Parallax tied to scroll position | GSAP ScrollTrigger with scrub |
| Hover | Button scale, card lift | CSS :hover transitions |
| Continuous | Spinning loader, pulsing dot | CSS @keyframes infinite |
| Pinned | Section stays while content scrolls | GSAP ScrollTrigger with pin |

### 6.6 Animation Implementation Decision Rule

**Default to CSS `@keyframes` + IntersectionObserver** for:
- Fade-in / slide-up reveals
- Staggered entrance animations
- Simple hover transitions
- Continuous animations

**Only use GSAP if the runtime recorder captured:**
- `scrollTrigger` with `scrub` (parallax tied to scroll position)
- `scrollTrigger` with `pin: true` (pinned sections)
- Complex timeline sequencing with callbacks
- 10+ coordinated animations with specific easing curves

**Why:** GSAP + React 18 Strict Mode breaks animations. `useLayoutEffect` runs twice in dev mode, leaving elements stuck at partial opacity. CSS `@keyframes` are immune to this.

### 6.7 Fallback (ONLY after runtime recorder has been attempted)

**IMPORTANT:** This fallback activates ONLY after the Phase 6 runtime recorder has been injected, triggered (scroll + hover), and returned empty or error results. "Empty" means `totalAnimationsRecorded: 0` AND `totalStyleChanges: 0` AND `scrollLinked: false`. Do NOT skip to this fallback because the site "looks simple" or because you plan to use CSS @keyframes anyway.

If the runtime recorder was attempted and genuinely failed (CSP blocks injection, page crashes, recorder returns error):
1. **RETRY once:** Re-inject the recorder script via a different method (`addInitScript` vs `browser_evaluate`). Some sites block one but not the other.
2. Fall back to Phase 6.5d (JS bundle forensics)
3. Fall back to `map_animations_v4.js` (old Phase 6)
4. If ALL THREE methods fail, default to CSS @keyframes with standard easing — but log `[PHASE 6: ALL METHODS FAILED - defaulting to CSS @keyframes]` in the Phase 7 prompt so Gemini knows animation data is missing.

---

## Phase 6.5: Content & Measurement Extraction

**Why:** Screenshots show what things *look like*, but not the exact pixel values, HTML markup, or font file URLs.

### 6.5a Run HTML Content Extraction (ENHANCED)

Inject `scripts/extract_html_content.js` via `mcp__claude-in-chrome__javascript_tool`.

**Captures per section:**
- Hero heading `innerHTML` (preserves `<br>`, `<span>`, `<em>` tags)
- Navigation links: text + href
- Logo/partner bar: all `<img>` src URLs + alt text
- CTA button labels + link targets
- Footer link columns: heading + links per column
- Product/feature card content: title, subtitle, image src

**v5.0 Enhancement:** Raised limits:
- Cards per section: 8 -> 20 (product/gallery pages have 12+)
- Paragraphs per section: 5 -> 15 (long-form sections get truncated)

### 6.5b Run Computed Measurements Extraction

Inject `scripts/extract_computed_measurements.js` via `mcp__claude-in-chrome__javascript_tool`.

**Captures `getComputedStyle()` + `getBoundingClientRect()` for:**
- `header` -> height, maxWidth, padding (e.g., `h-[52px] max-w-[1496px] px-8`)
- `h1` (hero) -> fontSize, lineHeight, maxWidth, letterSpacing
- Container/wrapper divs -> maxWidth, paddingLeft/Right
- Logo bar -> gap between items, item heights
- Grid sections -> gridTemplateColumns, gap, child aspect-ratio
- Footer -> column count, gap, padding

### 6.5c Run Font Assets Extraction

Inject `scripts/extract_font_assets.js` via `mcp__claude-in-chrome__javascript_tool`.

**Captures from CSSOM:**
- All `@font-face` rules: font-family, src URLs (.woff2), weight ranges, font-display
- Variable font detection (weight range like `100 900`)
- Body `text-rendering`, `font-feature-settings`, `font-kerning`, `font-variation-settings`
- Per-heading `font-variation-settings`

### Phase 6.5d: JS Bundle Animation Forensics

**Why:** ~70% of modern sites bundle GSAP as ES modules.
Phase 6 runtime recording is the primary approach. Phase 6.5d is now the **fallback**.

**Run:** `extract_js_animations.js` via Chrome DevTools `evaluate_script`

**Captures:** ScrollTrigger configs, SplitText usage, easing signatures, stagger patterns,
clipPath animations, timeline compositions, library detection (GSAP/Lenis/Barba).

**v5.0 Enhancement:** Raised tween signature limit from 30 to 100.

**Decision rule:**
- Phase 6 runtime recorder has data -> use Phase 6 data (preferred)
- Phase 6 empty + Phase 6.5d finds configs -> use Phase 6.5d data
- Both empty -> default to CSS @keyframes

---

## Scripts Reference

### Core Extraction Scripts (JavaScript)

| Script | Purpose | Phase | v5.0 Changes |
|--------|---------|-------|-------------|
| `detect_frameworks.js` | Framework/library detection | 0 | - |
| `extract_design_tokens_v4.js` | Confidence-scored design tokens | 2 | No black/white exclusion, +8 CSS properties |
| `analyze_layout.js` | Grid/Flex/Z-index extraction | 3 | Gap threshold: 30px -> 8px |
| `analyze_components.js` | ARIA/component mapping | 4 | - |
| `extract_svgs.js` | Icon extraction | 5 | Limit: 30 -> 100 |
| `record_runtime_animations.js` | **Runtime animation recording** | 6 | **NEW** (replaces map_animations_v4.js) |
| `map_animations_v4.js` | Animation configuration (legacy) | 6 | Fallback only |
| `extract_html_content.js` | Section-level HTML extraction | 6.5a | Cards: 8->20, Paragraphs: 5->15 |
| `extract_computed_measurements.js` | Exact pixel measurements | 6.5b | - |
| `extract_font_assets.js` | @font-face URLs + text rendering | 6.5c | - |
| `extract_js_animations.js` | JS bundle animation forensics | 6.5d | Tweens: 30->100, fallback role |
| `capture_hover_matrix.js` | Hover state capture | Support | Limit: 50->200, +10 selectors |

### Hover Matrix Enhanced Selectors (v5.0)

`capture_hover_matrix.js` now includes these additional selectors:
- `[class*="link"]`
- `[class*="nav"]`
- `[class*="menu"]`
- `[class*="tab"]`
- `[class*="accordion"]`
- `[class*="feature"]`
- `[class*="testimonial"]`
- `li`
- `input`
- `select`

### Python Scripts

| Script | Purpose |
|--------|---------|
| `gemini_api_v4.py` | Enhanced Gemini API integration |
| `generate_prompt_v4.py` | Build v4/v5 prompt structure |
| `record_scroll.py` | Scroll video recording (from v3) |

---

## Error Handling

| Issue | Solution |
|-------|----------|
| Framework detection fails | Falls back to "custom" |
| CORS blocks stylesheets | Uses computed styles |
| CORS blocks image download | Fetch through Playwright page context (same-origin) |
| Too many SVGs (>100) | Captures first 100 icons (was 30 in v4.0) |
| Too many images (>200) | Caps at 200 downloads, prioritizes by size |
| Page requires login | Ask user to log in manually |
| Gemini timeout | Retry with exponential backoff |
| Runtime animation recorder blocked by CSP | Fall back to Phase 6.5d + legacy map_animations_v4.js |
| ImageMagick not installed | Visual comparison via side-by-side screenshots |
| Font download fails | Log warning, Gemini generates with Google Fonts fallback |
| Phase extraction fails on re-run | Include [PHASE X: FAILED] in prompt, Gemini infers from screenshots |
| SSIM never reaches 95% | Exit after 3 iterations with best-effort report |
| Dev server fails to start | Check npm install errors, fix package.json, retry |

---

## v5.0 Extraction Limit Changes

| Script | Property | v4.0 Limit | v5.0 Limit | Reason |
|--------|----------|-----------|-----------|--------|
| `extract_svgs.js` | Inline icons | 30 | 100 | Sites like GitBook have 50+ icons |
| `capture_hover_matrix.js` | :hover rules | 50 | 200 | Complex sites have 100+ hover rules |
| `extract_design_tokens_v4.js` | LOW colors | 5 | 20 | LOW colors still useful for backgrounds |
| `extract_design_tokens_v4.js` | Black/white | Excluded | Included | Many sites use pure black/white intentionally |
| `extract_html_content.js` | Cards per section | 8 | 20 | Product/gallery pages have 12+ cards |
| `extract_html_content.js` | Paragraphs per section | 5 | 15 | Long-form sections were truncated |
| `extract_js_animations.js` | Tween signatures | 30 | 100 | Complex animation pages lost data |
| `analyze_layout.js` | Gap detection threshold | >30px | >8px | Modern designs use 16px, 20px, 24px gaps |
