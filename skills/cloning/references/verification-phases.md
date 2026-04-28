# Verification Phases Reference (v6.0)

Detailed procedures for Phases 7 through 9.5 of the website cloning pipeline.

## Table of Contents
- [Phase 7: Enhanced Gemini Prompt](#phase-7-enhanced-gemini-prompt-rewritten)
- [Phase 8: Gemini API + Automated Post-Processing](#phase-8-gemini-api--automated-post-processing-enhanced)
- [Phase 9: Mandatory Verification Loop](#phase-9-mandatory-verification-loop-rewritten)
- [Phase 9.5: Code Quality Gate (NEW in v6.0)](#phase-95-code-quality-gate-new-in-v60)

---

## Phase 7: Enhanced Gemini Prompt (REWRITTEN)

**Why:** The old prompt had critical gaps: HTML truncated at 100KB (missing content), only 3 screenshots sent (missing viewports), Phase 6.5 data sometimes missing entirely. This rewrite enforces completeness.

### 7.1 Phase Completion Gate (MANDATORY)

Before building the prompt, validate ALL extraction data exists:

```
REQUIRED_PHASES = {
  'phase0':     'frameworks'               -> detect_frameworks.js output
  'phase2':     'design_tokens'            -> extract_design_tokens_v4.js output
  'phase3':     'layout'                   -> analyze_layout.js output
  'phase4':     'components'               -> analyze_components.js output
  'phase5':     'svgs'                     -> extract_svgs.js output
  'phase6':     'animations'               -> record_runtime_animations.js output
  'phase6_5a':  'html_content'             -> extract_html_content.js output
  'phase6_5b':  'computed_measurements'    -> extract_computed_measurements.js output
  'phase6_5c':  'font_assets'              -> extract_font_assets.js output
}
```

**If ANY phase is missing:**
1. Re-run that specific extraction script
2. If it fails again, include `[PHASE X: EXTRACTION FAILED - Gemini must infer from screenshots]` in the prompt
3. NEVER silently omit data — Gemini needs to know what's missing

### 7.2 Smart HTML Truncation

**Old behavior:** Cut HTML at 100KB byte limit (mid-element, mid-attribute, losing content).

**New behavior:** Extract meaningful sections, never truncate mid-element:

```
1. <head> complete (meta tags, link tags, style references)
2. <nav> complete (all navigation markup)
3. Each <section> summarized:
   - First heading (h1-h6)
   - First paragraph
   - Structural skeleton (divs with classes, grid/flex containers)
   - Image sources and alt text
   - Button/link text and hrefs
4. <footer> complete
```

**Result:** ~30-50KB of MEANINGFUL HTML that captures the full page structure without truncation artifacts.

### 7.3 Send ALL Screenshots (Not Hardcoded 3)

Organize and attach up to 20 images total:

```
Priority 1 (always include): Viewport screenshots
  - mobile/01-full.png
  - tablet/01-full.png
  - desktop/01-full.png
  - wide/01-full.png

Priority 2 (include if exists): Interactive states (from Phase 0.5)
  - interactive/01-dropdown-open.png
  - interactive/02-faq-open.png
  - interactive/03-mobile-nav.png

Priority 3 (include if exists): Hover states
  - desktop/03-button-hover.png
  - desktop/04-card-hover.png

Priority 4 (include remaining budget): Additional viewports/states
```

### 7.4 Asset Manifest Section (NEW)

Include downloaded assets from Phase 1.5:

```markdown
## DOWNLOADED ASSETS (use these exact paths in components)

### Images (copy to public/images/)
- Hero mockup: /images/hero-product-mockup.png
  Original: https://cdn.gitbook.com/hero.png | 1200x800
- Logo FedEx: /images/logo-fedex.svg
  Original: https://cdn.gitbook.com/fedex.svg | 80x24
- Avatar Gareth: /images/avatar-gareth-brinn.jpg
  Original: https://cdn.gitbook.com/gareth.jpg | 64x64

### Background Images (reference as CSS backgrounds)
- Hero BG: /images/backgrounds/orange-swirl.webp
  Element: div.hero-bg

### Inline SVGs (embed directly in JSX)
- Company logo: [SVG markup provided in Phase 5 data]

IMPORTANT: Use <img src="/images/filename.ext" /> for downloaded assets.
Do NOT use emoji, placeholder text, or wireframe boxes.
Do NOT use external CDN URLs — all assets are local.
```

### 7.5 Structured Measurement Section (ENHANCED)

Add explicit sections with Phase 6.5b data that Gemini MUST use:

```markdown
## COMPUTED MEASUREMENTS (Phase 6.5b - USE THESE EXACT VALUES)

### Header
- height: {extracted}px -> h-[{value}px]
- max-width: {extracted}px -> max-w-[{value}px]
- padding: {extracted}px -> px-[{value/4}] or px-[{value}px]

### Hero Heading (h1)
- font-size: {extracted}px -> text-[{value}px]
- line-height: {extracted} -> leading-[{value}]
- letter-spacing: {extracted}px -> tracking-[{value}px]
- max-width: {extracted}px -> max-w-[{value}px]

### Container
- max-width: {extracted}px -> max-w-[{value}px]
- padding-left/right: {extracted}px -> px-[{value}px]

### Grid Sections
- columns: {extracted} -> grid-cols-{value} or grid-cols-[{value}]
- gap: {extracted}px -> gap-[{value}px]

### Footer
- max-width: {extracted}px -> max-w-[{value}px]
- columns: {count} -> grid-cols-{count}
- padding: {extracted}px -> px-[{value}px]

CRITICAL: These measurements are from getComputedStyle() on the live page.
They are MORE ACCURATE than what you see in screenshots.
If a screenshot LOOKS like 55px but measurement says 45px, USE 45px.
```

### 7.6 Font Assets Section (ENHANCED)

```markdown
## FONT ASSETS (Phase 6.5c - SELF-HOST THESE)

### Fonts to Download
- {FontFamily}: weight range {min}-{max}, variable={true/false}
  Source URL: {woff2_url}
  Download to: public/fonts/{filename}.woff2
  @font-face reference: src: url('/fonts/{filename}.woff2')

### Text Rendering (apply to body)
- text-rendering: {extracted}
- font-feature-settings: {extracted}
- font-kerning: {extracted}
- -webkit-font-smoothing: {extracted}

### Per-Element Font Variation
- h1: font-variation-settings: {extracted}
- h2: font-variation-settings: {extracted}

IMPORTANT: Do NOT use Google Fonts CDN links.
All fonts must be self-hosted in public/fonts/.
CORS blocks external font URLs in development.
```

### 7.7 Complete Prompt Template

```markdown
# CLONE REQUEST: {url}

## SITE ANALYSIS
### Frameworks: {Phase 0 data}
### Layout Method: {Phase 3 data}
### Components: {Phase 4 data}

## DOWNLOADED ASSETS
{Phase 1.5 asset manifest - Section 7.4}

## COMPUTED MEASUREMENTS
{Phase 6.5b data - Section 7.5}

## HTML CONTENT
{Phase 6.5a data - smart-truncated per Section 7.2}

## DESIGN SYSTEM
### Colors: {Phase 2 data - HIGH + MEDIUM + LOW}
### Font Manifest: {Phase 6.5c data - Section 7.6}

## ANIMATIONS
{Phase 6 runtime recording data OR Phase 6.5d fallback}
### Library Decision: {CSS @keyframes / GSAP per Phase 6.6 rule}

## SVG ICONS
{Phase 5 data - up to 100 inline SVGs}

## INTERACTIVE STATES
{Phase 0.5 manifest + screenshots attached}

## VISUAL CONTEXT
{Up to 20 screenshots attached per Section 7.3}

## STRUCTURED HTML
{Smart-truncated HTML per Section 7.2}
```

---

## Phase 7.5: Clone Contract Generation (NEW in v6.0)

**Why:** The evaluator needs an explicit checklist to grade against. Without a contract, verification becomes subjective ("looks about right") instead of objective ("12 sections expected, 11 present = 91.7%").

### 7.5.1 Generate Contract from Extraction Data

After Phase 7.1 completion gate passes, compile the Clone Contract from extraction results:

```json
{
  "url": "https://original-site.com",
  "timestamp": "2024-03-24T15:00:00Z",
  "expected_sections": [
    {"name": "Header/Nav", "type": "navigation", "has_interactive": true},
    {"name": "Hero", "type": "hero", "has_animation": true},
    {"name": "Logo Bar", "type": "social-proof", "expected_images": 15}
  ],
  "expected_assets": {
    "images": 42,
    "fonts": 7,
    "svgs": 12
  },
  "expected_animations": {
    "library": "gsap+scrolltrigger",
    "scroll_triggered": true,
    "hover_states": true,
    "marquee": true,
    "auto_rotation": true
  },
  "expected_interactive": [
    "mobile_nav_toggle",
    "tab_switching",
    "accordion_expand"
  ],
  "thresholds": {
    "layout_fidelity": 90,
    "asset_fidelity": 95,
    "animation_fidelity": 85,
    "content_fidelity": 95,
    "overall": 90
  }
}
```

### 7.5.2 Contract Sources

| Contract Field | Extraction Source |
|---------------|-----------------|
| expected_sections | Phase 4 (component analysis) + Phase 6.5a (HTML content) |
| expected_assets | Phase 1.5 (asset manifest) |
| expected_animations | Phase 6 (runtime recorder) + Phase 0 (framework detection) |
| expected_interactive | Phase 0.5 (interactive exploration) |
| thresholds | Default 90% overall, adjustable per site complexity |

### 7.5.3 Save Location

Save to `/tmp/claude/cloning-{timestamp}/clone-contract.json`. The evaluator subagent reads this file.

---

## Phase 8: Gemini API + Automated Post-Processing (ENHANCED)

### 8.1 Use Optimal Parameters

```python
response = model.generate_content(
    content,
    generation_config={
        "temperature": 1.0,  # Google's recommendation
        "max_output_tokens": 65536,
    }
)
```

### 8.2 Gemini 3 Vision Tips

- Use `media_resolution_high` for detailed image analysis
- Attach screenshots as inline base64 images
- Include video for scroll animations (Gemini can process video)

### 8.3 Post-Processing: Asset Deployment (MANDATORY - NEW)

After Gemini generates code, copy downloaded assets to the project:

```bash
PROJECT_DIR="path/to/generated/project"
ASSET_DIR="/tmp/claude/cloning-{timestamp}/assets"

# 1. Create public/images directory
mkdir -p "$PROJECT_DIR/public/images"

# 2. Copy all downloaded assets
cp -r "$ASSET_DIR/images/"* "$PROJECT_DIR/public/images/" 2>/dev/null
cp -r "$ASSET_DIR/backgrounds/"* "$PROJECT_DIR/public/images/" 2>/dev/null
cp -r "$ASSET_DIR/svgs/"* "$PROJECT_DIR/public/images/" 2>/dev/null

# 3. Verify assets are referenced in generated code
# Search for placeholder patterns and replace with real paths
```

If Gemini generated emoji/placeholder instead of `<img>` tags despite the asset manifest, manually replace them with proper `<img src="/images/...">` tags referencing the downloaded assets.

### 8.4 Post-Processing: Font Self-Hosting (MANDATORY)

This runs AUTOMATICALLY after Gemini output — not manually, not optionally.

```bash
# 1. Read font manifest from Phase 6.5c extraction
FONT_MANIFEST="/tmp/claude/cloning-{timestamp}/extraction/phase6_5c_fonts.json"

# 2. Create fonts directory
mkdir -p "$PROJECT_DIR/public/fonts"

# 3. Download each font file from extracted URLs
# For each font URL in the manifest:
curl -sL "{font_url}" -o "$PROJECT_DIR/public/fonts/{filename}.woff2"

# 4. Rewrite @font-face in globals.css from external to local
# Replace: url('https://fonts.googleapis.com/...')
# With:    url('/fonts/filename.woff2')
# Use sed or manual edit to fix all external font references

# 5. Verify text-rendering properties are in globals.css body
# Ensure: text-rendering, font-feature-settings, font-kerning from Phase 6.5c
```

**Why this is mandatory:** External font URLs in `@font-face` are blocked by CORS. The browser refuses to load fonts from a different origin. Self-hosting is the only reliable approach.

### 8.5 Post-Processing: Measurement Enforcement (MANDATORY - NEW)

After Gemini generates components, automatically cross-check and correct Tailwind values against Phase 6.5b measurements.

**Process:**

1. Load Phase 6.5b extracted measurements
2. For each critical measurement, search generated component files:

```
Measurement: header height = 52px
  Search generated code for: h-[XXpx] in header/nav components
  If found h-[72px] or h-[64px] -> replace with h-[52px]

Measurement: hero h1 font-size = 45px
  Search generated code for: text-[XXpx] in hero heading
  If found text-[55px] or text-[48px] -> replace with text-[45px]

Measurement: container max-width = 1496px
  Search generated code for: max-w-[XXXXpx] in wrapper/container
  If found max-w-[1360px] or max-w-[1440px] -> replace with max-w-[1496px]

Measurement: container padding = 32px
  Search for: px-[XXpx] or px-X in container elements
  Verify px-8 (=32px) or px-[32px]
```

3. Only correct values in the matching component context (don't blindly find-replace across all files)
4. Log all corrections made for Phase 9 verification

**Key measurements to enforce:**
- Header: height, max-width, padding
- Hero h1: font-size, line-height, letter-spacing, max-width
- Container: max-width, padding
- Grid sections: column count, gap
- Footer: max-width, padding, column count
- Logo bar: item count, gap, item heights

### 8.6 Post-Processing: Content Verification (MANDATORY)

Cross-check generated text/markup against Phase 6.5a HTML content:
- Hero heading has exact `<br>` tag placement?
- Logo images use correct local paths from asset manifest (not CDN URLs)?
- Footer links match extraction (correct column headings, link text)?
- Nav links match extraction?

---

## Phase 9: Mandatory Verification Loop (REWRITTEN)

**Why:** The old Phase 9 was "optional" and manual — generate once, hope for the best. Hero left-aligned in original but center-aligned in clone = never caught. This rewrite makes verification mandatory with automated comparison and iterative correction.

### 9.1 Start Clone Dev Server

```bash
cd output-folder
npm install
npm run dev
```

Wait for the dev server to be ready (check for "ready" or "localhost" in output).

### 9.2 Spawn Evaluator Subagent (MANDATORY)

**Why:** Self-evaluation bias causes the generator agent to skip or under-report issues. The evaluator is a SEPARATE agent with no context of how the code was generated.

Spawn a subagent with these instructions:

```
You are a clone fidelity evaluator. Your job is to compare a website clone against its original and grade it honestly.

## Inputs
- Original URL: {original_url}
- Clone URL: http://localhost:{port}
- Clone Contract: {path to clone-contract.json}
- Extraction Summary: {brief summary of what was extracted}

## Your Process
1. Read the Clone Contract to understand what's expected
2. Open the ORIGINAL site — screenshot full page at desktop (1440x900)
3. Open the CLONE site — screenshot full page at same viewport
4. For EACH section listed in the contract:
   a. Screenshot that section on both sites
   b. Compare layout, colors, fonts, spacing, images
   c. Score each of the 4 fidelity dimensions (see below)
5. Test animations: scroll the clone page slowly, check if scroll-triggered animations fire
6. Test interactivity: click dropdowns, tabs, mobile menu — do they work?
7. Check for AI slop: emoji placeholders, generic styling, effects not in original

## 4 Fidelity Dimensions

| Dimension | Weight | What to Check |
|-----------|--------|---------------|
| Layout (30%) | Grid vs Flex correct? Spacing within 5px? Responsive breakpoints? Sections in right order? |
| Assets (25%) | All images from contract present? Correct sizes? No placeholders? Fonts rendering correctly? |
| Animation (25%) | Correct library per contract? Scroll triggers fire? Hover states match? Timing reasonable? |
| Content (20%) | Exact text matches? Links correct? Heading hierarchy? Footer columns complete? |

## Score Calibration

95-100%: Indistinguishable. Only dynamic content differs. All animations + assets present.
85-94%: Correct structure, minor measurement drift (5-10px). Animations present but timing may differ.
70-84%: Structure correct but significant visual differences. Some animations missing or wrong library.
<70%: Major structural issues. Missing sections, wrong layout, broken interactivity.

## Anti-Slop Detection
Flag and deduct points for:
- Emoji where images should be (-10 points per instance)
- Placeholder URLs (-10 points per instance)
- Default component library styling not matching original (-5 points per section)
- Centered layouts where original is asymmetric (-5 points per section)
- Effects (glows, gradients) not present in original (-3 points per instance)

## Output Format
Return a structured report:
- Per-section scores (4 dimensions each)
- Overall weighted score
- Top 5 issues to fix (ranked by impact)
- Anti-slop findings
- PASS (>=90%) or FAIL (<90%) verdict
```

### 9.3 Process Evaluator Feedback

Read the evaluator's report:
- If PASS (>=90%): proceed to Phase 9.5 code quality gate
- If FAIL (<90%): fix the top 3 issues identified, then re-run evaluator (up to 3 iterations)

### 9.4 Correction Loop

```
Iteration 1: Evaluator returns scores + issues
  → Fix top 3 issues from evaluator feedback
  → Re-spawn evaluator

Iteration 2: Evaluator returns updated scores
  → If improved but still <90%, fix remaining issues
  → Re-spawn evaluator

Iteration 3: Final evaluator pass
  → Accept score regardless, report in Final Report
```

### 9.4.5 Fidelity Score Calibration Reference

This calibration is provided to the evaluator subagent (above) and also used to interpret scores in the Final Report:

**95-100% (Excellent):** Indistinguishable from original except dynamic content (dates, counters). All animations present and correctly timed. All assets loaded. Header height matches within 2px. All expected sections from contract present.

**85-94% (Good):** Correct structure with minor measurement drift (5-10px). Animations present but timing may differ slightly (300ms vs 500ms). All assets present. Grid gap or font size off by small amount.

**70-84% (Acceptable):** Structure correct but significant visual differences. Some animations missing or using wrong library (CSS where GSAP expected). Some assets may be placeholder. Hero font size 10px off. 2 images missing from logo bar.

**<70% (Needs Rework):** Major structural issues. Missing sections, wrong layout approach (Flexbox where Grid expected), broken interactivity. Mobile nav doesn't open. Footer missing columns. Needs fundamental rework, not patching.

### 9.5 Iterative Correction Loop

```
IF overall match < 95%:
  1. Identify top 3 worst-matching sections from diff
  2. For each problem section:
     a. Read the current component code
     b. Compare against Phase 6.5b measurements
     c. Compare against Phase 6.5a content
     d. Compare against Phase 1.5 asset manifest
     e. Fix the specific issues:
        - Wrong measurements -> apply Phase 6.5b values
        - Missing images -> add <img> tags with local asset paths
        - Wrong alignment -> match original layout from Phase 3
        - Missing content -> restore from Phase 6.5a
  3. Save changes
  4. Wait for hot-reload
  5. Re-screenshot the fixed sections
  6. Compare again
  7. Repeat up to 3 iterations total
```

### 9.6 Accessibility Tree Comparison

After visual comparison, verify structural correctness:

```
1. Take browser_snapshot of clone at localhost
2. Compare against original's accessibility tree (saved in Phase 0.5)
3. Check:
   - Same number of landmarks (header, nav, main, footer)
   - Same heading hierarchy (h1, h2, h3 order and count)
   - Same navigation link count and text
   - Same number of interactive elements (buttons, dropdowns)
   - Same ARIA roles present
```

### 9.7 Interactive State Verification

If Phase 0.5 captured interactive states:
1. Click each interactive element in the clone
2. Verify it opens/expands/toggles correctly
3. Compare expanded state against Phase 0.5 screenshots

### 9.8 Exit Criteria

The verification loop exits when ANY of these conditions are met:

| Condition | Status |
|-----------|--------|
| Overall SSIM >= 95% | PASS - ship it |
| 3 correction iterations completed | DONE - report final score |
| All per-section matches >= 90% | PASS - acceptable |
| Only remaining issues are dynamic content (dates, counters) | PASS - expected |

### 9.9 Final Report

After verification completes, output a summary:

```
## Clone Verification Report

Original: https://example.com
Clone: localhost:3000

Overall Match: {X}%
Iterations: {N}/3

Per-Section Results:
- Header:     {X}% [PASS/FAIL]
- Hero:       {X}% [PASS/FAIL]
- Features:   {X}% [PASS/FAIL]
- Footer:     {X}% [PASS/FAIL]

Assets: {N}/{total} images present
Fonts: {loaded/total} self-hosted correctly
Interactive: {N}/{total} elements functional

Remaining Issues:
- {list any unresolved discrepancies}
```

---

## Phase 9.5: Code Quality Gate (NEW in v6.0)

**Why:** Phase 9 checks VISUAL fidelity (SSIM screenshots) but not CODE quality. A 95% SSIM score can coexist with placeholder URLs, mixed animation libraries, and layout-thrashing CSS. This gate catches what screenshots cannot.

### 9.5.1 When to Run

**PREREQUISITE:** Phase 9 MUST have executed before Phase 9.5 begins. Specifically:
- The dev server MUST have been started (`npm run dev`)
- At least ONE clone screenshot MUST have been captured
- At least ONE SSIM comparison (or visual side-by-side comparison if ImageMagick unavailable) MUST have been performed
- An SSIM score (or visual match percentage estimate) MUST exist in the report data

If Phase 9 has not run, DO NOT proceed to Phase 9.5 — go back and run Phase 9 first.

After Phase 9 visual verification passes (or after 3 visual correction iterations), run code quality checks on the generated project's source code.

### 9.5.2 Hard Gate Checks (Auto-Fix Required)

These checks MUST pass. If they fail, trigger correction in the Phase 9 iteration loop (counts toward the 3-iteration limit):

**Check 0: TypeScript Compiles (FIRST CHECK — run before all others)**
```bash
npx tsc --noEmit
```
→ MUST return zero errors. If TypeScript errors exist, the project cannot start its dev server and Phase 9 visual verification cannot proceed. Fix: correct type annotations following the TypeScript rules injected into the Gemini prompt (useRef initialization, event handler typing, proper interfaces).

**Check 1: No Placeholder URLs**
```bash
grep -r "unsplash\|picsum\|placeholder\|placehold\|via\.placeholder\|lorempixel\|dummyimage\|lorem\.space" src/
```
→ MUST return empty. Fix: Replace with asset paths from Phase 1.5 manifest.

**Check 2: No Emoji Placeholders**
```bash
grep -rP '[\x{1F300}-\x{1FFFF}]' src/
```
→ MUST return empty (except intentional UI emoji in extracted content from Phase 6.5a). Fix: Replace with `<img>` tags referencing downloaded assets or extracted SVGs.

**Check 3: All Image Assets Exist**
```bash
# For each <img src="/images/..."> in code, verify file exists in public/images/
grep -roh 'src="/images/[^"]*"' src/ | sed 's/src="//;s/"//' | while read f; do
  [ ! -f "public$f" ] && echo "MISSING: $f"
done
```
→ MUST return empty. Fix: Copy missing assets from Phase 1.5 download directory, or re-download.

### 9.5.3 Soft Gate Checks (Report Only)

These checks produce WARNINGS in the final report. They do NOT trigger auto-correction:

**Check 4: Animation Tool Consistency**
```bash
# Per component file: flag dual gsap + framer-motion imports
for f in src/components/*.tsx src/app/**/*.tsx; do
  has_gsap=$(grep -l "from.*gsap\|import.*gsap" "$f" 2>/dev/null)
  has_framer=$(grep -l "from.*framer-motion\|import.*framer-motion" "$f" 2>/dev/null)
  [ -n "$has_gsap" ] && [ -n "$has_framer" ] && echo "MIXED: $f"
done
```
→ Flag: component imports both GSAP and Framer Motion. Recommendation: refactor per Animation Tool Matrix.

**Check 5: prefers-reduced-motion Present**
```bash
grep -r "prefers-reduced-motion" src/ app/
```
→ Flag if zero matches. Recommendation: add `@media (prefers-reduced-motion: reduce)` to globals.css.

**Check 6: GPU-Only Animation Properties**
```bash
grep -rE "animate\(\{[^}]*(width|height|top|left|margin|padding)" src/
grep -rE "\.to\([^)]*\{[^}]*(width|height|top|left|margin|padding)" src/
```
→ Flag violations. Recommendation: replace with transform equivalents (translateX/Y, scaleX/Y).

**Check 7: Fonts Self-Hosted**
```bash
grep -r "fonts\.googleapis\.com\|fonts\.gstatic\.com\|fonts\.bunny\.net" src/ app/ public/
```
→ Flag if matches found. Recommendation: download to public/fonts/ and rewrite @font-face.

### 9.5.4 Report Format

Add to the Phase 9 Final Report:

```
## Code Quality Gate (Phase 9.5)

### Hard Gate (auto-fixed):
- Placeholder URLs: {PASS/FAIL} — {N} found, {N} fixed
- Emoji placeholders: {PASS/FAIL} — {N} found, {N} fixed
- Missing assets: {PASS/FAIL} — {N} missing, {N} resolved

### Soft Gate (warnings):
- Animation tool consistency: {N} components with mixed imports
- prefers-reduced-motion: {PRESENT/MISSING}
- GPU-only properties: {N} violations found
- Font self-hosting: {PASS/N external references}
```

### 9.5.5 Integration with Phase 9 Loop

```
Phase 9 Visual Loop (up to 3 iterations):
  1. Screenshot clone
  2. SSIM comparison
  3. Fix visual issues
  4. Re-screenshot → repeat

After visual loop exits:
  5. Run Phase 9.5 hard gate checks
  6. If hard gate fails AND iterations < 3:
     → Fix issues, re-run visual + code checks
  7. Run Phase 9.5 soft gate checks
  8. Include all results in Final Report
```
