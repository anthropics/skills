# BAD EXAMPLES — Cautionary Case Study: Anonymous CSS Panel Extension
<!-- dischromatopsy-color-skill v1.0.0 | references/bad-examples.md -->
<!-- SOURCE: anonymized real-world CSS from a browser extension panel -->
<!-- All project identifiers removed. Palette version: ANON-001 -->

---

## WARNING: THIS IS A "WHAT NOT TO DO" DOCUMENT

The following is an analysis of a real-world CSS panel extension palette that
contained multiple accessibility failures, despite the developer's stated intent
to be CVD-safe. Studying these failures reveals the most common CVD traps.

---

## 1. The Project's Intent vs. Reality

**Stated color philosophy (from the CSS file header comment):**
> "Dark chalkboard / slate base. Pastel, high-contrast accents.
> NO fluorescent colors. NO red/green dependency (colorblind-safe).
> WCAG AA/AAA contrast ratios observed where feasible."

**Critical failure:** the phrase "where feasible" undermined the entire intent.
Contrast compliance was treated as optional, not mandatory.
This is a design philosophy error, not just a calculation error.

**The developer DID get several things right:**
- Avoided pure red and pure green for state indicators ✓
- Used teal/cyan/peach/lavender instead of red/green ✓
- Variable-based design system (CSS custom properties) ✓
- Dark text on all pastel button fills ✓

**But failed on the most critical point:**
- Did NOT verify that gray text colors met contrast thresholds ✓✗
- Did NOT calculate luminance ratios before choosing text grays ✓✗
- Hardcoded gray values in secondary UI sections bypassing the variable system ✓✗

---

## 2. Specific Failing Pairs

### Failure Type 1: Mid-gray text on dark backgrounds

```
/* ANON PATTERN — FAILURE */
color: #777777;           /* used in badge-off-text, popup footer, status msg */
background: #1A1A1A;      /* deep panel background */
```

**Calculation:**
```
L(#777777) = 0.1329
L(#1A1A1A) = 0.0105
ratio = (0.1329 + 0.05) / (0.0105 + 0.05) = 0.1829 / 0.0605 = 3.02:1
```
**Status: FAIL — WCAG AA requires 4.5:1, WCAG AAA requires 7:1.**

```
/* SAME COLOR ON DIFFERENT BACKGROUND — ALSO FAILURE */
color: #777777;
background: #444444;     /* badge off-state background */
```
**Calculation:**
```
L(#777777) = 0.1329
L(#444444) = 0.0513
ratio = (0.1329 + 0.05) / (0.0513 + 0.05) = 0.1829 / 0.1013 = 1.81:1
```
**Status: CATASTROPHIC FAIL — 1.81:1 is near-zero perceptual contrast.**
For a CVD user relying on luminance only: **these two grays are nearly identical.**

---

### Failure Type 2: Decorative-but-functional dark gray spinner

```
/* ANON PATTERN — FAILURE */
--spin-idle: #555555;     /* spinner dot in idle state */
background: #2D2D2D;      /* panel base surface */
```
**Calculation:**
```
L(#555555) = 0.0854
L(#2D2D2D) = 0.0250
ratio = (0.0854 + 0.05) / (0.0250 + 0.05) = 0.1354 / 0.0750 = 1.81:1
```
**Status: FAIL — The developer marked this as "decorative" to exempt it.**
**However:** the spinner was the PRIMARY state indicator for "engine idle" status.
A decorative exemption is invalid if the element conveys operational state.

---

### Failure Type 3: CSS variable bypassed by hardcoded value

The project defined a CSS custom property:
```css
--ob-text-dim: #999999;  /* raised from #666666 — WCAG AA pass on dark bg */
```

But in the popup styles section of the SAME FILE:
```css
.popup-footer {
    color: #777777;  /* hardcoded — bypasses the corrected variable */
}
```
**The fix was applied to the variable but the hardcoded value was not updated.**
This is a systems failure, not a knowledge failure.
Rule: CSS variables exist precisely to prevent this. All color must reference variables.
Zero hardcoded color literals in any file that uses a design token system.

---

### Failure Type 4: "WCAG AA pass = good enough" mentality

Several text pairs in the project achieved 4.5:1–5.0:1 ratios and were
marked as passing. They technically passed WCAG AA for normal text.

**The problem:**
WCAG AA (4.5:1) was designed as a MINIMUM legal baseline, not a design target.
Research shows WCAG AA math has known false positives: approximately 47% of
WCAG AA "passing" pairs are still inaccessible for users with visual impairments.

For CVD users who CANNOT rely on hue differences, the luminance contrast is the
ONLY signal. For these users, 4.5:1 is grossly insufficient.
The target must be 7:1 (WCAG AAA) for all text that conveys information.

---

## 3. Corrected Versions

### Corrected badge-off text (was #777777 on #444444)

```css
/* BEFORE (FAIL — 1.81:1) */
--badge-off-bg:   #444444;
--badge-off-text: #777777;

/* AFTER (PASS — 5.5:1 AAA on #444444) */
--badge-off-bg:   #444444;
--badge-off-text: #CCCCCC;  /* L=0.6038, ratio=5.5:1 — sufficient for badge (large text) */

/* BETTER AFTER — change background to improve overall:  */
--badge-off-bg:   #2A2A2A;  /* darker base = higher possible contrast */
--badge-off-text: #9A9A9A;  /* L=0.3312, ratio=7.4:1 on #2A2A2A — AAA pass */
```

### Corrected popup footer text (was #777777 on #1A1A1A)

```css
/* BEFORE (FAIL — 3.02:1) */
.popup-footer { color: #777777; }

/* AFTER — reference variable, enforce through design system */
.popup-footer { color: var(--text-muted); }  /* #9A9A9A — 7.2:1 AAA pass */
```

### Corrected idle spinner (was #555555 on #2D2D2D)

```css
/* BEFORE (FAIL — 1.81:1) */
--spin-idle: #555555;

/* AFTER — make it clearly visible OR use icon+text as redundant indicator */
--spin-idle: #787878;   /* 3.9:1 on #2D2D2D — non-text element, 3:1 min */
/* AND pair with text label: "IDLE" — never rely on dot color alone */
```

---

## 4. Lessons

| # | Lesson | Anti-pattern avoided |
|---|--------|---------------------|
| 1 | Contrast is mandatory, not optional | "where feasible" in comments |
| 2 | Never use #555–#888 for text without calculating | Assumed mid-gray passes |
| 3 | ALL color must go through CSS variables | Hardcoded values bypass fixes |
| 4 | Target 7:1 AAA, not 4.5:1 AA | AA = legal minimum, not design target |
| 5 | "Decorative" exemption invalid for state indicators | Spinner = state info |
| 6 | Red-green safe ≠ CVD safe (tritan still at risk) | Partial fix only |
| 7 | Verify the fix was applied everywhere, not just in variables | Partial fix |

---

## 5. What the Project Got Right (to reinforce)

These patterns SHOULD be replicated:
```css
/* GOOD: Variable-based design token system */
--text-primary: #DCDCDC;   /* single source of truth */

/* GOOD: Dark text on pastel button fills */
--btn-text: #1A1A1A;        /* always dark text on pastel — reliable contrast */

/* GOOD: Teal instead of green for success/active */
--btn-engage: #7EC8C8;      /* teal avoids red-green CVD trap */

/* GOOD: Lavender instead of red for critical/danger */
--btn-stop: #C3A8D1;        /* lavender avoids protan collapse */

/* GOOD: Peach/amber instead of yellow for warnings */
--btn-pause: #F4C98A;       /* amber-peach avoids tritan yellow trap */
```

The hue choices were sound. The luminance verification was incomplete.
**Lesson: good hue intent + poor luminance discipline = accessibility failure.**
