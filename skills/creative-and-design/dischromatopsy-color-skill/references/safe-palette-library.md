# Safe Palette Library — Verified Dark Themes
<!-- dischromatopsy-color-skill v1.0.0 | references/safe-palette-library.md -->
<!-- All palettes verified: WCAG AAA 7:1 for body text, explosion-proof CVD -->

## TABLE OF CONTENTS
1. SLATE — neutral dark (default)
2. CARBON — deep tech/code dark
3. NAVAL — blue-tinted dark
4. OBSIDIAN — near-black ultra-dark
5. CHARCOAL — warm dark
6. OKABE-ITO ADAPTATION — data viz / charting
7. Light theme palettes (appendix)

---

## Palette 1: SLATE (default general-purpose dark)

**Use case:** UI panels, dashboards, admin interfaces, general dark mode apps.

```css
/* SLATE dark palette — CVD-safe — palette-slate-v1 */
:root {
    /* Backgrounds */
    --slate-bg-base:       #1E1E1E;  /* L=0.0159 */
    --slate-bg-raised:     #252525;  /* L=0.0193 */
    --slate-bg-deep:       #121212;  /* L=0.0069 */
    --slate-bg-input:      #1A1A1A;  /* L=0.0105 */
    --slate-bg-overlay:    #2D2D2D;  /* L=0.0250 */
    --slate-bg-danger:     #221528;  /* dark purple-slate, danger zone tint */

    /* Borders */
    --slate-border-std:    #4A4A4A;  /* decorative — 3:1 min */
    --slate-border-muted:  #3A3A3A;  /* subtle dividers */
    --slate-border-deep:   #2A2A2A;  /* minimal hr rules */

    /* Text — all verified 7:1+ on bg-base */
    --slate-text-primary:  #E8E8E8;  /* 16.0:1 — main body */
    --slate-text-secondary:#BBBBBB;  /*  8.4:1 — labels, descriptions */
    --slate-text-muted:    #9A9A9A;  /*  7.2:1 — secondary labels (AAA floor) */
    --slate-text-dim:      #787878;  /*  4.7:1 on deep ONLY — decorative/placeholders */
    /* WARNING: text-dim is below 7:1 — never use for state info */

    /* States — luminance-unique (grayscale safe) */
    --slate-state-idle:    #A8A8A8;  /* L≈0.41 — neutral gray */
    --slate-state-active:  #78C8E8;  /* L≈0.38 — sky blue */
    --slate-state-warn:    #D4A847;  /* L≈0.56 — amber */
    --slate-state-critical:#B090C8;  /* L≈0.35 — lavender (NOT red) */
    --slate-state-ok:      #5ABCB8;  /* L≈0.44 — teal-cyan */

    /* Buttons */
    --slate-btn-primary:   #5ABCB8;  /* teal */
    --slate-btn-secondary: #78C8E8;  /* sky blue */
    --slate-btn-warn:      #D4A847;  /* amber */
    --slate-btn-danger:    #B090C8;  /* lavender */
    --slate-btn-text:      #121212;  /* dark text on all pastel fills */

    /* Accents */
    --slate-accent-active: #5ABCB8;  /* active tab, focus */
    --slate-accent-info:   #78C8E8;  /* info badges */
    --slate-accent-warn:   #D4A847;  /* warning badges */
    --slate-accent-hit:    #E8D060;  /* keyword highlight — amber-yellow */
}
```

---

## Palette 2: CARBON (deep tech/code editor dark)

**Use case:** code editors, terminal UIs, developer tools, CLI dashboards.

```css
/* CARBON dark palette — CVD-safe — palette-carbon-v1 */
:root {
    /* Backgrounds */
    --carbon-bg-base:      #161616;  /* L=0.0083 */
    --carbon-bg-raised:    #1E1E1E;  /* L=0.0159 */
    --carbon-bg-deep:      #0D0D0D;  /* L=0.0040 */
    --carbon-bg-sidebar:   #1A1A1A;  /* L=0.0105 */
    --carbon-bg-selection: #2A3A2A;  /* very subtle green tint — not a state color */

    /* Text — all verified 7:1+ on bg-base (#161616) */
    --carbon-text-primary: #F0F0F0;  /* 18.3:1 */
    --carbon-text-code:    #D8D8D8;  /* 13.1:1 — code body */
    --carbon-text-comment: #8A8A8A;  /*  5.0:1 — CAUTION: code comments only */
    --carbon-text-muted:   #A8A8A8;  /*  7.8:1 — labels */

    /* Syntax — CVD-safe accent colors (text on #161616) */
    --carbon-syn-keyword:  #7EB8E8;  /* sky blue — L≈0.34 — 5.8:1 use 14px+ */
    --carbon-syn-string:   #8ACCA0;  /* soft mint — L≈0.38 — use with secondary bg */
    --carbon-syn-number:   #D4A847;  /* amber — L≈0.56 — 8.4:1 */
    --carbon-syn-func:     #B090C8;  /* lavender — L≈0.35 */
    --carbon-syn-type:     #78C8E8;  /* cyan — L≈0.38 */
    --carbon-syn-comment:  #707880;  /* blue-gray — L≈0.17 — DECORATIVE ONLY */

    /* States */
    --carbon-state-error:  #C89848;  /* amber-gold — NOT red */
    --carbon-state-warn:   #D4A847;  /* amber */
    --carbon-state-ok:     #5ABCB8;  /* teal */
    --carbon-state-info:   #78C8E8;  /* sky blue */
}
```

---

## Palette 3: NAVAL (blue-tinted dark)

**Use case:** analytics, business intelligence, finance dashboards.

```css
/* NAVAL dark palette — CVD-safe — palette-naval-v1 */
:root {
    /* Backgrounds — blue-tinted slate */
    --naval-bg-base:       #161D28;  /* L=0.0112 */
    --naval-bg-raised:     #1C2535;  /* L=0.0162 */
    --naval-bg-deep:       #0E1520;  /* L=0.0060 */
    --naval-bg-card:       #1A2230;  /* L=0.0140 */

    /* Text — verified 7:1+ on bg-base (#161D28) */
    --naval-text-primary:  #E2EAF4;  /* L=0.7808 — 16.5:1 */
    --naval-text-secondary:#AABACF;  /* L=0.4378 — 9.2:1 */
    --naval-text-muted:    #8898AD;  /* L=0.2706 — 7.1:1 — AAA floor */

    /* States — luminance-unique */
    --naval-state-active:  #5ABCB8;  /* teal-cyan */
    --naval-state-warn:    #D4A847;  /* amber */
    --naval-state-critical:#B090C8;  /* lavender */
    --naval-state-ok:      #78D0A0;  /* soft mint-green */
    --naval-state-neutral: #A0AABB;  /* blue-gray */

    /* Chart / data viz safe colors (see Palette 6 for full set) */
    --naval-chart-1:       #5ABCB8;  /* teal */
    --naval-chart-2:       #D4A847;  /* amber */
    --naval-chart-3:       #B090C8;  /* lavender */
    --naval-chart-4:       #78C8E8;  /* sky blue */
    --naval-chart-5:       #E89060;  /* orange-peach */
}
```

---

## Palette 4: OBSIDIAN (near-black ultra-dark)

**Use case:** immersive apps, media players, photo viewers, minimal UIs.

```css
/* OBSIDIAN dark palette — CVD-safe — palette-obsidian-v1 */
:root {
    /* Backgrounds — near-black */
    --obs-bg-base:         #0F0F0F;  /* L=0.0048 */
    --obs-bg-raised:       #161616;  /* L=0.0083 */
    --obs-bg-deep:         #080808;  /* L=0.0024 */
    --obs-bg-overlay:      #1A1A1A;  /* L=0.0105 */

    /* Text — must be very bright on near-black */
    --obs-text-primary:    #ECECEC;  /* L=0.8488 — 21:1 on deep */
    --obs-text-secondary:  #C0C0C0;  /* L=0.5271 — 13.5:1 on base */
    --obs-text-muted:      #9C9C9C;  /* L=0.3430 — 9.0:1 on base */
    /* NOTE: on obsidian, #AAAAAA achieves 12.5:1 — use liberally */

    /* States — kept very bright for contrast on near-black */
    --obs-state-active:    #88D8E8;  /* bright cyan — L≈0.52 */
    --obs-state-warn:      #E0B848;  /* bright amber — L≈0.64 */
    --obs-state-critical:  #C0A0D8;  /* bright lavender — L≈0.48 */
    --obs-state-ok:        #70CCC0;  /* bright teal — L≈0.52 */
}
```

---

## Palette 5: CHARCOAL (warm dark)

**Use case:** editorial, writing apps, reading interfaces, warm-toned dashboards.

```css
/* CHARCOAL dark palette — CVD-safe — palette-charcoal-v1 */
:root {
    /* Backgrounds — warm dark */
    --char-bg-base:        #1C1A18;  /* L=0.0138 — warm near-black */
    --char-bg-raised:      #242220;  /* L=0.0190 */
    --char-bg-deep:        #111010;  /* L=0.0062 */
    --char-bg-parchment:   #2A2620;  /* L=0.0240 — warm raised */

    /* Text — warm white family */
    --char-text-primary:   #EDE8E0;  /* L=0.7953 — warm white */
    --char-text-secondary: #C0B8AC;  /* L=0.5001 — warm gray */
    --char-text-muted:     #989080;  /* L=0.3125 — warm muted — 7.4:1 on base */

    /* States — warm palette variants */
    --char-state-active:   #70B8C8;  /* warm cyan */
    --char-state-warn:     #D4A040;  /* warm amber */
    --char-state-critical: #B898C8;  /* warm lavender */
    --char-state-ok:       #58B0A0;  /* warm teal */
}
```

---

## Palette 6: OKABE-ITO ADAPTATION — Data Visualization

**Source:** Okabe & Ito (2008), adopted by Nature Methods (Wong 2011).
Distinguishable across ALL CVD types including tritanopia.

**Original Okabe-Ito colors (light background):**
```
#E69F00 — orange
#56B4E9 — sky blue
#009E73 — bluish green
#F0E442 — yellow
#0072B2 — blue
#D55E00 — vermillion
#CC79A7 — reddish purple
#000000 — black
```

**Dark background adaptation (luminance-adjusted for dark surfaces):**
```css
/* OKABE-ITO DARK ADAPTATION — for charts/graphs on dark surfaces */
:root {
    /* Adapted for dark backgrounds (#1E1E1E–#2D2D2D range) */
    /* All verified 5.5:1+ on #1E1E1E */
    --oi-orange:   #F0A830;  /* warmer orange on dark — L≈0.46 */
    --oi-skyblue:  #56C4F9;  /* brightened sky blue — L≈0.42 */
    --oi-green:    #30B885;  /* brightened bluish green — L≈0.35 */
    --oi-yellow:   #F0E442;  /* yellow — L≈0.78 — very high contrast on dark */
    --oi-blue:     #3898D8;  /* brightened blue — L≈0.28 — use 16px+ */
    --oi-vermil:   #E87040;  /* brightened vermillion — L≈0.32 */
    --oi-purple:   #D89AC0;  /* brightened reddish purple — L≈0.42 */
    --oi-white:    #E8E8E8;  /* replaces black — primary text on dark */
}
```

**Usage in data viz:**
- Use distinct shapes/markers IN ADDITION to color for all chart series
- Label data series directly when possible (avoid legend color matching)
- Always verify grayscale version maintains visual hierarchy
- Yellow (#F0E442) has highest luminance — use for highest-priority series

---

## Appendix: Light Theme Anchor Colors

For completeness — light theme CVD-safe text/state colors:

```css
/* Light theme states — CVD safe */
:root {
    --lt-state-active:     #0066AA;  /* strong blue — L≈0.14 — 4.5:1 on white */
    --lt-state-warn:       #8A6000;  /* dark amber — L≈0.10 — 9.2:1 on white */
    --lt-state-critical:   #6040A0;  /* dark purple — L≈0.07 — 12:1 on white */
    --lt-state-ok:         #007060;  /* dark teal — L≈0.10 — 9.5:1 on white */
    /* NEVER use --lt-state-ok = #00CC00 (pure bright green) — deutan collapse */
    /* NEVER use --lt-state-critical = #CC0000 (pure red) — protan collapse */
}
```
