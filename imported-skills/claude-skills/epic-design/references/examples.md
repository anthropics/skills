# Real-World Examples Reference

Five complete implementation blueprints. Each describes exactly which techniques to combine, in what order, with key code patterns.

## Table of Contents
1. [Juice/Beverage Brand Launch](#juice-brand)
2. [Tech SaaS Landing Page](#saas)
3. [Creative Portfolio](#portfolio)
4. [Gaming Website](#gaming)
5. [Luxury Product E-Commerce](#ecommerce)

---

## Example 1: Juice/Beverage Brand Launch {#juice-brand}

**Brief:** Premium juice brand. Hero has floating glass. Sections transition smoothly with the product "rising" between them.

**Techniques Used:**
- Loading screen curtain lift
- 6-layer depth parallax in hero
- Floating product between sections (THE signature move)
- Top-down clip birth for ingredients section
- Word-by-word scroll lighting for tagline
- Cascading card stack for flavors
- Split converge title exit

**Section Architecture:**

```
[LOADING SCREEN — brand logo on black, splits open]
     ↓
[HERO — dark purple gradient]
  depth-0: purple/dark gradient background
  depth-1: orange glow blob (brand color)
  depth-2: floating citrus slice PNGs (scattered, decorative)
  depth-3: juice glass PNG (main product, float-loop)
  depth-4: headline "Pure. Fresh. Electric." (split converge on enter)
  depth-5: liquid splash particle PNGs

[FLOATING PRODUCT BRIDGE — glass hovers between sections]

[INGREDIENTS — warm cream/yellow section]
  Entry: top-down clip birth (section drops from top)
  depth-0: warm gradient background
  depth-3: large orange PNG illustration
  depth-4: "Word by word" ingredient callouts (scroll-lit)
  Floating text: ingredient names fade in one by one

[FLAVORS — cascading card stack, 3 cards]
  Card 1: Orange — scales down as Card 2 arrives
  Card 2: Mango — scales down as Card 3 arrives  
  Card 3: Berry — stays full screen
  Each card: full-bleed color + depth-3 bottle + depth-4 title

[CTA — minimal, dark]
  Circle iris expand reveal
  Oversized bleed typography: "DRINK DIFFERENT"
  Simple form/button
```

**Key Code Pattern — The Glass Journey:**
```javascript
// Glass starts in hero depth-3, floats between sections,
// then descends into ingredients section
initFloatingProduct(); // from inter-section-effects.md

// On arrival in ingredients section, glass triggers
// the ingredient words to light up one by one
ScrollTrigger.create({
  trigger: '.ingredients-section',
  start: 'top 50%',
  onEnter: () => {
    initWordScrollLighting(
      '.ingredients-section',
      '.ingredients-tagline'
    );
  }
});
```

**Color Palette:**
- Hero: `#0a0014` (deep purple) → `#2d0b4e`
- Glow: `#ff6b00` (orange), `#ff9900` (amber)
- Ingredients: `#fdf4e7` (warm cream)
- Flavors: Brand-specific per flavor
- CTA: `#0a0014` (returns to hero dark)

---

## Example 2: Tech SaaS Landing Page {#saas}

**Brief:** B2B SaaS product — analytics dashboard. Premium, modern, tech-forward. Animated product screenshots.

**Techniques Used:**
- Window pane iris open (hero reveals from keyhole)
- DJI-style scale-in pin (dashboard screenshot fills viewport)
- Scrub timeline (features appear one by one)
- Curtain panel roll-up (pricing tiers reveal)
- Character cylinder rotation (headline numbers: "10x faster")
- Line clip wipe (feature descriptions)
- Horizontal scroll (integration logos)

**Section Architecture:**

```
[HERO — midnight blue]
  Entry: window pane iris — site reveals from tiny centered rectangle
  depth-0: mesh gradient (dark blue/purple)
  depth-1: subtle grid pattern (CSS, not PNG) with opacity 0.15
  depth-2: floating abstract geometric shapes (low opacity)
  depth-3: dashboard screenshot PNG (float-loop subtle)
  depth-4: headline with CYLINDER ROTATION on "10x"
            "Make your analytics 10x smarter"
  depth-5: small glow dots/particles

[FEATURE ZOOM — pinned section, 300vh scroll distance]
  DJI-style: Dashboard screenshot starts small, expands to full viewport
  Scrub timeline reveals 3 features as user scrolls through pin:
    - Feature 1: "Real-time insights" fades in left
    - Feature 2: "AI-powered" fades in right  
    - Feature 3: "Zero setup" fades in center
  Each feature: line clip wipe on description text

[HOW IT WORKS — top-down clip birth]
  3-step process
  Each step: multi-directional stagger (step 1 from left, step 2 from top, step 3 from right)
  Numbered steps with variable font weight animation

[INTEGRATIONS — horizontal scroll]
  Pin section, logos scroll horizontally
  Speed reactive marquee for "works with everything you use"

[PRICING — curtain panel roll-up]
  3 pricing tiers as curtain panels
  Free → Pro → Enterprise reveals one by one
  Each reveal: scramble text on price number

[CTA — circle iris]
  Dark background
  Bleed typography: "START FREE TODAY"
  Magnetic button (cursor-attracted)
```

---

## Example 3: Creative Portfolio {#portfolio}

**Brief:** Designer/developer portfolio. Bold, experimental, Awwwards-worthy. The work is the hero.

**Techniques Used:**
- Offset diagonal layout for name/title
- Theatrical enter+exit for all section content
- Horizontal scroll for project showcase
- GSAP Flip cross-section for project previews
- Scroll-speed reactive marquee for skills
- Bleed typography throughout
- Diagonal wipe births
- Cursor spotlight

**Section Architecture:**

```
[INTRO — stark black]
  NO loading screen — shock with immediate bold text
  depth-0: pure black (#000)
  depth-4: MASSIVE bleed title — name in 180px+ font
           offset diagonal layout:
           Line 1: "ALEX" — top-left, x: 5%
           Line 2: "MORENO" — lower-right, x: 40%
           Line 3: "Designer" — far right, smaller, italic
  Cursor spotlight effect follows mouse
  CTA: "See Work ↓" — subtle, bottom-right

[MARQUEE DIVIDER]
  Scroll-speed reactive marquee:
  "AVAILABLE FOR WORK  ·  BASED IN LONDON  ·  OPEN TO REMOTE  ·"
  Speed up when user scrolls fast

[PROJECTS — horizontal scroll, 4 projects]
  Pinned container, horizontal scroll
  Each panel: full-bleed project image
               project title via line clip wipe
               brief description via theatrical enter
  On hover: project image scale(1.03), cursor becomes "View →"
  Between projects: diagonal wipe transition

[ABOUT — section peel]
  Upper section peels away to reveal about section
  depth-3: portrait photo (clip-path circle iris, expands to full)
  depth-4: about text — curtain line reveal
  Skills: variable font wave animation

[PROCESS — pinned scrub timeline]
  3 process stages animate through scroll:
  Each stage: top-down clip birth reveals content
  Numbers: character cylinder rotation

[CONTACT — minimal]
  Circle iris expand
  Email address: scramble text effect on hover
  Social links: skew + bounce on scroll in
```

---

## Example 4: Gaming Website {#gaming}

**Brief:** Game launch page. Dark, cinematic, intense. Character reveals, environment depth.

**Techniques Used:**
- Curved path travel (character moves across page)
- Perspective zoom fly-through (fly into the game world)
- Full layered parallax (6 levels deep)
- SVG morph borders (organic landscape edges)
- Cascading card stacks (character select)
- Word-by-word scroll lighting (lore text)
- Particle trails (cursor leaves sparks)
- Multiple floating loops (atmospheric)

**Section Architecture:**

```
[LOADING SCREEN — game-style]
  Loading bar fills
  Logo does cylinder rotation
  Splits open with curtain top/bottom

[HERO — extreme depth parallax]
  depth-0: distant mountains/sky PNG (very slow, heavily blurred)
  depth-1: mid-distance fog layer (slightly blurred, mix-blend: screen)
  depth-2: closer terrain elements (decorative)
  depth-3: CHARACTER PNG — hero character (main float-loop)
  depth-4: game title — "SHADOWREALM" (split converge from sides)
  depth-5: foreground particles — embers/sparks (fast float)
  Cursor: particle trail (sparks follow cursor)

[FLY-THROUGH — perspective zoom, 300vh]
  Pinned section
  Camera appears to fly INTO the game world
  Background rushes toward viewer (scale 0.3 → 1.4)
  Character appears from far (scale 0.05 → 1)
  Title resolves via scramble text

[LORE — word scroll lighting, pinned 400vh]
  Dark section, long block of atmospheric text
  Words light up as user scrolls
  Atmospheric background particles drift slowly
  Character silhouette visible at depth-1 (very faint)

[CHARACTERS — cascading card stack, 4 characters]
  Each card: character art full-bleed
  Character name: cylinder rotation
  Class/description: line clip wipe
  Stats: stagger animate (bars fill on enter)
  Each card buried: scale(0.88), blur, pushed back

[WORLD MAP — horizontal scroll]
  5 zones scroll horizontally
  Zone titles: offset diagonal layout
  Environment art at different parallax speeds

[PRE-ORDER — window pane iris]
  Iris opens revealing pre-order section
  Bleed typography: "ENTER THE REALM"
  Magnetic CTA button
```

---

## Example 5: Luxury Product E-Commerce {#ecommerce}

**Brief:** High-end watch/jewelry brand. Understated elegance. Every animation whispers, not shouts. The product is the hero.

**Techniques Used:**
- DJI-style scale-in (product fills viewport, slowly)
- GSAP Flip (watch travels from hero to detail view)
- Section peel reveal (product details peel open)
- Masked line curtain reveal (all body text)
- Clip-path section birth (materials section)
- Floating product between sections
- Subtle parallax (depth factors halved for elegance)
- Bleed typography (collection names)

**Section Architecture:**

```
[HERO — pure white or cream]
  No loading screen — immediate elegance
  depth-0: pure white / soft cream gradient
  depth-1: VERY subtle warm glow (opacity 0.2 only)
  depth-2: minimal geometric line decoration (thin, opacity 0.3)
  depth-3: WATCH PNG — centered, generous space, slow float (14s loop, tiny movement)
  depth-4: brand name — thin weight, large tracking
           "Est. 1887" — tiny, centered below
  Parallax factors reduced: depth-3 factor = 0.3 (elegant, not dramatic)

[PRODUCT TRANSITION — GSAP Flip]
  Watch morphs from hero center to detail view (left side)
  Detail text reveals via masked line curtain (right side)
  Flip duration: 1.4s (luxury = slow, unhurried)

[MATERIALS — clip-path section birth]
  Cream/beige section
  Product rises up through the section boundary
  Material close-ups: stagger fade in from bottom (gentle)
  Text: curtain line reveal (one line at a time, 0.2s stagger)

[CRAFTSMANSHIP — top-down clip birth, then peel]
  Section drops from top (elegant, not dramatic)
  Video/image of watchmaker — DJI scale-in at reduced intensity
  Text: word-by-word scroll lighting (VERY slow, meditative)

[COLLECTION — section peel + horizontal scroll]
  Peel reveals horizontal scroll gallery
  4 watch variants scroll horizontally
  Each: full-bleed product + minimal text (clip wipe)

[PURCHASE — circle iris (small, elegant)]
  Circle opens from center, but slowly (2s duration)
  Minimal layout: price, materials, add to cart
  CTA: subtle skew + bounce (barely perceptible)
  Trust signals: line-by-line curtain reveal
```

---

## Combining Patterns — Quick Reference

These combinations appear most often across successful premium sites:

**The "Product Hero" Combination:**
Floating product between sections + Top-down clip birth + Split converge title + Word scroll lighting

**The "Cinematic Chapter" Combination:**
Pinned sticky + Scrub timeline + Curtain panel roll-up + Theatrical enter/exit

**The "Tech Premium" Combination:**
Window pane iris + DJI scale-in + Line clip wipe + Cylinder rotation

**The "Editorial" Combination:**
Bleed typography + Offset diagonal + Horizontal scroll + Diagonal wipe

**The "Minimal Luxury" Combination:**
GSAP Flip + Section peel + Masked line curtain + Reduced parallax factors
