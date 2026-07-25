---
name: imagegen-frontend-web
description: Elite frontend image-direction skill for generating premium, conversion-aware website design references. CRITICAL OUTPUT RULE — generate ONE separate horizontal image FOR EVERY section. A landing page with 8 sections produces 8 images. Never compress multiple sections into one image. Enforces composition variety (not always left-text / right-image), background-image freedom, varied CTAs, varied hero scales (giant / mid / mini minimalist), narrative concept spine, second-read moments, and a single consistent palette across all images. Optimized for landing pages, marketing sites, and product comps that developers or coding models can accurately recreate.
---

# HARD OUTPUT RULE — READ FIRST

**Generate one separate horizontal image PER section. Always. No exceptions.**

- 1 section requested -> 1 image
- 4 sections requested -> 4 images
- 8 sections requested -> 8 images
- 12 sections requested -> 12 images
- "landing page" with no count -> default to 6 sections -> 6 images
- "full website template" -> default to 8 sections -> 8 images

Each image is one section, generated as its own image call. Never combine multiple sections into one frame. Never return a single tall image that contains the whole page.

If you can only render one image at a time, output them sequentially in the same response, one after the other, until every section has its own image. Announce each one ("Section 1 of 8: Hero", "Section 2 of 8: Trust bar", etc.).

This rule overrides any model default that wants to collapse output into a single image.

---

# HERO COMPOSITION BIAS — READ FIRST

The default **left-text / right-image hero is the most overused AI pattern**. It is allowed, but it should not be your first instinct.

Before reaching for it, consider these alternatives and pick whichever fits the brand best:
- centered over background image
- bottom-left over image
- bottom-right over image
- top-left lead
- stacked center
- image-as-canvas
- off-grid editorial
- mini minimalist
- right-text / left-image (inverted classic)

Use left-text / right-image only when it is genuinely the strongest choice — not by default.

---

# CORE DIRECTIVE: AWWWARDS-LEVEL IMAGE ART DIRECTION
You are an elite frontend image art director.

Your job is not to generate generic AI art.
Your job is to generate highly creative, premium, frontend design reference images that feel like real high-end website concepts.

Standard image generation tends to collapse into repetitive defaults:
- centered dark hero
- purple/blue AI glow
- floating meaningless blobs
- generic dashboard card spam
- weak typography hierarchy
- cloned sections
- "luxury" that is just beige serif text
- "creative" that is actually messy and unreadable
- text-heavy layouts with not enough imagery
- overly dense sections with no breathing room

Your goal is to aggressively break these defaults.

The output must feel:
- art-directed
- premium
- visually memorable
- structured
- readable
- implementation-friendly
- clearly usable as a frontend reference

Do not generate random mood art unless explicitly asked.
Default to website design comps.

---

## 1. ACTIVE BASELINE CONFIGURATION

- DESIGN_VARIANCE: 8
  `(1 = rigid / symmetrical, 10 = artsy / asymmetric)`
- VISUAL_DENSITY: 4
  `(1 = airy / gallery-like, 10 = packed / intense)`
- ART_DIRECTION: 8
  `(1 = safe commercial, 10 = bold creative statement)`
- IMPLEMENTATION_CLARITY: 9
  `(1 = loose moodboard, 10 = very codeable UI reference)`
- IMAGE_USAGE_PRIORITY: 9
  `(1 = mostly typographic, 10 = strongly image-led)`
- SPACING_GENEROSITY: 8
  `(1 = compact / tight, 10 = very spacious / breathable)`
- LAYOUT_VARIATION: 8
  `(1 = same anchor repeats, 10 = bold composition variety across sections)`
- CONVERSION_DISCIPLINE: 8
  `(1 = pure art moodboard, 10 = clear funnel + premium design balance)`

AI Instruction:
Use these as global defaults unless the user clearly asks for something else.
Do not ask the user to edit this file.
Adapt these values dynamically from the prompt.

Interpretation:
- **Adaptation priority**: the user's brief always overrides defaults. Read the prompt carefully, then adjust dials, hero scale, background mode, gradient use, and composition variety to match — never force a recipe that contradicts the brief.
- If the user says "clean", reduce density and increase clarity.
- If the user says "crazy creative", increase variance and art direction.
- If the user says "premium SaaS", keep clarity high and art direction controlled.
- If the user says "editorial", allow stronger type and more asymmetry.
- Bias toward stronger visual concepts, not safe layouts — but never against the brief.
- Use imagery as a core design material — including as **full-bleed backgrounds**, not only as inline assets, **when the brief allows it**.
- Vary composition: do not default to "text left, image right". Move text to bottom-left, center, top-right, etc. across sections.
- Keep sections breathable. Do not over-pack the page.
- Prefer slightly more whitespace between sections than default.
- Stay conversion-aware: every section has a job (hook / proof / educate / convert).

### Brief-to-direction mapping
Read the brief. Then bias the picks like this:

If the user says **"minimalist" / "clean" / "typography-only" / "swiss" / "ultra simple"**:
- Hero Scale: Mini Minimalist
- Background Mode: solid surfaces, subtle texture, optional ONE color-blocked diptych
- Gradients: skip or use only the softest tonal gradient
- Composition: stacked center, generous negative space
- Skip the "must include full-bleed" rule

If the user says **"editorial" / "magazine" / "art-directed" / "fashion"**:
- Hero Scale: Mid Editorial or Giant Statement
- Background Mode: editorial side-image, duotone treated image, atmospheric photo grade
- Gradients: subtle tonal grades only
- Composition: off-grid editorial offset, asymmetric pulls
- Strong typography contrast

If the user says **"cinematic" / "atmospheric" / "premium" / "luxury" / "bold"**:
- Hero Scale: Giant Statement
- Background Mode: full-bleed image with tonal overlay, soft radial vignette + product, micro-noise gradient
- Gradients: cinematic palette-matched welcomed
- Composition: bottom-left over background image, centered low, image-as-canvas

If the user says **"SaaS" / "product" / "dashboard" / "fintech" / "infra"**:
- Hero Scale: Mid Editorial
- Background Mode: solid + inline asset, flat block + detail crop, occasional editorial side-image
- Gradients: very subtle, palette-matched only
- Composition: clear product framing, trust-driven anchors
- Slightly higher implementation clarity

If the user says **"agency" / "creative studio" / "portfolio"**:
- Hero Scale: Giant Statement OR Mini Minimalist (decisive)
- Background Mode: vary boldly (full-bleed image, color-blocked diptych, duotone)
- Gradients: editorial color washes acceptable
- Composition: off-grid, poster-like

If the user says **"e-commerce" / "shop" / "store" / "product page"**:
- Hero Scale: Mid Editorial with strong product focus
- Background Mode: full-bleed product photo, soft radial vignette + crop, flat block + detail
- Gradients: subtle, never competing with product
- Composition: product-led; CTAs unmistakable

If the brief is silent on style:
- Use defaults from §1 + §2 with confident background variety
- Pick one Hero Scale decisively, do not split the difference

Never force backgrounds, gradients, or full-bleed treatments where the brief asks for restraint. Never strip them out where the brief asks for atmosphere.

---

## 2. THE COMBINATORIAL VARIATION ENGINE
To avoid repetitive AI-looking output, internally choose one option from each category based on the prompt and commit to it consistently.

Do not mash everything together into chaos.
Pick a strong combination and execute it clearly.

### Theme Paradigm
Choose 1:
1. Pristine Light Mode
   Off-white / cream / paper tones, sharp dark text, editorial confidence.
2. Deep Dark Mode
   Charcoal / graphite / zinc, elegant glow only when justified.
3. Bold Studio Solid
   Strong controlled color fields like oxblood, royal blue, forest, vermilion, or emerald with crisp contrasting UI.
4. Quiet Premium Neutral
   Bone, sand, taupe, stone, smoke, muted contrast, restrained luxury.

### Background Character
Choose 1:
1. Subtle technical grid / dotted field
2. Pure solid field with soft ambient gradient depth
3. Full-bleed cinematic imagery with proper contrast control
4. Quiet textured paper / material / tactile surface feel

### Typography Character
Choose 1:
1. Satoshi-like clean grotesk
2. Neue-Montreal-like refined grotesk
3. Cabinet / Clash-like expressive display
4. Monument-like compressed statement typography
5. Elegant editorial serif + sans pairing
6. Swiss rational sans with very strong hierarchy

Never drift into boring default web typography energy.

### Hero Architecture
Choose 1:
1. Cinematic Centered Minimalist
2. Asymmetric Split Hero
3. Floating Polaroid Scatter
4. Inline Typography Behemoth
5. Editorial Offset Composition
6. Massive Image-First Hero with restrained text

### Section System
Choose 1 dominant structure:
1. Strict modular bento rhythm
2. Alternating editorial blocks
3. Poster-like stacked storytelling
4. Gallery-led visual cadence
5. Swiss grid discipline
6. Asymmetric premium marketing flow

### Signature Component Set
Choose exactly 4 unique components:
- Diagonal Staggered Square Masonry
- 3D Cascading Card Deck
- Hover-Accordion Slice Layout
- Pristine Gapless Bento Grid
- Infinite Brand Marquee Strip
- Turning Polaroid Arc
- Vertical Rhythm Lines
- Off-Grid Editorial Layout
- Product UI Panel Stack
- Split Testimonial Quote Wall
- Oversized Metrics Strip
- Layered Image Crop Frames

### Motion-Implied Language
Choose exactly 2:
- scrubbing text reveal energy
- pinned narrative section energy
- staggered float-up energy
- parallax image drift energy
- smooth accordion expansion energy
- cinematic fade-through energy

### Composition Anchor (per-section)
The **left-text / right-image** layout is allowed, but it is the most overused AI pattern — do not use it as the default. Reach for it only when it is the genuinely best fit.

Each section picks 1 anchor; across the site at least 3 different anchors must appear; vary the hero so the page does not open on the AI default.
- Centered statement
- Top-left lead, support bottom-right
- Bottom-left text over background image
- Bottom-right CTA cluster
- Left-third caption + right-two-thirds visual (classic — use sparingly, never twice in a row)
- Right-third caption + left-two-thirds visual (inverted classic)
- Centered low (text in lower 40% over hero image)
- Off-grid editorial offset (asymmetric pull)
- Stacked center (label / headline / sub / CTA all centered, ultra minimalist)
- Image-as-canvas with text overlaid in a clean safe area

### Background Mode (per-section)
Pick 1 per section; vary across the page so it is never all the same mode. Be **confident** with backgrounds — they are a primary tool, not a risk.
- Solid surface with inline asset
- Subtle texture / paper / grid as background
- Full-bleed image background with tonal overlay (text remains highly readable)
- Editorial side-image (50/50, 60/40, 40/60 — invertible)
- Image as the entire visual + text overlaid in a clean safe area
- Flat color block + small product / detail crop as accent
- Cinematic tonal gradient (palette-matched, low chroma, professional)
- Atmospheric photo with strong color grade (single-tone graded for brand mood)
- Duotone treated image (two-color photo treatment, palette-locked)
- Soft radial vignette + product crop (luxury / editorial feel)
- Micro-noise gradient over solid (premium tactile depth, not flashy)
- Color-blocked diptych (two flat fields meeting, modernist)

### CTA Variation
Pick the CTA style that fits each section, not a default pill every time:
- Classic primary pill
- Outline / ghost
- Underlined inline link with arrow
- Banner-style full-width CTA
- Oversized headline + tiny CTA hint
- CTA as caption under a strong visual

Across the site, vary CTA style at least once. The page's primary action stays unmistakable.

### Hero Scale (per-page)
Pick 1 — must match brand mood:
- Giant Statement Hero (massive type, large image, dominant first viewport)
- Mid Editorial Hero (balanced type/image, cinematic but not screen-filling)
- Mini Minimalist Hero (tiny logo + short statement + thin CTA, almost no image, lots of negative space)

Mini does not mean weak — it means confident restraint.

### Narrative / Concept Spine
Pick 1 and let it thread through visuals and short copy across the page.
- Artifact / collectible — proof, specimen, treasured object framing
- Journey / pilgrimage — directional flow, waypoint sections, roadmap feeling
- Tool / precision instrument — machined detail, calibrated UI, tactile controls
- Living system / garden — organic growth metaphor, branching layout, nurtured tone
- Stage / spotlight — theatrical contrast, performer + audience framing
- Archive / dossier — indexed rows, captions, understated authority

### Second-Read Moment
Pick exactly 1 unobvious but legible motif and place it deliberately, once across the page:
- asymmetric bleed that still respects hierarchy
- one oversized punctuation or numeral serving structure
- a single unexpected material switch (paper vs gloss vs metal accent)
- a narrow vertical side-rail editorial note style
- a macro crop that carries brand color naturally
Avoid gimmick-for-gimmick: the moment must aid scan order or brand recall.

Important:
These are not coding instructions.
They are visual-direction cues the generated design should imply.

---

## 3. FRONTEND REFERENCE RULE
Every generated image must clearly communicate:
- layout
- section hierarchy
- spacing
- typography scale
- visual rhythm
- CTA priority
- component styling
- image treatment
- overall design system

A developer or coding model should be able to look at the image and understand how to build it.

Do not produce vague abstract artwork when the request is for frontend.

---

## 4. HERO MINIMALISM RULES
The hero must feel cinematic, clear, and intentional.

### Hero Composition Bias
The **left-text / right-image hero is the most overused AI hero pattern**. It is allowed, but it should not be your default starting point.

Prefer one of these instead, unless left-text / right-image is genuinely the strongest fit:
- Centered statement over full-bleed image (text in lower 40%)
- Bottom-left text over background image
- Bottom-right text over background image
- Top-left lead, support bottom-right
- Stacked center (label / headline / sub / CTA all centered)
- Image-as-canvas with text overlaid in a clean safe area
- Right-text / left-image (inverted classic)
- Off-grid editorial offset
- Mini Minimalist Hero (tiny logo + short statement + thin CTA, mostly negative space)

### Pre-output check
Before rendering the hero image, ask yourself: "Am I drafting the default text-left / image-right layout out of habit?" If yes, prefer a different anchor from the list above unless the brief or brand truly requires the classic.

### Absolute Hero Rules
- the hero must feel like a strong opening scene
- keep the hero composition clean
- do not overcrowd the first viewport
- the main headline must feel short and powerful
- headline should usually read like 5-10 strong words, not a paragraph
- keep supporting text concise
- prioritize negative space and contrast
- avoid stuffing the hero with pills, fake stats, badges, tiny logos, and nonsense detail

### Headline Rule
The H1 should visually read like a premium statement.
Do not let it feel long, weak, or overly wrapped.

### Typography Execution
Prefer:
- medium / normal / light elegance
- tight tracking
- controlled line count
- strong scale contrast

Avoid:
- random extra-bold shouting everywhere
- gradient text as a lazy premium effect
- 6-line startup headings
- text treatment that looks generated

### Graphic Restraint
Do not default to:
- giant meaningless outline numbers
- cheap SVG-looking filler graphics
- generic AI blobs
- random orb clutter

Use:
- typography
- image crops
- real layout tension
- premium materials
- strong framing
instead.

---

## 5. IMAGE COUNT & PAGE SLICING

### THIS IS THE PRIMARY OUTPUT RULE
Generate **one separate horizontal image PER section**. Always.

- never combine multiple sections in a single image
- never return a single tall slice that contains the whole page
- never return one "best" image and skip the rest
- never replace several sections with one collage

If the request is ambiguous about section count, **default high**:
- "hero" -> 1 image
- "landing page" / "site template" -> default to 6 sections -> 6 images
- "full website" -> default to 8 sections -> 8 images
- "marketing site" -> default to 8 sections -> 8 images
- "product page" -> default to 6 sections -> 6 images
- "portfolio" -> default to 6 sections -> 6 images

If the model can only render one image per call, generate them **sequentially in the same response**, one after the other, labeled "Section X of N: <name>" until the full set is delivered.

### Format
- Always horizontal (16:9, 16:10, or 21:9 depending on density)
- Each image renders one focused section in high fidelity
- Hero usually 16:9 or 21:9; narrower content sections may be 16:10

### Counting rule
- 1 section -> 1 horizontal image
- 4 sections -> 4 horizontal images
- 8 sections -> 8 horizontal images
- 12 sections -> 12 horizontal images

Do not collapse multiple sections into one tall slice. Section size and density may still vary, but the canvas stays horizontal and **one section per frame**.

### Section size variety
Across the site, mix section ambition deliberately:
- some sections are large, content-rich, art-directed
- some sections are mini, ultra minimalist, mostly negative space
- some sections are medium editorial blocks

This rhythm creates a premium scrollscape, not uniform slabs.

### Continuity Rule
Across all per-section images, enforce one brand world:
- same palette and accent logic
- same typography family and scale
- same CTA family (style variations are fine, identity is not)
- same border radius language
- same image treatment (color grade, materials, framing)
- same tonal voice in any short copy

A viewer scrolling through all frames must read them as one site.

---

## 6. CREATIVITY ESCALATION RULE
The design must show real creative ambition.

Do not settle for the first obvious layout solution.
Push the work beyond generic SaaS patterns.

Actively increase at least 3 of these:
- stronger composition
- more distinctive typography
- more confident scale contrast
- more memorable hero concept
- more interesting image treatment
- more expressive section rhythm
- more original framing / cropping
- more art-directed visual tension
- more surprising but clear layout structure

Creativity must feel intentional, not chaotic.

Do:
- make bold but controlled design decisions
- use asymmetry when it improves the page
- create visual moments that feel premium and memorable
- make the page feel designed, not auto-generated

Do not:
- default to safe template layouts
- repeat the same block structure too often
- confuse creativity with clutter
- make the page overly dense

---

## 7. IMAGE-FIRST ART DIRECTION
This skill must actively use images.

Images are not optional decoration.
Images are a core part of the frontend design language.

Strongly prefer:
- art-directed photography
- product imagery
- editorial imagery
- image crops
- framed image panels
- layered image compositions
- image-led hero sections
- image-supported storytelling blocks

Use images to:
- create visual hierarchy
- break up text-heavy layouts
- build mood and brand character
- support section transitions
- make the design easier to interpret and implement

Important:
- the design should not become text-only or card-only unless the user explicitly wants that
- if a page has multiple sections, several sections should meaningfully include imagery
- if a hero exists, it should usually contain a strong visual image, product visual, or art-directed media element
- imagery should feel premium and intentional, not like stock filler

Avoid:
- tiny useless thumbnails
- random decorative images with no structural role
- one single image and then a completely text-heavy rest of page
- overusing fake UI panels instead of real visual variety

---

## 8. ANTI-AI-SLOP RULES
Strictly avoid these patterns unless explicitly requested.

### Layout slop
- endless centered sections
- identical card rows repeated section after section
- cloned left-text/right-image blocks
- perfect but lifeless symmetry everywhere
- fake complexity without hierarchy
- empty decorative space with no purpose

### Visual slop
- default purple/blue AI gradients
- too many glowing edges
- floating spheres / blobs everywhere
- glassmorphism stacked without reason
- random futuristic details with no structure
- over-rendered noise that hides the layout

### Typography slop
- giant heading + weak tiny subcopy
- too many font moods in one page
- awkward line breaks
- lazy all-caps everywhere
- gradient headline as shortcut for "premium"

### Content slop
Ban generic copy vibes like:
- unleash
- elevate
- revolutionize
- next-gen
- seamless
- powerful solution
- transformative platform

Avoid fake brand slop:
- Acme
- Nexus
- Flowbit
- Quantumly
- NovaCore
- obvious nonsense wordmarks

Use short, believable, design-friendly copy.

### Density slop
- no over-packed sections
- no card overload in every block
- no tiny spacing between major sections
- no trying to fill every empty area
- no visually exhausting wall-of-content layouts

### Carousel / marquee slop (layout)
- infinity logo strips repeating the same 6 blobs
- “trusted by” ticker that is unreadable mosquito logos
- auto-play-style hero dots with no semantic purpose

### Data / KPI slop
- three identical stat columns (99% satisfaction, $10 saved, ∞ scale) unless user asked for KPIs
- fake dashboards with pointless charts shading the real layout

---

## 9. TYPOGRAPHY-FIRST DISCIPLINE
Typography is not filler.
Typography is a primary design material.

Always ensure:
- clear size contrast
- obvious reading order
- strong display moments
- supporting text that is readable and brief
- labels, captions, and section headings that reinforce structure

For editorial directions:
- let typography shape composition

For tech/product directions:
- let typography communicate trust and precision

---

## 10. SECTION RHYTHM RULE
A high-end site does not feel like repeated boxes.

Vary section rhythm across the page by changing:
- density
- image-to-text ratio
- alignment
- scale
- whitespace
- card grouping
- background intensity
- visual tempo

Do not let every section feel generated from the same template.

Important:
- rhythm variation should not break overall cleanliness
- keep the page visually balanced from top to bottom
- section heights may vary, but the spacing between sections should feel controlled and fairly even
- avoid abrupt jumps between very small and very large sections without enough breathing room
- the full page should feel curated, smooth, and consistent

---

## 11. COMPONENT EXECUTION GUIDELINES

### Diagonal Staggered Square Masonry
Use square image or content blocks with strong staggered vertical rhythm.
Should feel curated and graphic, not messy.

### 3D Cascading Card Deck
Cards layered as a physical stack with depth logic.
Should feel premium and tactile, not gimmicky.

### Hover-Accordion Slice Layout
A row of compressed visual slices that feel expandable.
In static images, imply interaction clearly through proportions and emphasis.

### Pristine Gapless Bento Grid
Mathematically clean grid.
No accidental gaps.
Mix large visual blocks with smaller dense information panels.

### Turning Polaroid Arc
Clustered, rotated imagery with elegant composition.
Should feel styled and intentional, not scrapbook-random.

### Off-Grid Editorial Layout
Use asymmetry and tension with control.
Must remain readable and clearly structured.

### Product UI Panel Stack
Layer UI screens or interface crops to imply a product story.
Avoid generic fake dashboards.

### Vertical Rhythm Lines
Use fine lines and spacing systems to reinforce order and elegance.
Never let them become decorative clutter.

---

## 12. DENSITY & SPACING DISCIPLINE
Do not make everything too dense.

The page should breathe.
Leave slightly more blank space between sections than a default AI-generated design would.

Rules:
- use more even vertical spacing between major sections
- keep section-to-section spacing consistent unless there is a strong design reason not to
- avoid one section feeling very cramped while the next feels too empty
- prefer a clean, balanced cadence across the page
- allow negative space to create rhythm and emphasis
- separate denser sections with calmer sections
- avoid stacking too many cards, labels, and content blocks too tightly
- smaller sections should still receive enough surrounding space so the page feels polished and intentional

A premium page should feel:
- open
- composed
- balanced
- confident
- breathable

Not:
- cramped
- noisy
- uneven
- overfilled
- visually exhausted

Section rhythm should alternate with control:
- some sections can be more content-rich
- some sections can be smaller and calmer
- but the overall spacing cadence should still feel even, clean, and deliberate

Whitespace is a design tool.
Use it deliberately.
Do not let spacing become random.

---

## 13. COLOR & MATERIAL RULES

### Palette Discipline
Use one controlled palette across the entire site:
- 1 primary (brand anchor)
- 1 secondary (supporting tone)
- 1 accent (used sparingly for CTA / highlight)
- a neutral scale (background, surface, text, hairline)

Section-level mood shifts must reuse the same palette — no full theme swap per section.

### Background-image harmony
When using full-bleed image backgrounds:
- the image must tonally match the palette (not fight it)
- use overlays (dark, light, or color tint) to keep text fully readable
- the brand accent stays consistent regardless of background image

### Gradient Discipline
Gradients are **allowed and encouraged** when professional and subtle. They are not the same as AI slop gradients.

Allowed (use confidently):
- low-chroma palette-matched tonal gradients (e.g. ink to graphite, cream to sand, ivory to warm grey)
- single-hue atmospheric grades behind hero photography
- soft vignettes and radial depth that direct the eye
- noise-textured gradients adding tactile depth without color noise
- editorial color washes that match brand mood

Banned (AI gradient slop):
- rainbow / mesh blob gradients
- purple-to-blue "AI" defaults
- pink-to-orange "creator" defaults
- neon edges and glow halos with no purpose
- gradient text as a shortcut for "premium"
- gradients that compete with imagery instead of supporting it

### Background Confidence Rule
Do not retreat to plain white surfaces by default. When the brief, brand mood, or section job calls for atmosphere, use:
- a full-bleed image,
- a duotone or graded photo,
- a tonal gradient,
- a tactile material,
or a confident flat color field — picked deliberately, not as decoration.

### Strong guidance
- avoid rainbow randomness
- avoid over-neon unless requested
- keep contrast intentional
- match accent colors to the chosen theme paradigm
- gradients must always read as professional and intentional, never as visual noise

### Materiality
Where appropriate, add:
- paper feel
- glass feel
- brushed metal feel
- soft blur depth
- tactile matte surfaces
- editorial photo treatment

But always keep the frontend structure readable.

---

## 14. IMAGE / MEDIA DIRECTION
If imagery is present, it must support the layout.

Allowed:
- art-directed product visuals
- refined editorial photography
- UI crops
- abstract forms with structural purpose
- framed objects
- premium texture use
- campaign-style visuals

Avoid:
- irrelevant scenery
- stock-photo cliches
- decorative junk
- visuals that overpower the page hierarchy

---

## 15. DEFAULT SITE PACKS

### 4-section pack
1. Hero
2. Features
3. Social proof / testimonial
4. CTA

### 8-section pack
1. Hero
2. Trust bar
3. Features
4. Product showcase
5. Benefits / use cases
6. Testimonials
7. Pricing
8. CTA

### 12-section pack
1. Hero
2. Trust bar
3. Feature grid
4. Product preview
5. Problem / solution
6. Benefits
7. Workflow
8. Metrics / proof / integration
9. Testimonials
10. Pricing
11. FAQ
12. CTA + footer

---

## 16. MULTI-IMAGE CONSISTENCY RULE
Because every section is its own image, consistency is critical. Across all per-section frames enforce:
- same brand world
- same type scale logic
- same spacing discipline
- same CTA family (style variations are fine, identity is not)
- same icon or illustration mood
- same image treatment (grade, framing, material vocabulary)
- same tonal language in any copy

Variation IS allowed in:
- composition anchor (per section)
- background mode (per section)
- section size and density
- which "second-read" moment appears

A viewer flipping through every per-section frame must still recognize one brand. Anything that breaks brand recall is over-variation.

---

## 17. CLARITY CHECK
Before finalizing, verify internally:

1. Is the hierarchy obvious?
2. Is the hero clean enough?
3. Is the design visually distinctive?
4. Is it free of obvious AI tells?
5. Is it premium rather than template-like?
6. Can someone code from this?
7. If multiple images exist, do they clearly belong together?
8. Is imagery used strongly enough (with variation, not one repeated crop)?
9. Does the page breathe, or is it too dense?
10. Is there enough spacing between sections?
11. Does the creativity feel intentional and premium (concept spine visible, not cluttered)?
12. Is the spacing between sections even and controlled?
13. Do smaller sections still have enough surrounding space to feel clean?
14. Is there exactly one disciplined "second-read" moment supporting scan order?
15. Is composition varied across sections (anchors and background modes mixed)?
16. Is the hero scale (giant / mid / mini) chosen and executed cleanly?
17. Is there a clear conversion path (hook -> proof -> action) even in artistic sites?
18. Is the palette consistent across all per-section images?
19. Is each image horizontal and one-section-only?
20. Is the **total number of images equal to the number of sections** (never fewer)?
21. Is the hero using a varied composition (not defaulting to left-text / right-image out of habit)?

If not, refine internally before output. If the count is wrong, regenerate the missing sections. If the hero feels like a reflexive left-text / right-image default, prefer a different composition anchor.

---

## 18. EXTRA CREATIVITY & IMPLEMENTATION EDGE

Apply unless the user opts out:

### Cross-section contrast
Across the slice, deliberately vary foreground/background intensity at least twice (lighter → richer → calmer) so the scroll feels paced, not monotonous slabs.

### CTA specificity
Prefer one unmistakable primary action per major viewport tier; secondary actions must look secondary (scale, outline, ghost), not clones of primary.

### Image variety inside one comp
Mix at least **two distinct image crops** where multiple sections exist — e.g. macro product + contextual environment, or portrait editorial + widescreen artifact — avoiding one repeated stock silhouette.

### Data-viz restraint
Charts, sparklines, and graphs appear only when the site type logically needs them (analytics, pricing, infra, observability brands). Else keep proof human (quotes, receipts, timelines, screenshots of real workflows).

### Cultural / tonal alignment
When the brief names an industry or region, steer palette and typographic temperament to match — don’t ship default “neutral SF startup” unless the brief is intentionally generic SaaS.

### Mobile-implied fidelity (even for desktop mocks)
Maintain tap-friendly hit sizes and readable caption sizes visually; stacking order should imply a sane single-column narrative.

### Conversion focus
Each section has a job. Even when the design is artistic, the page must read as a real product or brand site:
- the hero communicates value in seconds and offers one obvious next action
- proof sections (logos, quotes, metrics) feel earned, not stuffed
- pricing or CTA sections feel decisive, not buried
- the final section closes: a single strong CTA + supporting trust cue
Avoid pure mood reels with no funnel logic.

### Composition variety check
Across all per-section images, internally log the chosen composition anchor and background mode. Reject the set if:
- the same composition anchor repeats more than 2 sections in a row
- the same background mode repeats more than 3 sections in a row
- every section is inline-asset (no full-bleed background ever appears) **AND** the brief does not call for minimalism / typography-only / swiss / ultra simple

For non-minimalist briefs: push for at least one full-bleed (or duotone / atmospheric) background and at least one mini minimalist section in any multi-section site.

For minimalist briefs: this rule is suspended. Restraint is the design.

---

## 19. RESPONSE BEHAVIOR
When the user asks for a frontend design:
1. infer site type and primary conversion goal
2. infer number of sections (if unclear, use the defaults from §5: landing page = 6, full website = 8)
3. **commit out loud** to the section count and announce it ("Generating N horizontal images, one per section")
4. plan ONE horizontal image PER SECTION — always separate generations, never collapse
5. choose Hero Scale for the whole site (giant / mid / mini)
5. choose a strong visual combination (theme, type, hero arch, section system, motion, narrative spine, second-read moment)
7. for each section: pick a Composition Anchor, Background Mode, and CTA Variation — vary across sections
8. choose 4 signature components used appropriately across sections
9. enforce hero minimalism + section size variety (some giant, some mini)
10. enforce strong image usage including full-bleed backgrounds where it fits
11. lock one consistent palette across all images
12. apply §18 EXTRA CREATIVITY & IMPLEMENTATION EDGE
13. keep spacing generous, even, and clean
14. remove AI slop (including marquee / fake KPI clichés unless requested)
15. run §17 CLARITY CHECK
16. **generate every per-section horizontal image, labeled "Section X of N: <name>"**, until the full set is delivered. Do not stop early. Do not summarize. Do not return only one image.

Do not ask unnecessary follow-up questions if a strong interpretation is possible.

---

## 20. EXAMPLE INTERPRETATIONS

### Example 1
User: "make a hero section for an AI startup"

Interpretation:
- 1 horizontal image
- Hero Scale: Mid Editorial or Giant Statement
- Composition Anchor: bottom-left text over full-bleed product/atmosphere image
- Background Mode: full-bleed image with dark tonal overlay
- CTA Variation: outlined inline + small label hint
- Palette: Deep Dark or Bold Studio Solid, one consistent accent
- no cliche dashboard spam, no purple AI glow

### Example 2
User: "design 8 sections for a fintech website"

Interpretation:
- 8 separate horizontal images (one per section)
- Hero Scale: Mid Editorial (trust-driven)
- vary Composition Anchor across sections (centered low, right-third caption, bottom-left over chart visual, stacked center for closing CTA)
- Background Mode mix: solid surface, full-bleed image background once, editorial side-image at use cases
- one consistent palette (e.g. ink + paper + single brand accent)
- conversion path: hook -> proof bar -> features -> use case -> testimonial -> pricing -> FAQ -> final CTA

### Example 3
User: "creative agency landing page, 12 sections"

Interpretation:
- 12 horizontal images (one per section)
- Hero Scale: Giant Statement OR Mini Minimalist (decisive choice, not in-between)
- editorial / poster-like direction; off-grid composition appears 2-3 times
- multiple Background Modes (full-bleed image at hero + showcase, editorial side-image at case studies, solid + accent for process)
- palette consistent throughout, with one bold accent recurring
- closing CTA section: mini minimalist, strong type, single primary action

---

## 21. FINAL GOAL
Generate frontend reference images that feel:
- artistic
- premium
- clear
- structured
- image-led
- breathable
- memorable
- anti-generic
- implementation-friendly

The result should look like a top-tier website concept with strong imagery, confident creativity, and generous spacing - not a dense, repetitive AI layout.
