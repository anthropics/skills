# Presentation Aesthetics & Quality Bar

This reference captures the quality standards and aesthetic principles that define a high-quality HTML presentation — distilled from real iteration feedback.

## Table of Contents
1. [The Core Problem with AI-generated Slides](#1-the-core-problem)
2. [Narrative & Story Structure](#2-narrative--story-structure)
3. [Visual Hierarchy & Typography](#3-visual-hierarchy--typography)
4. [Decoration vs. Information](#4-decoration-vs-information)
5. [Diagrams & Visual Content](#5-diagrams--visual-content)
6. [Slide-Level Feedback Patterns](#6-slide-level-feedback-patterns)
7. [Consolidation Principles](#7-consolidation-principles)
8. [Photo & Illustration Usage](#8-photo--illustration-usage)

---

## 1. The Core Problem

The most common failure mode: **slides that look like a website, not a pitch deck.**

Signs of this failure:
- Every element is a card with a border
- Colored pill badges and dot indicators scattered throughout
- Stats displayed as giant isolated numbers with no context
- Section labels ("Section Name") feel bureaucratic, not editorial
- The slide shows WHAT but never WHY

The fix: think of each slide as a page in a story, not a UI wireframe.

---

## 2. Narrative & Story Structure

### Lead with WHY, not WHAT

Every slide should open with a narrative paragraph that answers "Why does this matter?" before showing any data, diagram, or feature list.

**Bad:**
> *[3 stat cards: "10 min", "6+ systems", "78% adverse events"]*

**Good:**
> "Triage nurses spend 10–15 minutes manually assembling patient context from 6+ disconnected systems — ambulance reports on paper, EHRs, wearables, labs, handwritten referrals. The problem isn't a lack of data. It's a lack of interoperability."

Then show the stat cards below as supporting evidence.

### Tell a connected story

Each slide should connect to the next. The narrative arc for a pitch deck typically follows:
1. Problem (the pain) → 2. Solution (what we built) → 3. How it works (architecture) → 4. What it does (features) → 5. Does it work? (metrics) → 6. What's next (roadmap)

Judges should feel pulled forward through the story, not confronted with isolated info dumps.

### Stats inline in narrative

Embed key numbers inside sentences when they support a point:

**Isolated (bad):** A floating card with "87%" in 36px font.

**Contextual (good):** "Our XGBoost model achieves **87% accuracy** on ESI classification — validated against Synthea-generated ground-truth data."

Reserve large stat displays for emphasis on the most important 2–3 numbers per slide, and always pair them with a label that explains what they measure.

---

## 3. Visual Hierarchy & Typography

### Font size discipline

The most common mistake is inverted hierarchy: decorative text is large, informative text is small.

| Right | Wrong |
|-------|-------|
| Body narrative at 16–17px | Body narrative at 13px |
| Card heading at 18px | Pill badge at 16px |
| Eyebrow label at 11px mono | Label at 14px bold |
| Stat number at 28–36px | Everything at 14px |

### The accent italic technique

Use `Instrument Serif` italic for one key word per major heading. This creates editorial sophistication — the contrast between a clean sans-serif and a serif italic signals craft.

```html
<h2>Emergency triage, <span style="font-family:'Instrument Serif',serif;font-style:italic;color:#0D9488;">reimagined.</span></h2>
```

Use sparingly — only for the single most emotionally resonant word in the heading. Never more than one per slide.

### JetBrains Mono for metadata, not content

Mono should only appear in:
- Eyebrow labels (UPPERCASE, 11px, teal, letter-spacing 0.1em)
- Slide numbers
- Code/format tags (FHIR R4, HL7 v2, etc.)
- Technical values (port numbers, file extensions)

Never use mono for body copy or card headings.

### Text color intentionality

- `#0F172A` (text-primary) — headings and critical information
- `#475569` (text-secondary) — body narrative, card descriptions
- `#94A3B8` (text-muted) — labels, captions, slide numbers
- `#0D9488` (accent-teal) — eyebrow labels, inline stats, key highlights

Never use pure black `#000000` for text. The contrast is too harsh on a light background.

---

## 4. Decoration vs. Information

### The decoration tax

Every decorative element costs context window attention. Ask: "Does this element convey information, or just fill space?"

**Costs too much:**
- Colored dots inside pill badges (decorative noise)
- Multiple colored left-borders on adjacent cards (creates visual chaos)
- Box shadows on every card (makes everything equally loud)
- Badge clusters (4+ tags stacked on one slide)

**Worth keeping:**
- A single subtle glow blob at a corner (establishes spatial depth)
- An edge photo at 0.12 opacity (adds atmosphere without competing)
- One teal accent line/divider (marks section transitions)

### Card restraint

All cards should use the same neutral style:
```css
background: rgba(255,255,255,0.5);
border: 1px solid rgba(0,0,0,0.08);
border-radius: 10px;
```

Don't vary the card style within a slide (different colors, different border treatments, different shadows) — it looks undesigned. The content within cards differentiates them; the containers should be invisible infrastructure.

### Pill badges

Use pills for metadata only (standards compliance, version labels, hackathon category). Never use them as primary information carriers. Rules:
- No colored dots inside pills
- All pills should use the same neutral style (subtle border, light bg)
- Maximum 3–4 pills on a slide
- Only on slides where they genuinely add metadata value

---

## 5. Diagrams & Visual Content

### Architecture and pipeline flows must be diagrams

If a slide describes how data flows through a system, it must have a visual diagram — not a list of text cards arranged vertically.

Use inline SVG:
```svg
<svg viewBox="0 0 1136 380">
  <!-- Column containers as <rect> -->
  <!-- Labels as <text> in JetBrains Mono -->
  <!-- Arrows as <line> or <path> in teal -->
</svg>
```

Column structure for pipeline diagrams:
- Each stage = a `<rect>` box with rounded corners
- Stage label = `<text>` in JetBrains Mono, 9px, UPPERCASE, teal
- Component rows = `<rect>` sub-boxes within stage, `<text>` titles + descriptions
- Arrows = `<line>` or `<path>` between stages

### Tech stack slides need real logos

Fetch actual SVG logos from `https://cdn.simpleicons.org/{name}/{hex}`. Never use text tags as substitutes for logos on a tech stack slide — it looks unpolished.

### The Technology Stack slide as the bar

The Technology Stack slide format (logos + name + brief role, grouped by category) is the gold standard for visual density without over-decoration. If judges say "that slide looks great" — replicate that visual approach for other slides.

### When to use illustrations

Use unDraw SVG illustrations (`https://cdn.jsdelivr.net/gh/balazser/undraw-svg-collection@main/svgs/{name}.svg`) as:
- Background watermarks (`opacity: 0.10–0.15`, `position: absolute`, `z-index: 0`)
- Replacements for placeholder "mockup" boxes

CSS to match teal theme:
```css
filter: hue-rotate(160deg) saturate(0.8) brightness(0.95);
```

Never use illustrations at full opacity as primary content. They're atmospheric accents.

---

## 6. Slide-Level Feedback Patterns

These are recurring critique patterns to watch for:

### "This slide reads like a website"
- Cause: Too many distinct card styles, colored borders, pill stacking
- Fix: Unify all card styles, remove colored borders, reduce decoration to 2 elements per slide

### "The stats are floating with no context"
- Cause: Large stat display without narrative setup
- Fix: Add a narrative intro paragraph; embed secondary stats inline in text

### "This looks too text-heavy / boring"
- Cause: All content is text blocks, no diagrams or visual anchors
- Fix: Add one SVG diagram or photo accent; convert a text-only flow to a visual flow

### "This slide is too late in the deck / why am I seeing this now?"
- Cause: Content ordering doesn't follow the narrative arc
- Fix: Ensure the deck follows: Problem → Solution → How → Performance → Future

### "The text is too small / I can't read that"
- Cause: Body copy at 13–14px to fit more content
- Fix: Cut content before reducing font size; 16px minimum for narrative body text

### "This looks like just a vibe — no real substance"
- Cause: Lots of decorative elements, big gradients, not enough informative text
- Fix: Every slide should have a narrative paragraph that could stand alone

### "Why so many slides about the same thing?"
- Cause: Slides padded to hit a target count
- Fix: Consolidate. Three slides on the same topic → one slide with a proper diagram

---

## 7. Consolidation Principles

When you have multiple slides that cover the same conceptual area, consolidate them into one slide with a proper diagram. The right slide count comes from the story, not a target number.

**Consolidation signals:**
- Two consecutive slides with the same eyebrow label
- A slide whose entire content is a subset of the next slide's content
- A slide with only 2–3 elements that could each be a bullet on another slide

**How to consolidate:**
1. Identify the unified concept these slides share
2. Create a single SVG diagram or well-structured layout that covers all the content
3. Write one narrative paragraph that introduces the full concept
4. Use sub-sections within the single slide (not new slides) for detail

Example: "Architecture", "Data Pipeline", and "Semantic Backbone" → one "System Architecture" slide with a full pipeline SVG.

---

## 8. Photo & Illustration Usage

### Unsplash photos

Use only as atmospheric edge accents. Rules:
- `opacity: 0.10–0.15` maximum
- `filter: saturate(0.3–0.5)` to desaturate and prevent color clash
- Always apply a gradient overlay that fades the photo into the slide background
- Position at the edge (right side, 30–35% width) — never center-stage
- Never obscure text

```html
<div style="position:absolute;right:0;top:0;width:420px;height:720px;z-index:0;overflow:hidden;">
  <img src="[url]" style="width:100%;height:100%;object-fit:cover;opacity:0.12;filter:saturate(0.4);">
  <div style="position:absolute;inset:0;background:linear-gradient(90deg,var(--bg-primary) 0%,transparent 40%,transparent 60%,var(--bg-primary) 100%);"></div>
</div>
```

### Photo for specific slides

- **Problem slides:** Hospital corridor, ER, crowded waiting room — establishes the pain context
- **Ambulance/transport slides:** Ambulance exterior, first responder — makes the scenario concrete
- **Clinical slides:** Medical monitor, doctor with tablet — situates the user

### When NOT to add photos

- Architecture slides (diagram is the visual)
- Tech stack slides (logos are the visual)
- Performance slides (charts are the visual)
- Title and closing slides (use gradient/glow instead)
