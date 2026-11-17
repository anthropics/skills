---
name: presentation-chef
description: "Convert any content into a stunning Apple Keynote-style HTML presentation. Takes markdown, text descriptions, or structured data and generates a single self-contained .html file with cinematic animations, glassmorphism, and premium design. Inspired by ChronicleHQ."
license: Complete terms in LICENSE.txt
---

# Presentation Chef

Generate cinematic, Apple Keynote-style HTML presentations from any content. Single self-contained .html file with zero dependencies.

<HARD-GATE>
You MUST gather all inputs interactively using AskUserQuestion before generating any HTML. Do NOT skip the input gathering phase. Do NOT generate a presentation without knowing the content, theme, and design preferences.
</HARD-GATE>

## Process

Follow these steps exactly:

### Step 1: Gather Content

Ask the user for their content source using AskUserQuestion:

```
AskUserQuestion:
  question: "What content should I turn into a presentation?"
  header: "Content"
  options:
    - label: "Paste or describe it"
      description: "I'll type/paste content or describe what I want in the presentation"
    - label: "Read from a file"
      description: "I have a markdown file, text file, or other document to convert"
    - label: "Generate from topic"
      description: "Give me a topic and I'll create both content and design"
  multiSelect: false
```

If the user selects "Read from a file", ask for the file path and use the Read tool to get the content.
If the user selects "Generate from topic", ask what the topic is and what audience/purpose it serves.
If the user pastes content, analyze it to understand its structure.

### Step 2: Analyze Content & Suggest Theme

After receiving content, analyze it to determine:
- **Content type**: pitch deck, portfolio, product launch, educational, report, personal story, etc.
- **Tone**: professional, creative, technical, casual, dramatic
- **Slide count**: how many slides the content naturally breaks into

Then present theme options interactively:

```
AskUserQuestion:
  question: "What visual theme should the presentation use?"
  header: "Theme"
  options:
    - label: "Dark Cinematic (Recommended)"
      description: "[AI reasoning why this fits the content]. Pure black bg, ambient orbs, glassmorphism cards, Apple blue/purple accents"
      markdown: |
        DARK CINEMATIC
        ──────────────────────────────
        Background:  #000000 (pure black)
        Text:        #ffffff / #86868b
        Accent 1:    #0071e3 (Apple blue)
        Accent 2:    #a855f7 (purple)
        Warm:        #ff6723 (orange)
        Success:     #30d158 (green)

        Effects:     Ambient orbs, grain overlay
                     Glassmorphism cards
                     Gradient text on headlines

        Font:        SF Pro / system sans-serif
        Animations:  Cinematic (900ms, spring easing)
    - label: "Light Minimal"
      description: "Clean, Chronicle-style white canvas with bold typography and single accent color"
      markdown: |
        LIGHT MINIMAL
        ──────────────────────────────
        Background:  #ffffff / #fafafa
        Text:        #1d1d1f / #86868b
        Accent:      #0071e3 (or content-matched)
        Border:      #e5e5e5

        Effects:     Subtle shadows, no orbs
                     Clean card borders
                     Understated elegance

        Font:        Geist / clean geometric sans
        Animations:  Smooth (600ms, ease-out)
    - label: "Warm Editorial"
      description: "Magazine-style warmth with serif typography and rich earth tones"
      markdown: |
        WARM EDITORIAL
        ──────────────────────────────
        Background:  #1a1210 / #f5efe8
        Text:        #f5efe8 / #a89585
        Accent:      #e8734a (coral)
        Secondary:   #c4956a (warm gold)

        Effects:     Warm ambient glow
                     Paper-like texture
                     Editorial layouts

        Font:        Playfair Display + Source Sans
        Animations:  Elegant (800ms, smooth)
    - label: "Neon Cyberpunk"
      description: "High-energy tech aesthetic with neon accents on deep dark backgrounds"
      markdown: |
        NEON CYBERPUNK
        ──────────────────────────────
        Background:  #0a0a1a / #0d1117
        Text:        #e0e0ff / #6b7280
        Accent 1:    #00f0ff (cyan)
        Accent 2:    #ff00aa (magenta)
        Glow:        #7c3aed (purple)

        Effects:     Neon glow borders
                     Scanline overlay
                     Matrix-style grid bg

        Font:        JetBrains Mono + Space Grotesk
        Animations:  Snappy (500ms, sharp easing)
  multiSelect: false
```

**IMPORTANT**: Customize the recommendation text based on the actual content analyzed. Don't use generic descriptions. For example: "Since this is a startup pitch, Dark Cinematic will make your numbers feel impactful and your product feel premium."

### Step 3: Customize Design

Ask about specific design preferences:

```
AskUserQuestion:
  question: "Any design customizations?"
  header: "Customize"
  options:
    - label: "Use defaults"
      description: "The theme preset looks great as-is, no changes needed"
    - label: "Custom accent color"
      description: "I want to use a specific brand color as the primary accent"
    - label: "Custom fonts"
      description: "I want specific fonts (e.g., Google Fonts or system fonts)"
    - label: "Multiple customizations"
      description: "I have specific requirements for colors, fonts, or effects"
  multiSelect: false
```

If the user wants customizations, ask follow-up questions one at a time about each customization.

### Step 4: Map Content to Slides

Analyze the content and map it to the appropriate slide types. Present the slide plan:

```
AskUserQuestion:
  question: "Here's my proposed slide structure. Does this look right?"
  header: "Structure"
  options:
    - label: "Looks perfect"
      description: "Generate the presentation with this structure"
    - label: "Adjust order"
      description: "I want to reorder some slides"
    - label: "Add/remove slides"
      description: "I want to add or remove specific slides"
    - label: "Different approach"
      description: "I want a different overall structure"
  multiSelect: false
```

Before asking, present the slide plan as a numbered list in your message text. Example:
```
Slide 1: Hero — "Company Name" + tagline
Slide 2: Stats — 3 key metrics with count-up
Slide 3: Chapter — "The Problem"
Slide 4: Content Card — Problem description
...
```

### Step 5: Ask Output Location

```
AskUserQuestion:
  question: "Where should I save the presentation?"
  header: "Output"
  options:
    - label: "Current directory"
      description: "Save as presentation.html in the current working directory"
    - label: "Custom path"
      description: "I'll specify the exact file path and name"
    - label: "Desktop"
      description: "Save to ~/Desktop/ for easy access"
  multiSelect: false
```

### Step 6: Generate the Presentation

Generate a single self-contained .html file following the design system below. Use the Write tool to save it.

After saving, tell the user the file path and suggest opening it in a browser.

---

## Design System Reference

When generating the HTML presentation, follow these specifications exactly.

### Document Structure

```html
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>[Presentation Title]</title>
  <style>/* ALL CSS INLINE */</style>
</head>
<body>
  <!-- Loading Screen -->
  <!-- Grain Overlay (if dark theme) -->
  <!-- Progress Bar -->
  <!-- Navigation Dots -->
  <!-- Keyboard Hint -->
  <!-- Speaker Notes Sidebar -->
  <!-- Controls Bar (Notes T, PDF P) -->
  <!-- Slide Container -->
  <script>/* ALL JS INLINE */</script>
</body>
</html>
```

Everything must be inline. Zero external dependencies. No CDN links. No Google Fonts links (use system font stacks or embed @font-face with base64 only if absolutely necessary for a specific requested font).

### CSS Foundation

#### Reset & Base

```css
*, *::before, *::after {
  margin: 0; padding: 0; box-sizing: border-box;
}

:root {
  /* Theme tokens - set these per theme */
  --bg-primary: #000000;
  --bg-secondary: #0a1628;
  --text-primary: #ffffff;
  --text-secondary: #86868b;
  --text-muted: #6e6e73;
  --accent-1: #0071e3;
  --accent-1-light: #2997ff;
  --accent-2-start: #6e3aff;
  --accent-2-end: #a855f7;
  --accent-warm: #ff6723;
  --accent-pink: #ff375f;
  --accent-green: #30d158;
  --accent-teal: #64d2ff;
  --gray-100: #f5f5f7;
  --gray-200: #d2d2d7;
  --gray-400: #86868b;
  --gray-600: #6e6e73;
  --gray-800: #1d1d1f;
  --card-bg: rgba(255, 255, 255, 0.04);
  --card-border: rgba(255, 255, 255, 0.08);
  --card-blur: 40px;
  --transition-smooth: cubic-bezier(0.25, 0.46, 0.45, 0.94);
  --transition-spring: cubic-bezier(0.175, 0.885, 0.32, 1.275);
  --transition-cinematic: cubic-bezier(0.16, 1, 0.3, 1);
  --slide-duration: 900ms;
  --reveal-stagger: 150ms;
}

html { scroll-behavior: auto; overflow: hidden; background: var(--bg-primary); }

body {
  font-family: -apple-system, BlinkMacSystemFont, 'SF Pro Display', 'Inter', 'Segoe UI', Roboto, Helvetica, Arial, sans-serif;
  background: var(--bg-primary);
  color: var(--text-primary);
  overflow: hidden;
  height: 100vh;
  width: 100vw;
  -webkit-font-smoothing: antialiased;
  -moz-osx-font-smoothing: grayscale;
}
```

#### Light Theme Override

For light themes, override:
```css
:root {
  --bg-primary: #ffffff;
  --bg-secondary: #fafafa;
  --text-primary: #1d1d1f;
  --text-secondary: #86868b;
  --text-muted: #aeaeb2;
  --card-bg: rgba(0, 0, 0, 0.03);
  --card-border: rgba(0, 0, 0, 0.08);
  /* Adjust accent colors for contrast on light */
}
```

### Effects

#### Grain Overlay (dark themes only)

```css
.grain-overlay {
  position: fixed;
  top: -50%; left: -50%;
  width: 200%; height: 200%;
  pointer-events: none;
  z-index: 9998;
  opacity: 0.035;
  background-image: url("data:image/svg+xml,%3Csvg viewBox='0 0 256 256' xmlns='http://www.w3.org/2000/svg'%3E%3Cfilter id='noise'%3E%3CfeTurbulence type='fractalNoise' baseFrequency='0.9' numOctaves='4' stitchTiles='stitch'/%3E%3C/filter%3E%3Crect width='100%25' height='100%25' filter='url(%23noise)'/%3E%3C/svg%3E");
  animation: grainShift 0.5s steps(3) infinite;
}
@keyframes grainShift {
  0% { transform: translate(0, 0); }
  33% { transform: translate(-2px, 1px); }
  66% { transform: translate(1px, -1px); }
  100% { transform: translate(0, 0); }
}
```

#### Ambient Orbs (dark themes)

```css
.ambient-orb {
  position: absolute;
  border-radius: 50%;
  filter: blur(120px);
  opacity: 0.15;
  pointer-events: none;
  animation: orbFloat 12s ease-in-out infinite alternate;
}
@keyframes orbFloat {
  0% { transform: translate(0, 0) scale(1); }
  100% { transform: translate(30px, -20px) scale(1.1); }
}
```

Create 2-3 orbs per slide with different colors matching the theme. Vary sizes (400-600px), positions, animation delays.

#### Hero Glow Ring

```css
.hero-glow {
  position: absolute;
  width: 600px; height: 600px;
  border-radius: 50%;
  background: radial-gradient(circle, rgba(accent1, 0.08) 0%, rgba(accent2, 0.04) 40%, transparent 70%);
  pointer-events: none;
  top: 50%; left: 50%;
  transform: translate(-50%, -50%);
  animation: glowPulse 6s ease-in-out infinite alternate;
}
```

### Slide System

#### Container & Transitions

```css
.slide-container {
  position: fixed; inset: 0;
  width: 100vw; height: 100vh;
}

.slide {
  position: absolute; inset: 0;
  width: 100%; height: 100%;
  display: flex;
  flex-direction: column;
  align-items: center;
  justify-content: center;
  padding: 40px;
  opacity: 0;
  visibility: hidden;
  transform: scale(0.95) translateY(30px);
  transition: opacity var(--slide-duration) var(--transition-cinematic),
              transform var(--slide-duration) var(--transition-cinematic),
              visibility 0s linear var(--slide-duration);
  will-change: opacity, transform;
  overflow-y: auto;
  overflow-x: hidden;
}

.slide.active {
  opacity: 1;
  visibility: visible;
  transform: scale(1) translateY(0);
  transition: opacity var(--slide-duration) var(--transition-cinematic),
              transform var(--slide-duration) var(--transition-cinematic),
              visibility 0s linear 0s;
}

.slide.exiting-up {
  opacity: 0; visibility: hidden;
  transform: scale(1.05) translateY(-50px);
}

.slide.exiting-down {
  opacity: 0; visibility: hidden;
  transform: scale(0.9) translateY(50px);
}
```

#### Slide Background Variants

For dark themes, create gradient backgrounds per slide:
```css
.slide--dark { background: var(--bg-primary); }
.slide--gradient-blue { background: linear-gradient(145deg, #000 0%, #0a1628 40%, #0d2137 70%, #0a0a2e 100%); }
.slide--gradient-purple { background: linear-gradient(145deg, #000 0%, #1a0a2e 40%, #2d1b4e 60%, #0a0a2e 100%); }
.slide--gradient-warm { background: linear-gradient(145deg, #000 0%, #2e1a0a 40%, #3d1f0f 60%, #1a0a00 100%); }
```

For light themes, use subtle gradients:
```css
.slide--light { background: var(--bg-primary); }
.slide--gradient-soft { background: linear-gradient(145deg, #fff 0%, #f8f9fa 50%, #f0f0f5 100%); }
```

### Reveal Animations

```css
.reveal-element {
  opacity: 0;
  transform: translateY(40px);
  transition: opacity 0.8s var(--transition-cinematic),
              transform 0.8s var(--transition-cinematic);
}

.reveal-element.revealed {
  opacity: 1; transform: translateY(0);
}

/* Staggered delays */
.reveal-element[data-delay="1"] { transition-delay: 0.15s; }
.reveal-element[data-delay="2"] { transition-delay: 0.3s; }
.reveal-element[data-delay="3"] { transition-delay: 0.45s; }
/* Continue up to data-delay="12" at 0.15s increments */
```

Wrap every content element in a `<div class="reveal-element" data-delay="N">` with sequential delay values per slide.

### Slide Types — HTML Patterns

#### 1. Hero Slide

```html
<div class="slide slide--dark active" data-slide="0">
  <div class="hero-glow"></div>
  <div class="reveal-element" data-delay="0">
    <h1 class="hero-name">[Title]</h1>
  </div>
  <div class="reveal-element" data-delay="2">
    <p class="hero-subtitle">[Subtitle with separator spans]</p>
  </div>
  <div class="reveal-element" data-delay="4">
    <div class="divider-line"></div>
  </div>
  <div class="reveal-element" data-delay="5">
    <p class="hero-location">[Location or tagline]</p>
  </div>
</div>
```

Typography:
```css
.hero-name {
  font-size: clamp(48px, 10vw, 120px);
  font-weight: 700;
  letter-spacing: -0.03em;
  line-height: 1;
  text-align: center;
  background: linear-gradient(135deg, var(--text-primary) 0%, var(--gray-200) 100%);
  -webkit-background-clip: text;
  -webkit-text-fill-color: transparent;
  background-clip: text;
}

.hero-subtitle {
  font-size: clamp(18px, 3vw, 32px);
  font-weight: 400;
  color: var(--text-secondary);
  text-align: center;
  margin-top: 24px;
  letter-spacing: 0.02em;
}
```

#### 2. Stats Slide

```html
<div class="slide slide--gradient-blue" data-slide="N">
  <div class="ambient-orb ambient-orb--accent1"></div>
  <div class="reveal-element" data-delay="0">
    <p class="section-label">[Label text]</p>
  </div>
  <div class="stats-grid">
    <div class="stat-item reveal-element" data-delay="1">
      <div class="stat-number mega-number--accent1"><span class="count-up" data-target="[N]">0</span>[suffix]</div>
      <div class="stat-label">[Label]</div>
    </div>
    <!-- Repeat for each stat (2-4 stats ideal) -->
  </div>
</div>
```

Stats grid: `grid-template-columns: repeat(2, 1fr)`, gap `48px 64px`, max-width `900px`.

Mega numbers: `font-size: clamp(48px, 8vw, 96px)`, weight 800, gradient text with matching glow.

Count-up JS animates from 0 to target with ease-out cubic easing over 1200ms.

#### 3. Chapter Divider Slide

```html
<div class="slide slide--gradient-[color]" data-slide="N">
  <div class="ambient-orb"></div>
  <div class="reveal-element" data-delay="0">
    <p class="section-label">[Small label]</p>
  </div>
  <div class="reveal-element" data-delay="1">
    <h2 class="section-title">[Big title with gradient text]</h2>
  </div>
  <div class="reveal-element" data-delay="2">
    <p class="section-subtitle">[Supporting text, max 2 lines]</p>
  </div>
</div>
```

Section title: `font-size: clamp(36px, 7vw, 96px)`, weight 700, tight tracking.

#### 4. Content Card Slide

```html
<div class="slide slide--gradient-[color]" data-slide="N">
  <div class="ambient-orb"></div>
  <div class="reveal-element" data-delay="0">
    <p class="section-label">[Context label]</p>
  </div>
  <div class="reveal-element" data-delay="1">
    <h2 class="section-title" style="font-size: clamp(28px, 5vw, 56px);">[Title]</h2>
  </div>
  <div class="experience-card reveal-element" data-delay="2">
    <div class="card-title">[Title]</div>
    <div class="card-subtitle">[Subtitle in accent color]</div>
    <div class="card-meta">[Date/location/metadata]</div>
    <div class="card-body">
      <ul>
        <li>[Point 1]</li>
        <li>[Point 2]</li>
      </ul>
    </div>
  </div>
</div>
```

Card: `background: var(--card-bg)`, `backdrop-filter: blur(var(--card-blur))`, `border: 1px solid var(--card-border)`, `border-radius: 24px`, padding `clamp(32px, 4vw, 56px)`.

Top highlight: `::before` pseudo-element with gradient line.

Bullet points: custom dot (6px circle in accent color) via `::before`.

#### 5. Feature Grid Slide

```html
<div class="slide slide--gradient-deep" data-slide="N">
  <div class="reveal-element" data-delay="0">
    <p class="section-label">[Label]</p>
  </div>
  <div class="reveal-element" data-delay="1">
    <h2 class="section-title">[Title]</h2>
  </div>
  <div class="tech-grid">
    <div class="tech-chip tech-chip--[category] reveal-element" data-delay="2">
      [Item name]
      <span class="tech-category-label">[Category]</span>
    </div>
    <!-- Repeat -->
  </div>
</div>
```

Grid: `repeat(auto-fit, minmax(120px, 1fr))`, gap 16px. Chips have hover lift + scale, radial gradient glow on hover.

#### 6. Timeline Slide

```html
<div class="slide slide--gradient-[color]" data-slide="N">
  <div class="reveal-element" data-delay="0">
    <p class="section-label">[Label]</p>
  </div>
  <div class="reveal-element" data-delay="1">
    <h2 class="section-title">[Title]</h2>
  </div>
  <div class="timeline">
    <div class="timeline-item reveal-element" data-delay="2">
      <div class="timeline-marker"></div>
      <div class="timeline-content">
        <div class="timeline-date">[Date]</div>
        <div class="timeline-title">[Title]</div>
        <div class="timeline-desc">[Description]</div>
      </div>
    </div>
    <!-- Repeat -->
  </div>
</div>
```

Timeline: vertical line (2px, accent gradient) with circular markers (12px). Content cards to the right. Alternating layout on desktop.

```css
.timeline {
  position: relative;
  max-width: 800px;
  width: 100%;
  margin-top: 32px;
  padding-left: 40px;
}
.timeline::before {
  content: '';
  position: absolute;
  left: 16px;
  top: 0;
  bottom: 0;
  width: 2px;
  background: linear-gradient(to bottom, var(--accent-1), var(--accent-2-end));
}
.timeline-item {
  position: relative;
  margin-bottom: 32px;
  padding-left: 24px;
}
.timeline-marker {
  position: absolute;
  left: -32px;
  top: 6px;
  width: 12px;
  height: 12px;
  border-radius: 50%;
  background: var(--accent-1);
  border: 2px solid var(--bg-primary);
  box-shadow: 0 0 0 4px rgba(var(--accent-1-rgb), 0.2);
}
```

#### 7. Comparison Slide

```html
<div class="slide slide--gradient-[color]" data-slide="N">
  <div class="reveal-element" data-delay="0">
    <p class="section-label">[Label]</p>
  </div>
  <div class="reveal-element" data-delay="1">
    <h2 class="section-title">[Title]</h2>
  </div>
  <div class="comparison-grid">
    <div class="comparison-col reveal-element" data-delay="2">
      <h3 class="comparison-heading">[Side A]</h3>
      <ul class="comparison-list">
        <li>[Point]</li>
      </ul>
    </div>
    <div class="comparison-divider reveal-element" data-delay="3"></div>
    <div class="comparison-col reveal-element" data-delay="4">
      <h3 class="comparison-heading">[Side B]</h3>
      <ul class="comparison-list">
        <li>[Point]</li>
      </ul>
    </div>
  </div>
</div>
```

Two-column grid with vertical divider. Cards have frosted glass background.

#### 8. Quote Slide

```html
<div class="slide slide--dark" data-slide="N">
  <div class="hero-glow" style="opacity: 0.3;"></div>
  <div class="reveal-element" data-delay="0">
    <blockquote class="quote-text">"[Quote text]"</blockquote>
  </div>
  <div class="reveal-element" data-delay="2">
    <p class="quote-attribution">— [Name], [Title]</p>
  </div>
</div>
```

Quote: `font-size: clamp(24px, 4vw, 48px)`, weight 400, italic, line-height 1.4. Center aligned with max-width 800px.

#### 9. Image Slide

```html
<div class="slide slide--image" data-slide="N" style="background: linear-gradient(rgba(0,0,0,0.6), rgba(0,0,0,0.8)), url('[base64 or path]') center/cover;">
  <div class="reveal-element" data-delay="0">
    <p class="section-label">[Label]</p>
  </div>
  <div class="reveal-element" data-delay="1">
    <h2 class="section-title">[Overlay text]</h2>
  </div>
</div>
```

Note: For truly self-contained files, images should be base64-encoded inline if the user provides them. Otherwise use descriptive gradient backgrounds as visual stand-ins.

#### 10. Data Slide

```html
<div class="slide slide--gradient-[color]" data-slide="N">
  <div class="reveal-element" data-delay="0">
    <p class="section-label">[Label]</p>
  </div>
  <div class="reveal-element" data-delay="1">
    <h2 class="section-title">[Title]</h2>
  </div>
  <div class="data-bars">
    <div class="data-bar-item reveal-element" data-delay="2">
      <div class="data-bar-label">[Label]</div>
      <div class="data-bar-track">
        <div class="data-bar-fill" style="--bar-width: [N]%;" data-value="[N]%"></div>
      </div>
    </div>
    <!-- Repeat -->
  </div>
</div>
```

CSS-only animated bars. Fill animates width from 0 to `--bar-width` on reveal. Gradient fill matching theme accent.

```css
.data-bar-track {
  height: 8px;
  background: var(--card-bg);
  border-radius: 4px;
  overflow: hidden;
  flex: 1;
}
.data-bar-fill {
  height: 100%;
  width: 0;
  background: linear-gradient(90deg, var(--accent-1), var(--accent-2-end));
  border-radius: 4px;
  transition: width 1.2s var(--transition-cinematic);
}
.data-bar-fill.revealed { width: var(--bar-width); }
```

#### 11. Split Screen Slide

```html
<div class="slide slide--gradient-[color]" data-slide="N">
  <div class="split-layout">
    <div class="split-text reveal-element" data-delay="0">
      <p class="section-label">[Label]</p>
      <h2 class="section-title" style="text-align: left; font-size: clamp(28px, 5vw, 56px);">[Title]</h2>
      <p class="section-subtitle" style="text-align: left;">[Description]</p>
    </div>
    <div class="split-visual reveal-element" data-delay="2">
      <!-- Visual content: card, graphic, or placeholder -->
    </div>
  </div>
</div>
```

```css
.split-layout {
  display: grid;
  grid-template-columns: 1fr 1fr;
  gap: 64px;
  max-width: 1100px;
  width: 100%;
  align-items: center;
}
@media (max-width: 768px) {
  .split-layout { grid-template-columns: 1fr; gap: 32px; }
}
```

#### 12. List / Achievements Slide

```html
<div class="slide slide--dark" data-slide="N">
  <div class="reveal-element" data-delay="0">
    <h2 class="section-title">[Title]</h2>
  </div>
  <div class="achievements-list">
    <div class="achievement-item reveal-element" data-delay="1">
      <div class="achievement-icon">[emoji or icon]</div>
      <div class="achievement-content">
        <div class="achievement-title">[Title]</div>
        <div class="achievement-desc">[Description]</div>
      </div>
    </div>
    <!-- Repeat -->
  </div>
</div>
```

Icon container: 48x48, rounded 12px, frosted glass bg. Flex row with 20px gap.

#### 13. CTA / Contact Slide

```html
<div class="slide slide--gradient-[color]" data-slide="N">
  <div class="reveal-element" data-delay="0">
    <div class="available-badge">
      <span class="available-pulse"></span>
      [Status text]
    </div>
  </div>
  <div class="reveal-element" data-delay="1">
    <h2 class="section-title">[CTA headline]</h2>
  </div>
  <div class="reveal-element" data-delay="2">
    <p class="section-subtitle">[Supporting text]</p>
  </div>
  <div class="contact-links reveal-element" data-delay="3">
    <a href="[url]" class="contact-link contact-link--primary">
      <svg>...</svg> [Label]
    </a>
    <a href="[url]" class="contact-link">
      <svg>...</svg> [Label]
    </a>
  </div>
</div>
```

Pill-shaped links: `border-radius: 100px`, frosted glass bg, hover lift.

Available badge: green pulse animation, pill shape, green tint bg.

### Navigation Components

#### Progress Bar

```css
.progress-bar {
  position: fixed; top: 0; left: 0;
  height: 2px;
  background: linear-gradient(90deg, var(--accent-1), var(--accent-2-end));
  z-index: 200;
  transition: width 0.6s var(--transition-cinematic);
  box-shadow: 0 0 10px rgba(accent1, 0.5);
}
```

#### Navigation Dots

Fixed right side, vertical, 8px circles. Active dot: white, scale 1.4, glow shadow. Hover shows label via `::before` content.

#### Keyboard Hint

Fixed bottom center. Shows arrow keys and space. Hidden class after first interaction. Bounce arrow animation.

### JavaScript Engine

The JS engine handles:

1. **Slide navigation** — `goToSlide(index, direction)` with transition locking
2. **Reveal animations** — trigger `.revealed` class on active slide elements
3. **Count-up animations** — `requestAnimationFrame` with ease-out cubic
4. **Data bar animations** — trigger fill width on reveal
5. **Dot/progress updates** — sync with current slide
6. **Keyboard navigation** — arrows, space, page up/down, home/end, escape, T (notes), P (pdf)
7. **Mouse wheel** — debounced with accumulator (threshold 50, debounce 80ms)
8. **Touch** — swipe detection with 50px threshold
9. **Parallax** — mousemove on hero glow and ambient orbs
10. **Loading screen** — fade out after 600ms on window load
11. **Speaker notes toggle** — `toggleNotes()` opens/closes sidebar, `updateNotes()` syncs content to current slide
12. **PDF export** — `exportPdf()` snaps all count-up numbers to `data-target` values and data bars to full width before calling `window.print()`, ensuring animated values render correctly in the PDF

Key constants:
```js
const TOTAL_SLIDES = [number];
const TRANSITION_DURATION = 900;
const DEBOUNCE_MS = 80;
const COUNT_DURATION = 1200;
const WHEEL_THRESHOLD = 50;
```

Use an IIFE wrapper. No external dependencies. All event listeners with proper passive flags.

### Responsive Breakpoints

- **768px**: Single columns, reduced gaps, hidden dot labels, smaller padding
- **480px**: Further simplified grids, hidden keyboard hints
- **Touch devices**: Disable hover transforms via `@media (hover: none)`

### Speaker Notes Sidebar (Press T)

Every presentation MUST include a speaker notes sidebar. The sidebar:
- Slides in from the left when pressing `T` key or clicking the Notes button
- Frosted glass panel (`rgba(10,10,20,0.92)` bg, `backdrop-filter: blur(30px)`, 340px wide)
- Has a sticky header with "Talking Points" title, close button, and "Slide X of N" label
- Contains a `<div class="note-content" data-note="N">` for each slide with talking points
- Only the `.note-content.active` matching current slide is shown (display block/none)
- When open, the main slide container shifts right and scales down: `transform: translateX(170px) scale(0.88)`
- Progress bar left offset adjusts: `left: 340px`
- Toggle via `body.notes-open` class

**Talking points content**: Write 2-3 paragraphs per slide with:
- **Bold opener** — what to emphasize on this slide
- Key talking points in natural speaking language (not bullet points)
- A `.note-tip` callout for delivery tips (when to pause, make eye contact, etc.)

**Important**: Call `updateNotes()` inside `goToSlide()` when `notesOpen` is true.

### Controls Bar

Fixed bottom-right, two buttons:

```html
<div class="controls-bar">
  <button class="control-btn" id="btnNotes">
    <svg><!-- document icon --></svg> Notes <span class="key-badge">T</span>
  </button>
  <button class="control-btn" id="btnPdf">
    <svg><!-- download icon --></svg> PDF <span class="key-badge">P</span>
  </button>
</div>
```

Buttons: `border-radius: 10px`, frosted glass bg, 12px font. Key badge: 20x20 rounded square.

Hide controls bar on mobile (`@media (max-width: 480px) { .controls-bar { display: none; } }`).

### PDF / Print Export (Press P)

Every presentation MUST include PDF export via `window.print()` with a print stylesheet.

**Critical: Count-up number fix.** Before printing, the `exportPdf()` function MUST:
1. Snap ALL `.count-up` elements to their `data-target` values (set `textContent = getAttribute('data-target')`)
2. Add `.revealed` class to ALL `.data-bar-fill` elements so bars show at full width
3. Close speaker notes if open
4. Call `window.print()` after a 100ms delay to let CSS settle

```js
function exportPdf() {
  document.querySelectorAll('.count-up').forEach(function(el) {
    el.textContent = el.getAttribute('data-target');
  });
  document.querySelectorAll('.data-bar-fill').forEach(function(el) {
    el.classList.add('revealed');
  });
  var wasNotesOpen = notesOpen;
  if (notesOpen) toggleNotes();
  setTimeout(function() {
    window.print();
    if (wasNotesOpen) setTimeout(toggleNotes, 300);
  }, 100);
}
```

**Print stylesheet** (`@media print`):

```css
@media print {
  *, *::before, *::after { animation: none !important; transition: none !important; }
  html, body { overflow: visible !important; height: auto !important; width: auto !important; }
  .loading-screen, .grain-overlay, .progress-bar, .nav-dots,
  .keyboard-hint, .controls-bar, .speaker-notes,
  .ambient-orb, .hero-glow { display: none !important; }
  .slide-container { position: static !important; transform: none !important; }
  .slide {
    position: relative !important;
    opacity: 1 !important; visibility: visible !important; transform: none !important;
    width: 100% !important; height: 100vh !important;
    page-break-after: always; break-after: page;
    page-break-inside: avoid; break-inside: avoid;
    overflow: hidden !important;
  }
  .slide:last-child { page-break-after: auto; }
  .reveal-element { opacity: 1 !important; transform: none !important; }
  .data-bar-fill { width: var(--bar-width) !important; }
}
@page { size: landscape; margin: 0; }
```

### Typography Scale

| Element | Size | Weight | Tracking |
|---------|------|--------|----------|
| Hero name | clamp(48px, 10vw, 120px) | 700 | -0.03em |
| Section title | clamp(36px, 7vw, 96px) | 700 | -0.03em |
| Mega number | clamp(64px, 15vw, 180px) | 800 | -0.04em |
| Section label | clamp(14px, 1.5vw, 18px) | 600 | 0.15em, uppercase |
| Body text | clamp(14px, 1.8vw, 18px) | 400 | normal |
| Subtitle | clamp(16px, 2.5vw, 28px) | 400 | normal |
| Chip text | clamp(12px, 1.4vw, 15px) | 500 | normal |

### Quality Checklist

Before outputting the final HTML, verify:

- [ ] All CSS is inline in a single `<style>` tag
- [ ] All JS is inline in a single `<script>` tag
- [ ] No external dependencies or CDN links
- [ ] Every content element wrapped in `reveal-element` with sequential delays
- [ ] Navigation dots count matches total slides
- [ ] `TOTAL_SLIDES` constant matches actual slide count
- [ ] Progress bar gradient matches theme
- [ ] All `data-slide` attributes are sequential from 0
- [ ] Count-up elements have `data-target` set
- [ ] Cards have `::before` top highlight gradient
- [ ] Responsive styles handle 768px and 480px breakpoints
- [ ] Touch prevention (`touchmove` preventDefault) is included
- [ ] Loading screen included and auto-hides
- [ ] `will-change` hints on slide elements
- [ ] Grain overlay included (dark themes) or omitted (light themes)
- [ ] Ambient orbs have varied positions, sizes, and animation delays
- [ ] Speaker notes sidebar included with talking points for EVERY slide
- [ ] Each `.note-content[data-note="N"]` matches a slide (0-indexed)
- [ ] Controls bar with Notes (T) and PDF (P) buttons is included
- [ ] `exportPdf()` snaps count-up values to targets before `window.print()`
- [ ] `@media print` stylesheet hides UI chrome and shows all slides as pages
- [ ] `@page { size: landscape; margin: 0; }` is set
- [ ] `updateNotes()` is called in `goToSlide()` when notes are open
- [ ] T key toggles notes, P key triggers PDF export, Escape closes notes

### Common SVG Icons for Contact Links

Include these inline SVGs as needed:

- **Email**: `<path d="M20 4H4c-1.1 0-2 .9-2 2v12c0 1.1.9 2 2 2h16c1.1 0 2-.9 2-2V6c0-1.1-.9-2-2-2zm0 4l-8 5-8-5V6l8 5 8-5v2z"/>`
- **LinkedIn**: `<path d="M19 3a2 2 0 0 1 2 2v14a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h14m-.5 15.5v-5.3a3.26 3.26 0 0 0-3.26-3.26c-.85 0-1.84.52-2.32 1.3v-1.11h-2.79v8.37h2.79v-4.93c0-.77.62-1.4 1.39-1.4a1.4 1.4 0 0 1 1.4 1.4v4.93h2.79M6.88 8.56a1.68 1.68 0 0 0 1.68-1.68c0-.93-.75-1.69-1.68-1.69a1.69 1.69 0 0 0-1.69 1.69c0 .93.76 1.68 1.69 1.68m1.39 9.94v-8.37H5.5v8.37h2.77z"/>`
- **GitHub**: `<path d="M12 2A10 10 0 0 0 2 12c0 4.42 2.87 8.17 6.84 9.5.5.08.66-.23.66-.5v-1.69c-2.77.6-3.36-1.34-3.36-1.34-.46-1.16-1.11-1.47-1.11-1.47-.91-.62.07-.6.07-.6 1 .07 1.53 1.03 1.53 1.03.87 1.52 2.34 1.07 2.91.83.09-.65.35-1.09.63-1.34-2.22-.25-4.55-1.11-4.55-4.92 0-1.11.38-2 1.03-2.71-.1-.25-.45-1.29.1-2.64 0 0 .84-.27 2.75 1.02.79-.22 1.65-.33 2.5-.33.85 0 1.71.11 2.5.33 1.91-1.29 2.75-1.02 2.75-1.02.55 1.35.2 2.39.1 2.64.65.71 1.03 1.6 1.03 2.71 0 3.82-2.34 4.66-4.57 4.91.36.31.69.92.69 1.85V21c0 .27.16.59.67.5C19.14 20.16 22 16.42 22 12A10 10 0 0 0 12 2z"/>`
- **Twitter/X**: `<path d="M18.244 2.25h3.308l-7.227 8.26 8.502 11.24H16.17l-5.214-6.817L4.99 21.75H1.68l7.73-8.835L1.254 2.25H8.08l4.713 6.231zm-1.161 17.52h1.833L7.084 4.126H5.117z"/>`
- **Website**: `<path d="M12 2C6.48 2 2 6.48 2 12s4.48 10 10 10 10-4.48 10-10S17.52 2 12 2zm-1 17.93c-3.95-.49-7-3.85-7-7.93 0-.62.08-1.21.21-1.79L9 15v1c0 1.1.9 2 2 2v1.93zm6.9-2.54c-.26-.81-1-1.39-1.9-1.39h-1v-3c0-.55-.45-1-1-1H8v-2h2c.55 0 1-.45 1-1V7h2c1.1 0 2-.9 2-2v-.41c2.93 1.19 5 4.06 5 7.41 0 2.08-.8 3.97-2.1 5.39z"/>`

All SVGs use `viewBox="0 0 24 24"` and `fill="currentColor"` at 18x18px.

---

## Theme Definitions

When the user selects a theme, apply these complete variable sets:

### Dark Cinematic
```
--bg-primary: #000000
--text-primary: #ffffff
--text-secondary: #86868b
--accent-1: #0071e3
--accent-1-light: #2997ff
--accent-2-start: #6e3aff
--accent-2-end: #a855f7
--accent-warm: #ff6723
--accent-green: #30d158
--card-bg: rgba(255, 255, 255, 0.04)
--card-border: rgba(255, 255, 255, 0.08)
Font: -apple-system, BlinkMacSystemFont, SF Pro, system
Effects: grain overlay, ambient orbs, hero glow
```

### Light Minimal
```
--bg-primary: #ffffff
--bg-secondary: #fafafa
--text-primary: #1d1d1f
--text-secondary: #86868b
--text-muted: #aeaeb2
--accent-1: #0071e3
--card-bg: rgba(0, 0, 0, 0.03)
--card-border: rgba(0, 0, 0, 0.08)
Font: 'Geist', -apple-system, system
Effects: subtle shadows, no grain, no orbs
```

### Warm Editorial
```
--bg-primary: #1a1210
--text-primary: #f5efe8
--text-secondary: #a89585
--accent-1: #e8734a
--accent-2-end: #c4956a
--card-bg: rgba(245, 239, 232, 0.04)
--card-border: rgba(245, 239, 232, 0.08)
Font: 'Playfair Display', Georgia, serif (headings) + 'Source Sans 3', system (body)
Effects: warm grain, warm orbs, paper texture
```

### Neon Cyberpunk
```
--bg-primary: #0a0a1a
--text-primary: #e0e0ff
--text-secondary: #6b7280
--accent-1: #00f0ff
--accent-2-end: #ff00aa
--accent-warm: #7c3aed
--card-bg: rgba(0, 240, 255, 0.04)
--card-border: rgba(0, 240, 255, 0.12)
Font: 'JetBrains Mono', monospace (headings) + 'Space Grotesk', system (body)
Effects: neon glow borders, scanline overlay, grid background
```

### Earth Organic
```
--bg-primary: #faf8f5
--text-primary: #2d2a26
--text-secondary: #7a7470
--accent-1: #2d6a4f
--accent-2-end: #b07d62
--card-bg: rgba(45, 106, 79, 0.04)
--card-border: rgba(45, 106, 79, 0.1)
Font: 'DM Sans', system (headings + body)
Effects: no grain, organic blob shapes instead of orbs, warm shadows
```

---

## Content-Aware AI Decisions

When analyzing content, use these heuristics to suggest themes and slide types:

| Content Type | Suggested Theme | Typical Slides |
|-------------|-----------------|----------------|
| Startup pitch | Dark Cinematic | Hero, Stats, Chapter, Content Card, Feature Grid, CTA |
| Portfolio | Dark Cinematic or Light Minimal | Hero, Stats, Chapter, Content Card x N, Feature Grid, List, CTA |
| Product launch | Neon Cyberpunk or Dark Cinematic | Hero, Chapter, Split, Feature Grid, Comparison, Stats, CTA |
| Educational | Light Minimal or Earth Organic | Hero, Chapter, Content Card, Data, Timeline, List, CTA |
| Report / research | Light Minimal | Hero, Stats, Data, Content Card, Comparison, List, CTA |
| Personal story | Warm Editorial | Hero, Timeline, Quote, Content Card, List, CTA |
| Company overview | Dark Cinematic | Hero, Stats, Chapter, Content Card, Feature Grid, Timeline, CTA |

Always tell the user WHY you're recommending a specific theme. Be specific about the content, not generic.

---

## Narrative Arc Guidelines

Structure slides to follow a story arc:

1. **Hook** — Hero slide that grabs attention
2. **Context** — Stats or chapter that establishes credibility
3. **Body** — The core content (cards, grids, timelines, comparisons)
4. **Surprise** — A "one more thing" moment or unexpected highlight
5. **Close** — CTA or contact slide

Each slide should communicate ONE idea. If a slide has too much content, split it into multiple slides.

Keep total slide count between 8-15 for optimal pacing. Fewer than 8 feels thin; more than 15 feels long.
