# Accessibility Reference

## Non-Negotiable Rules

Every 2.5D website MUST implement ALL of the following. These are not optional enhancements — they are legal requirements in many jurisdictions and ethical requirements always.

---

## 1. prefers-reduced-motion (Most Critical)

Parallax and complex animations can trigger vestibular disorders — dizziness, nausea, migraines — in a significant portion of users. WCAG 2.1 Success Criterion 2.3.3 requires handling this.

```css
/* This block must be in EVERY project */
@media (prefers-reduced-motion: reduce) {
  /* Nuclear option: stop all animations globally */
  *,
  *::before,
  *::after {
    animation-duration: 0.01ms !important;
    animation-iteration-count: 1 !important;
    transition-duration: 0.01ms !important;
    scroll-behavior: auto !important;
  }

  /* Specifically disable 2.5D techniques */
  .float-loop { animation: none !important; }
  .parallax-layer { transform: none !important; }
  .depth-0, .depth-1, .depth-2, 
  .depth-3, .depth-4, .depth-5 {
    transform: none !important;
    filter: none !important;
  }
  .glow-blob { opacity: 0.3; animation: none !important; }
  .theatrical, .theatrical-with-exit {
    animation: none !important;
    opacity: 1 !important;
    transform: none !important;
  }
}
```

```javascript
// Also check in JavaScript — some GSAP animations don't respect CSS media queries
if (window.matchMedia('(prefers-reduced-motion: reduce)').matches) {
  gsap.globalTimeline.timeScale(0); // Stops all GSAP animations
  ScrollTrigger.getAll().forEach(t => t.kill()); // Kill all scroll triggers
  
  // Show all content immediately (don't hide-until-animated)
  document.querySelectorAll('[data-animate]').forEach(el => {
    el.style.opacity = '1';
    el.style.transform = 'none';
    el.removeAttribute('data-animate');
  });
}
```

## Per-Effect Reduced Motion (Smarter Than Kill-All)

Rather than freezing every animation globally, classify each type:

| Animation Type | At reduced-motion |
|---|---|
| Scroll parallax depth layers | DISABLE — continuous motion triggers vestibular issues |
| Float loops / ambient movement | DISABLE — looping motion is a trigger |
| DJI scale-in / perspective zoom | DISABLE — fast scale can cause dizziness |
| Particle systems | DISABLE |
| Clip-path reveals (one-shot) | KEEP — not continuous, not fast |
| Fade-in on scroll (opacity only) | KEEP — safe |
| Word-by-word scroll lighting | KEEP — no movement, just colour |
| Curtain / wipe reveals (one-shot) | KEEP |
| Text entrance slides (one-shot) | KEEP but reduce duration |

```javascript
const prefersReduced = window.matchMedia('(prefers-reduced-motion: reduce)').matches;

if (prefersReduced) {
  // Disable the motion-heavy ones
  document.querySelectorAll('.float-loop').forEach(el => {
    el.style.animation = 'none';
  });
  document.querySelectorAll('[data-depth]').forEach(el => {
    el.style.transform = 'none';
    el.style.willChange = 'auto';
  });

  // Slow GSAP to near-freeze (don't fully kill — keep structure intact)
  gsap.globalTimeline.timeScale(0.01);

  // Safe animations: show them immediately at final state
  gsap.utils.toArray('.clip-reveal, .fade-reveal, .word-light').forEach(el => {
    gsap.set(el, { clipPath: 'inset(0 0% 0 0)', opacity: 1 });
  });
}
```

---

## 2. Semantic HTML Structure

```html
<!-- CORRECT semantic structure -->
<main>
  <!-- Each visual scene is a section with proper landmarks -->
  <section aria-label="Hero — Product Introduction">
    
    <!-- ALL purely decorative elements get aria-hidden -->
    <div class="layer depth-0" aria-hidden="true">
      <!-- background gradients, glow blobs, particles -->
    </div>
    <div class="layer depth-1" aria-hidden="true">
      <!-- atmospheric effects -->
    </div>
    <div class="layer depth-5" aria-hidden="true">
      <!-- particles, sparkles -->
    </div>

    <!-- Meaningful content is NOT hidden -->
    <div class="layer depth-3">
      <img 
        src="product.png" 
        alt="[Descriptive alt text — what is the product, what does it look like]"
        <!-- NOT: alt="" for meaningful images! -->
      >
    </div>
    
    <div class="layer depth-4">
      <!-- Proper heading hierarchy -->
      <h1>Your Brand Name</h1>
      <!-- h1 is the page title — only one per page -->
      <p>Supporting description that provides context for screen readers</p>
      <a href="#features" class="cta-btn">
        Explore Features
        <!-- CTAs need descriptive text, not just "Click here" -->
      </a>
    </div>

  </section>
  
  <section aria-label="Product Features">
    <h2>Why Choose [Product]</h2>
    <!-- h2 for section headings -->
  </section>
</main>
```

---

## 3. SplitText & Screen Readers

When using SplitText to fragment text into characters/words, the individual fragments get announced one at a time by screen readers — which sounds terrible. Fix this:

```javascript
function splitTextAccessibly(el, options) {
  // Save the full text for screen readers
  const fullText = el.textContent.trim();
  el.setAttribute('aria-label', fullText);

  // Split visually only
  const split = new SplitText(el, options);

  // Hide the split fragments from screen readers
  // Screen readers will use aria-label instead
  split.chars?.forEach(char => char.setAttribute('aria-hidden', 'true'));
  split.words?.forEach(word => word.setAttribute('aria-hidden', 'true'));
  split.lines?.forEach(line => line.setAttribute('aria-hidden', 'true'));

  return split;
}

// Usage
splitTextAccessibly(document.querySelector('.hero-title'), { type: 'chars,words' });
```

---

## 4. Keyboard Navigation

All interactive elements must be reachable and operable via keyboard (Tab, Enter, Space, Arrow keys).

```css
/* Ensure focus indicators are visible — WCAG 2.4.7 */
:focus-visible {
  outline: 3px solid #005fcc; /* High contrast focus ring */
  outline-offset: 3px;
  border-radius: 3px;
}

/* Remove default outline only if replacing with custom */
:focus:not(:focus-visible) {
  outline: none;
}

/* Skip link for keyboard users to bypass navigation */
.skip-link {
  position: absolute;
  top: -100px;
  left: 0;
  background: #005fcc;
  color: white;
  padding: 12px 20px;
  z-index: 10000;
  font-weight: 600;
  text-decoration: none;
}
.skip-link:focus {
  top: 0; /* Appears at top when focused */
}
```

```html
<!-- Always first element in body -->
<a href="#main-content" class="skip-link">Skip to main content</a>
<main id="main-content">
  ...
</main>
```

---

## 5. Color Contrast (WCAG 2.1 AA)

Text must have sufficient contrast against its background:
- Normal text (under 18pt): **minimum 4.5:1 contrast ratio**
- Large text (18pt+ or 14pt+ bold): **minimum 3:1 contrast ratio**
- UI components and focus indicators: **minimum 3:1**

```css
/* Common mistake: light text on gradient with glow effects */
/* Always test contrast with the darkest AND lightest background in the gradient */

/* Safe text over complex backgrounds — add text shadow for contrast boost */
.hero-text-on-image {
  color: #ffffff;
  /* Multiple small text shadows create a halo that boosts contrast */
  text-shadow: 
    0 0 20px rgba(0,0,0,0.8),
    0 2px 4px rgba(0,0,0,0.6),
    0 0 40px rgba(0,0,0,0.4);
}

/* Or use a semi-transparent backdrop */
.text-backdrop {
  background: rgba(0, 0, 0, 0.55);
  backdrop-filter: blur(8px);
  padding: 1rem 1.5rem;
  border-radius: 8px;
}
```

**Testing tool:** Use browser DevTools accessibility panel or webaim.org/resources/contrastchecker/

---

## 6. Motion-Sensitive Users — User Control

Beyond `prefers-reduced-motion`, provide an in-page control:

```html
<!-- Floating toggle button -->
<button 
  class="motion-toggle" 
  aria-pressed="false"
  aria-label="Toggle animations on/off"
>
  <span class="motion-toggle-icon">✦</span>
  <span class="motion-toggle-text">Animations On</span>
</button>
```

```javascript
const motionToggle = document.querySelector('.motion-toggle');
let animationsEnabled = !window.matchMedia('(prefers-reduced-motion: reduce)').matches;

motionToggle.addEventListener('click', () => {
  animationsEnabled = !animationsEnabled;
  motionToggle.setAttribute('aria-pressed', !animationsEnabled);
  motionToggle.querySelector('.motion-toggle-text').textContent = 
    animationsEnabled ? 'Animations On' : 'Animations Off';
  
  if (animationsEnabled) {
    document.documentElement.classList.remove('no-motion');
    gsap.globalTimeline.timeScale(1);
  } else {
    document.documentElement.classList.add('no-motion');
    gsap.globalTimeline.timeScale(0);
  }
  
  // Persist preference
  localStorage.setItem('motionPreference', animationsEnabled ? 'on' : 'off');
});

// Restore on load
const saved = localStorage.getItem('motionPreference');
if (saved === 'off') motionToggle.click();
```

---

## 7. Images — Alt Text Guidelines

```html
<!-- Meaningful product image -->
<img src="juice-glass.png" alt="Tall glass of fresh orange juice with ice, floating on a gradient background">

<!-- Decorative geometric shape -->
<img src="shape-circle.png" alt="" aria-hidden="true">
<!-- Empty alt="" tells screen readers to skip it -->

<!-- Icon with text label next to it -->
<img src="icon-arrow.svg" alt="" aria-hidden="true">
<span>Learn More</span>
<!-- Icon is decorative when text is present -->

<!-- Standalone icon button — needs alt text -->
<button>
  <img src="icon-menu.svg" alt="Open navigation menu">
</button>
```

---

## 8. Loading Screen Accessibility

```javascript
// Announce loading state to screen readers
function announceLoading() {
  const announcement = document.createElement('div');
  announcement.setAttribute('role', 'status');
  announcement.setAttribute('aria-live', 'polite');
  announcement.setAttribute('aria-label', 'Page loading');
  announcement.className = 'sr-only'; // visually hidden
  document.body.appendChild(announcement);

  // Update announcement when done
  window.addEventListener('load', () => {
    announcement.textContent = 'Page loaded';
    setTimeout(() => announcement.remove(), 1000);
  });
}
```

```css
/* Screen-reader only utility class */
.sr-only {
  position: absolute;
  width: 1px;
  height: 1px;
  padding: 0;
  margin: -1px;
  overflow: hidden;
  clip: rect(0,0,0,0);
  white-space: nowrap;
  border: 0;
}
```

---

## WCAG 2.1 AA Compliance Checklist

Before shipping any 2.5D website:

- [ ] `prefers-reduced-motion` CSS block present and tested
- [ ] GSAP animations stopped when reduced motion detected
- [ ] All decorative elements have `aria-hidden="true"`
- [ ] All meaningful images have descriptive alt text
- [ ] SplitText elements have `aria-label` on parent
- [ ] Heading hierarchy is logical (h1 → h2 → h3, no skipping)
- [ ] All interactive elements reachable via keyboard Tab
- [ ] Focus indicators visible and have 3:1 contrast
- [ ] Skip-to-main-content link present
- [ ] Text contrast meets 4.5:1 minimum
- [ ] CTA buttons have descriptive text
- [ ] Motion toggle button provided (optional but recommended)
- [ ] Page has `<html lang="en">` (or correct language)
- [ ] `<main>` landmark wraps page content
- [ ] Section landmarks use `aria-label` to differentiate them
