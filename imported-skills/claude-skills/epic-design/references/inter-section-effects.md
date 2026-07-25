# Inter-Section Effects Reference

These are the most premium techniques — effects where elements **persist, travel, or transition between sections**, creating a seamless narrative thread across the entire page.

## Table of Contents
1. [Floating Product Between Sections](#floating-product)
2. [GSAP Flip Cross-Section Morph](#flip-morph)
3. [Clip-Path Section Birth (Product Grows from Border)](#clip-birth)
4. [DJI-Style Scale-In Pin](#dji-scale)
5. [Element Curved Path Travel](#curved-path)
6. [Section Peel Reveal](#section-peel)

---

## Technique 1: Floating Product Between Sections {#floating-product}

This is THE signature technique for product brands. A product image (juice bottle, phone, sneaker) starts inside the hero section. As you scroll, it appears to "rise up" through the section boundary and hover between two differently-colored sections — partially owned by neither. Then as you continue scrolling, it gracefully descends back in.

**The Visual Story:**
- Hero section: product sitting naturally inside
- Mid-scroll: product "floating" in space, section colors visible above and below it
- Continue scroll: product becomes part of the next section

```css
/* The product is positioned in a sticky wrapper */
.inter-section-product-wrapper {
  /* This wrapper spans BOTH sections */
  position: relative;
  z-index: 100;
  pointer-events: none;
  height: 0; /* no height — just a position anchor */
}

.inter-section-product {
  position: sticky;
  top: 50vh; /* stick to vertical center of viewport */
  transform: translateY(-50%); /* true center */
  width: 100%;
  display: flex;
  justify-content: center;
  pointer-events: none;
}

.inter-section-product img {
  width: clamp(280px, 35vw, 560px);
  /* The product will be exactly at the section boundary
     when the page is scrolled to that point */
}
```

```javascript
function initFloatingProduct() {
  const wrapper = document.querySelector('.inter-section-product-wrapper');
  const productImg = wrapper.querySelector('img');
  const heroSection = document.querySelector('.hero-section');
  const nextSection = document.querySelector('.feature-section');

  // Create a ScrollTrigger timeline for the product's journey
  const tl = gsap.timeline({
    scrollTrigger: {
      trigger: heroSection,
      start: 'bottom 80%',    // starts rising as hero bottom approaches viewport
      end: 'bottom 20%',      // completes rise when hero fully exited
      scrub: 1.5,
    }
  });

  // Phase 1: Product rises up from hero (scale grows, shadow intensifies)
  tl.fromTo(productImg,
    {
      y: 0,
      scale: 0.85,
      filter: 'drop-shadow(0 10px 20px rgba(0,0,0,0.2))',
    },
    {
      y: '-8vh',
      scale: 1.05,
      filter: 'drop-shadow(0 40px 80px rgba(0,0,0,0.5))',
      duration: 0.5,
    }
  );

  // Phase 2: Product fully "between" sections — peak visibility
  tl.to(productImg, {
    y: '-5vh',
    scale: 1.1,
    duration: 0.3,
  });

  // Phase 3: Product descends into next section
  ScrollTrigger.create({
    trigger: nextSection,
    start: 'top 60%',
    end: 'top 20%',
    scrub: 1.5,
    onUpdate: (self) => {
      gsap.to(productImg, {
        y: `${self.progress * 8}vh`,
        scale: 1.1 - (self.progress * 0.2),
        duration: 0.1,
        overwrite: true,
      });
    }
  });
}
```

### Required HTML Structure

```html
<!-- SECTION 1: Hero (dark background) -->
<section class="hero-section" style="background: #0a0014; min-height: 100vh; position: relative; z-index: 1;">
  <!-- depth layers 0-2 (bg, glow, decorations) -->
  <!-- NO product image here — it's in the inter-section wrapper -->
  <div class="layer depth-4">
    <h1>Your Headline</h1>
    <p>Hero subtext here</p>
  </div>
</section>

<!-- THE FLOATING PRODUCT — outside both sections, between them -->
<div class="inter-section-product-wrapper">
  <div class="inter-section-product">
    <img 
      src="product.png" 
      alt="Product Name — floating between hero and features"
      class="float-loop"
    />
  </div>
</div>

<!-- SECTION 2: Features (lighter background) -->
<section class="feature-section" style="background: #f5f0ff; min-height: 100vh; position: relative; z-index: 2; padding-top: 15vh;">
  <!-- Product appears to "land" into this section -->
  <div class="feature-content">
    <h2>Features Headline</h2>
  </div>
</section>
```

---

## Technique 2: GSAP Flip Cross-Section Morph {#flip-morph}

The same DOM element appears to travel between completely different layout positions across sections. In the hero it's large and centered; in the feature section it's small and left-aligned; in the detail section it's full-width. One smooth morph connects them all.

```javascript
function initFlipMorphSections() {
  gsap.registerPlugin(Flip);

  // The product element exists in one place in the DOM
  // but we have "ghost" placeholder positions in other sections
  const product = document.querySelector('.traveling-product');
  const positions = {
    hero:    document.querySelector('.product-position-hero'),
    feature: document.querySelector('.product-position-feature'),
    detail:  document.querySelector('.product-position-detail'),
  };

  function morphToPosition(positionEl, options = {}) {
    // Capture current state
    const state = Flip.getState(product);

    // Move element to new position
    positionEl.appendChild(product);

    // Animate from captured state to new position
    Flip.from(state, {
      duration: 0.9,
      ease: 'power3.inOut',
      ...options
    });
  }

  // Trigger morphs on scroll
  ScrollTrigger.create({
    trigger: '.feature-section',
    start: 'top 60%',
    onEnter: () => morphToPosition(positions.feature),
    onLeaveBack: () => morphToPosition(positions.hero),
  });

  ScrollTrigger.create({
    trigger: '.detail-section',
    start: 'top 60%',
    onEnter: () => morphToPosition(positions.detail),
    onLeaveBack: () => morphToPosition(positions.feature),
  });
}
```

### Ghost Position Placeholders HTML

```html
<!-- Hero section: large, centered position -->
<section class="hero-section">
  <div class="product-position-hero" style="width: 500px; height: 500px; margin: 0 auto;">
    <!-- Product starts here -->
    <img class="traveling-product" src="product.png" alt="Product" style="width:100%;">
  </div>
</section>

<!-- Feature section: medium, left-side position -->
<section class="feature-section">
  <div class="feature-layout">
    <div class="product-position-feature" style="width: 280px; height: 280px;">
      <!-- Product morphs to here -->
    </div>
    <div class="feature-text">...</div>
  </div>
</section>
```

---

## Technique 3: Clip-Path Section Birth (Product Grows from Border) {#clip-birth}

The product image starts completely hidden below the section's bottom border — clipped out of existence. As the user scrolls into the section boundary, the product "grows up" through the border like a plant emerging from soil. This is distinct from the floating product — here, the section itself is the stage.

```css
.birth-section {
  position: relative;
  overflow: hidden; /* hard clip at section border */
  min-height: 100vh;
}

.birth-product {
  position: absolute;
  bottom: -20%;  /* starts 20% below the section — invisible */
  left: 50%;
  transform: translateX(-50%);
  width: clamp(300px, 40vw, 600px);
  /* Will animate up through the section boundary */
}
```

```javascript
function initClipPathBirth(sectionEl, productEl) {
  const tl = gsap.timeline({
    scrollTrigger: {
      trigger: sectionEl,
      start: 'top 80%',
      end: 'top 20%',
      scrub: 1.2,
    }
  });

  // Product rises from below section boundary
  tl.fromTo(productEl,
    {
      y: '120%',     // fully below section
      scale: 0.7,
      opacity: 0,
      filter: 'blur(8px)'
    },
    {
      y: '0%',        // sits naturally in section
      scale: 1,
      opacity: 1,
      filter: 'blur(0px)',
      ease: 'power3.out',
      duration: 1,
    }
  );

  // Continue scroll → product rises further and becomes full height
  // then disappears back below as section exits
  ScrollTrigger.create({
    trigger: sectionEl,
    start: 'bottom 60%',
    end: 'bottom top',
    scrub: 1,
    onUpdate: (self) => {
      gsap.to(productEl, {
        y: `${-self.progress * 50}%`,
        opacity: 1 - self.progress,
        scale: 1 + self.progress * 0.2,
        duration: 0.1,
        overwrite: true,
      });
    }
  });
}
```

---

## Technique 4: DJI-Style Scale-In Pin {#dji-scale}

Made famous by DJI drone product pages. A section starts with a small, contained image. As the user scrolls, the image scales up to fill the entire viewport — THEN the section unpins and the next content reveals. Creates a "zoom into the world" feeling.

```javascript
function initDJIScaleIn(sectionEl) {
  const heroMedia = sectionEl.querySelector('.dji-media');
  const heroContent = sectionEl.querySelector('.dji-content');
  const overlay = sectionEl.querySelector('.dji-overlay');

  const tl = gsap.timeline({
    scrollTrigger: {
      trigger: sectionEl,
      start: 'top top',
      end: '+=300%',
      pin: true,
      scrub: 1.5,
    }
  });

  // Stage 1: Small image scales up to fill viewport
  tl.fromTo(heroMedia,
    {
      borderRadius: '20px',
      scale: 0.3,
      width: '60%',
      left: '20%',
      top: '20%',
    },
    {
      borderRadius: '0px',
      scale: 1,
      width: '100%',
      left: '0%',
      top: '0%',
      duration: 0.4,
      ease: 'power2.inOut',
    }
  )
  // Stage 2: Overlay fades in over the full-viewport image
  .fromTo(overlay,
    { opacity: 0 },
    { opacity: 0.6, duration: 0.2 },
    0.35
  )
  // Stage 3: Content text appears over the overlay
  .from(heroContent.querySelectorAll('.dji-line'),
    {
      y: 40,
      opacity: 0,
      stagger: 0.08,
      duration: 0.25,
    },
    0.45
  );

  return tl;
}
```

```css
.dji-section {
  position: relative;
  height: 100vh;
  overflow: hidden;
}
.dji-media {
  position: absolute;
  height: 100%;
  object-fit: cover;
  /* Will be animated to full coverage */
}
.dji-overlay {
  position: absolute;
  inset: 0;
  background: linear-gradient(to bottom, transparent, rgba(0,0,0,0.8));
  opacity: 0;
}
.dji-content {
  position: absolute;
  bottom: 15%;
  left: 8%;
  right: 8%;
  color: white;
}
```

---

## Technique 5: Element Curved Path Travel {#curved-path}

The most advanced technique. A product element travels along a smooth, curved Bezier path across the page as the user scrolls — arcing through space like it's floating or being thrown, rather than just translating in a straight line.

```html
<script src="https://cdn.jsdelivr.net/npm/gsap@3.12.5/dist/MotionPathPlugin.min.js"></script>
```

```javascript
function initCurvedPathTravel(productEl) {
  gsap.registerPlugin(MotionPathPlugin);

  // Define the curved path as SVG coordinates
  // Relative to the product's parent container
  const path = [
    { x: 0, y: 0 },          // Start: hero center
    { x: -200, y: -100 },    // Arc left and up
    { x: 100, y: -300 },     // Continue arcing
    { x: 300, y: -150 },     // Swing right
    { x: 200, y: 50 },       // Land into feature section
  ];

  gsap.to(productEl, {
    motionPath: {
      path: path,
      curviness: 1.4,  // How curvy (0 = straight lines, 2 = very curved)
      autoRotate: false, // Don't rotate along path (keep product upright)
    },
    scale: gsap.utils.interpolate([0.8, 1.1, 0.9, 1.0, 1.2]),
    ease: 'none',
    scrollTrigger: {
      trigger: '.journey-container',
      start: 'top top',
      end: '+=400%',
      pin: true,
      scrub: 1.5,
    }
  });
}
```

---

## Technique 6: Section Peel Reveal {#section-peel}

The section below is revealed by the section above peeling away — like turning a page. Uses `sticky: bottom: 0` so the lower section sticks to the screen bottom while the upper section scrolls away.

```css
.peel-upper {
  position: relative;
  z-index: 2;
  min-height: 100vh;
  /* This section scrolls away normally */
}

.peel-lower {
  position: sticky;
  bottom: 0;          /* sticks to BOTTOM of viewport */
  z-index: 1;
  min-height: 100vh;
  /* This section waits at the bottom as upper section peels away */
}

/* Container wraps both */
.peel-container {
  position: relative;
}
```

```javascript
function initSectionPeel() {
  const upper = document.querySelector('.peel-upper');
  const lower = document.querySelector('.peel-lower');

  // As upper section scrolls, reveal lower by reducing clip
  gsap.fromTo(upper,
    { clipPath: 'inset(0 0 0 0)' },
    {
      clipPath: 'inset(0 0 100% 0)', // upper peels up and away
      ease: 'none',
      scrollTrigger: {
        trigger: '.peel-container',
        start: 'top top',
        end: 'center top',
        scrub: true,
      }
    }
  );

  // Lower section content animates in as it's revealed
  gsap.from(lower.querySelectorAll('.peel-content > *'), {
    y: 30,
    opacity: 0,
    stagger: 0.1,
    duration: 0.6,
    scrollTrigger: {
      trigger: '.peel-container',
      start: '30% top',
      toggleActions: 'play none none reverse',
    }
  });
}
```

---

## Choosing the Right Inter-Section Technique

| Situation | Best Technique |
|-----------|---------------|
| Brand/product site with hero image | Floating Product Between Sections |
| Product appears in multiple contexts | GSAP Flip Cross-Section Morph |
| Product "rises" from section boundary | Clip-Path Section Birth |
| Cinematic "enter the world" feeling | DJI-Style Scale-In Pin |
| Product travels a journey narrative | Curved Path Travel |
| Elegant section-to-section transition | Section Peel Reveal |
| Dark → light section transition | Floating Product (section backgrounds change beneath) |
