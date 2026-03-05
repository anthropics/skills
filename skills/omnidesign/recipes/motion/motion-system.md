# Motion System

Comprehensive motion and animation guidelines including duration by interaction type, easing selection, reduced motion behavior, and animation choreography patterns.

## When to Use

**Use motion for:**
- Providing feedback on user interactions (hover, click, focus)
- Guiding attention to important elements
- Indicating state changes (loading, success, error)
- Creating smooth transitions between states
- Enhancing perceived performance

**Don't use motion for:**
- Decorative animations without purpose
- Auto-playing animations (let user control)
- Rapid or flashing animations (accessibility risk)
- Animations that distract from content
- Animations on every interaction (reserve for important moments)

## Motion Tokens

### Duration

| Token | Value | Use Case |
|-------|-------|----------|
| `duration.fast` | 150ms | Hover feedback, quick state changes |
| `duration.normal` | 300ms | Standard transitions, element entry |
| `duration.slow` | 500ms | Page transitions, major layout changes |
| `duration.slowest` | 800ms | Cinematic animations, hero sections |

**Duration selection:**
- **Fast (150ms)**: Hover states, button feedback, subtle transitions
- **Normal (300ms)**: Element appearance, modal open, form validation
- **Slow (500ms)**: Page transitions, hero animations, major state changes
- **Slowest (800ms)**: Cinematic sequences, landing page animations

### Easing

| Token | Curve | Use Case |
|-------|-------|----------|
| `easing.easeOut` | Cubic Bezier (0.33, 0.66, 0.66, 1) | Elements appearing, entering viewport |
| `easing.easeIn` | Cubic Bezier (0.33, 0, 0.66, 0.33) | Elements disappearing, leaving viewport |
| `easing.easeInOut` | Cubic Bezier (0.42, 0, 0.58, 1) | Smooth, natural motion for page transitions |
| `easing.spring` | Spring physics (stiffness: 300, damping: 30) | Bouncy, playful interactions, emphasis |

**Easing selection:**
- **easeOut**: Use when element is appearing or entering (feels responsive)
- **easeIn**: Use when element is disappearing or leaving (feels natural)
- **easeInOut**: Use for continuous motion or page transitions (smooth)
- **spring**: Use for emphasis, playful feedback, or attention-grabbing

### Semantic Motion Tokens

| Token | Duration | Easing | Use Case |
|-------|----------|--------|----------|
| `motion.hover` | 150ms | easeOut | Hover states, button feedback |
| `motion.enter` | 300ms | easeOut | Elements appearing, modal open |
| `motion.exit` | 150ms | easeIn | Elements disappearing, modal close |
| `motion.page` | 500ms | easeInOut | Page transitions, major layout changes |
| `motion.spring` | 300ms | spring | Bouncy interactions, emphasis |

## Implementation Patterns

### Hover Feedback

**Pattern:**
```
Element at rest → User hovers → Subtle visual change (150ms easeOut)
```

**Properties to animate:**
- Background color (primary → primary.hover)
- Scale (1 → 1.02 for lift effect)
- Shadow (shadow.card → shadow.card elevated)
- Opacity (100% → 100%, no change needed)

**Token usage:**
- Duration: `motion.hover` (150ms)
- Easing: `easing.easeOut`
- Properties: background-color, transform, box-shadow

**Example:**
```css
.button {
  background-color: color.interactive.primary;
  transition: background-color 150ms ease-out, transform 150ms ease-out;
}

.button:hover {
  background-color: color.interactive.primary.hover;
  transform: scale(1.02);
}
```

### Element Entry

**Pattern:**
```
Element hidden → Element appears → Fade in + slide up (300ms easeOut)
```

**Properties to animate:**
- Opacity (0% → 100%)
- Transform (translateY(10px) → translateY(0))
- Scale (0.95 → 1)

**Token usage:**
- Duration: `motion.enter` (300ms)
- Easing: `easing.easeOut`
- Properties: opacity, transform

**Example:**
```css
@keyframes slideUp {
  from {
    opacity: 0;
    transform: translateY(10px);
  }
  to {
    opacity: 1;
    transform: translateY(0);
  }
}

.modal {
  animation: slideUp 300ms ease-out;
}
```

### Element Exit

**Pattern:**
```
Element visible → User closes → Fade out + slide down (150ms easeIn)
```

**Properties to animate:**
- Opacity (100% → 0%)
- Transform (translateY(0) → translateY(10px))
- Scale (1 → 0.95)

**Token usage:**
- Duration: `motion.exit` (150ms)
- Easing: `easing.easeIn`
- Properties: opacity, transform

**Example:**
```css
@keyframes slideDown {
  from {
    opacity: 1;
    transform: translateY(0);
  }
  to {
    opacity: 0;
    transform: translateY(10px);
  }
}

.modal.closing {
  animation: slideDown 150ms ease-in;
}
```

### Page Transition

**Pattern:**
```
Page A visible → User navigates → Fade out (150ms) → Page B fades in (300ms)
```

**Properties to animate:**
- Opacity (100% → 0% → 100%)
- Scale (1 → 0.98 → 1)

**Token usage:**
- Duration: `motion.page` (500ms)
- Easing: `easing.easeInOut`
- Properties: opacity, transform

**Example:**
```css
@keyframes pageTransition {
  0% {
    opacity: 1;
    transform: scale(1);
  }
  50% {
    opacity: 0;
    transform: scale(0.98);
  }
  100% {
    opacity: 1;
    transform: scale(1);
  }
}

.page {
  animation: pageTransition 500ms ease-in-out;
}
```

### Loading State

**Pattern:**
```
User submits form → Spinner appears → Button disabled → Success/Error feedback
```

**Properties to animate:**
- Spinner rotation (0deg → 360deg, continuous)
- Button opacity (100% → 80%)
- Button pointer-events (auto → none)

**Token usage:**
- Duration: `motion.hover` (150ms) for state change
- Easing: `easing.easeOut`
- Properties: opacity, pointer-events

**Example:**
```css
@keyframes spin {
  from {
    transform: rotate(0deg);
  }
  to {
    transform: rotate(360deg);
  }
}

.spinner {
  animation: spin 1s linear infinite;
}

.button.loading {
  opacity: 0.8;
  pointer-events: none;
}
```

### Staggered List Animation

**Pattern:**
```
List appears → Each item fades in sequentially (50ms stagger)
```

**Properties to animate:**
- Opacity (0% → 100%)
- Transform (translateY(10px) → translateY(0))

**Token usage:**
- Duration: `motion.enter` (300ms)
- Easing: `easing.easeOut`
- Stagger: 50ms between items

**Example:**
```css
@keyframes slideUp {
  from {
    opacity: 0;
    transform: translateY(10px);
  }
  to {
    opacity: 1;
    transform: translateY(0);
  }
}

.list-item {
  animation: slideUp 300ms ease-out backwards;
}

.list-item:nth-child(1) { animation-delay: 0ms; }
.list-item:nth-child(2) { animation-delay: 50ms; }
.list-item:nth-child(3) { animation-delay: 100ms; }
```

## Reduced Motion Behavior

### Implementation

**Respect `prefers-reduced-motion` media query:**
```css
@media (prefers-reduced-motion: reduce) {
  * {
    animation-duration: 0.01ms !important;
    animation-iteration-count: 1 !important;
    transition-duration: 0.01ms !important;
  }
}
```

**Alternative approach (per-component):**
```css
@media (prefers-reduced-motion: reduce) {
  .button {
    transition: none;
  }
  
  .spinner {
    animation: none;
  }
}
```

### React Implementation

**Detect reduced motion preference:**
```javascript
const prefersReducedMotion = window.matchMedia('(prefers-reduced-motion: reduce)').matches;

// Use in conditional rendering or state
const duration = prefersReducedMotion ? 0 : 300;
```

**Apply to animations:**
```javascript
const animationProps = prefersReducedMotion 
  ? { animation: 'none' }
  : { animation: 'slideUp 300ms ease-out' };
```

## Animation Choreography

### Principle: Sequential Entrance

**Pattern:**
```
1. Background/container appears (fade in, 300ms)
2. Content fades in (300ms, 100ms delay)
3. CTA button scales in (300ms, 200ms delay)
```

**Effect:** Creates sense of anticipation and guides user attention

**Token usage:**
- All animations use `motion.enter` (300ms, easeOut)
- Stagger with 100ms delays between elements

### Principle: Unified Exit

**Pattern:**
```
1. CTA button fades out (150ms)
2. Content fades out (150ms, 50ms delay)
3. Background fades out (150ms, 100ms delay)
```

**Effect:** Feels cohesive and intentional

**Token usage:**
- All animations use `motion.exit` (150ms, easeIn)
- Stagger with 50ms delays

### Principle: Emphasis on Interaction

**Pattern:**
```
1. User hovers button → Scale up (150ms, spring)
2. User clicks button → Scale down (100ms, easeIn)
3. Loading state → Spinner rotates (continuous)
4. Success → Checkmark appears (300ms, spring)
```

**Effect:** Provides clear feedback at each step

**Token usage:**
- Hover: `motion.hover` (150ms, spring)
- Click: `motion.exit` (100ms, easeIn)
- Loading: Custom duration (1s, linear)
- Success: `motion.enter` (300ms, spring)

## Acceptance Criteria

- [ ] Hover animations use `motion.hover` token (150ms, easeOut)
- [ ] Element entry uses `motion.enter` token (300ms, easeOut)
- [ ] Element exit uses `motion.exit` token (150ms, easeIn)
- [ ] Page transitions use `motion.page` token (500ms, easeInOut)
- [ ] Spring animations use `motion.spring` token (300ms, spring easing)
- [ ] All animations respect `prefers-reduced-motion` media query
- [ ] No auto-playing animations (user-triggered only)
- [ ] No rapid animations (>3 per second)
- [ ] Staggered animations use 50-100ms delays between items
- [ ] Loading states show spinner with continuous rotation
- [ ] Success/error states use appropriate color tokens
- [ ] All animations use semantic motion tokens (not hardcoded values)

## Performance Considerations

### GPU Acceleration

**Use these properties for smooth 60fps animations:**
- `transform` (translate, rotate, scale)
- `opacity`

**Avoid these properties (cause repaints):**
- `width`, `height`, `left`, `top`
- `margin`, `padding`
- `background-color` (use opacity + background instead)

### Optimization

**Best practices:**
- Use `will-change: transform` for animated elements
- Use `transform: translateZ(0)` to force GPU acceleration
- Limit simultaneous animations (max 3-4 per screen)
- Use `requestAnimationFrame` for custom animations
- Debounce scroll/resize listeners

**Example:**
```css
.animated-element {
  will-change: transform;
  transform: translateZ(0);
}
```

## Accessibility

### Motion Sensitivity
- Respect `prefers-reduced-motion: reduce` for users with vestibular disorders
- Provide instant state changes when reduced motion is preferred
- Test with actual users who have motion sensitivity

### Clarity
- Use motion to clarify, not confuse
- Avoid rapid or flashing animations
- Ensure motion doesn't obscure content
- Provide alternative feedback (color, icon) in addition to motion

### Testing
- Test animations on low-end devices (60fps target)
- Test with `prefers-reduced-motion` enabled
- Test with screen readers (ensure motion doesn't interfere)
- Test on actual mobile devices for performance
