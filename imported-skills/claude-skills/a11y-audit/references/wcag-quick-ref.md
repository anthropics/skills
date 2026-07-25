# WCAG 2.2 Quick Reference — Level A & AA

## Perceivable

### 1.1 Text Alternatives

| Criterion | Level | Requirement | Common Violation |
|-----------|-------|-------------|------------------|
| 1.1.1 Non-text Content | A | All images have `alt` text; decorative images use `alt=""` or `role="presentation"` | `<img src="logo.png">` without alt |

### 1.2 Time-Based Media

| Criterion | Level | Requirement | Common Violation |
|-----------|-------|-------------|------------------|
| 1.2.1 Audio-only / Video-only | A | Provide transcript or audio description | Video without captions |
| 1.2.2 Captions | A | Captions for all prerecorded audio in video | Missing `<track kind="captions">` |
| 1.2.3 Audio Description | A | Audio description for prerecorded video | No descriptive track |
| 1.2.5 Audio Description (Prerecorded) | AA | Audio description for all prerecorded video | Same as 1.2.3 but stricter |

### 1.3 Adaptable

| Criterion | Level | Requirement | Common Violation |
|-----------|-------|-------------|------------------|
| 1.3.1 Info and Relationships | A | Semantic markup conveys structure | Using `<div>` instead of `<nav>`, `<main>`, `<header>` |
| 1.3.2 Meaningful Sequence | A | Reading order matches visual order | CSS flex/grid reordering without DOM reorder |
| 1.3.3 Sensory Characteristics | A | Don't rely solely on color, shape, position | "Click the red button" |
| 1.3.4 Orientation | AA | Content not restricted to portrait/landscape | CSS `orientation: portrait` lock |
| 1.3.5 Identify Input Purpose | AA | Input purpose identifiable via `autocomplete` | Missing `autocomplete="email"` on email inputs |

### 1.4 Distinguishable

| Criterion | Level | Requirement | Ratio |
|-----------|-------|-------------|-------|
| 1.4.1 Use of Color | A | Color not sole means of conveying info | Red-only error indicators |
| 1.4.2 Audio Control | A | Auto-playing audio has pause/stop | `autoplay` without `controls` |
| 1.4.3 Contrast (Minimum) | AA | Text: 4.5:1, Large text: 3:1 | Light gray text on white |
| 1.4.4 Resize Text | AA | Text resizable to 200% without loss | Fixed `px` font sizes |
| 1.4.5 Images of Text | AA | Use real text, not text in images | Logo text as PNG |
| 1.4.10 Reflow | AA | Content reflows at 320px width | Horizontal scrolling at mobile widths |
| 1.4.11 Non-text Contrast | AA | UI components and graphics: 3:1 | Low-contrast borders, icons |
| 1.4.12 Text Spacing | AA | No loss of content when spacing adjusted | Fixed-height containers clipping |
| 1.4.13 Content on Hover/Focus | AA | Dismissible, hoverable, persistent | Tooltips that disappear on mouse move |

## Operable

### 2.1 Keyboard Accessible

| Criterion | Level | Requirement | Common Violation |
|-----------|-------|-------------|------------------|
| 2.1.1 Keyboard | A | All functionality via keyboard | `onClick` without `onKeyDown` |
| 2.1.2 No Keyboard Trap | A | Focus can move away from any component | Modal without focus trap escape |
| 2.1.4 Character Key Shortcuts | A | Single-key shortcuts can be turned off | `accesskey` conflicts |

### 2.4 Navigable

| Criterion | Level | Requirement | Common Violation |
|-----------|-------|-------------|------------------|
| 2.4.1 Bypass Blocks | A | Skip navigation link | No "Skip to content" link |
| 2.4.2 Page Titled | A | Descriptive `<title>` | `<title>Untitled</title>` |
| 2.4.3 Focus Order | A | Logical tab order | `tabindex` > 0 |
| 2.4.4 Link Purpose | A | Link text describes destination | "Click here", "Read more" |
| 2.4.6 Headings and Labels | AA | Descriptive headings | Generic headings |
| 2.4.7 Focus Visible | AA | Visible focus indicator | `outline: none` without replacement |
| 2.4.11 Focus Not Obscured | AA | Focused element not hidden by sticky header | Fixed header covering focused element |

### 2.5 Input Modalities

| Criterion | Level | Requirement | Common Violation |
|-----------|-------|-------------|------------------|
| 2.5.1 Pointer Gestures | A | Multi-point gestures have single-point alternative | Pinch-to-zoom only |
| 2.5.2 Pointer Cancellation | A | Down-event doesn't trigger action | `mousedown` instead of `click` |
| 2.5.3 Label in Name | A | Visible label is in accessible name | Button shows "Submit" but `aria-label="btn1"` |
| 2.5.4 Motion Actuation | A | Motion-triggered actions have alternative | Shake-to-undo only |
| 2.5.7 Dragging Movements | AA | Drag has single-pointer alternative | Drag-and-drop only reordering |
| 2.5.8 Target Size | AA | Touch targets minimum 24x24 CSS pixels | Tiny mobile buttons |

## Understandable

### 3.1 Readable

| Criterion | Level | Requirement | Common Violation |
|-----------|-------|-------------|------------------|
| 3.1.1 Language of Page | A | `<html lang="en">` | Missing `lang` attribute |
| 3.1.2 Language of Parts | AA | `lang` on foreign-language spans | Mixed-language content without `lang` |

### 3.2 Predictable

| Criterion | Level | Requirement | Common Violation |
|-----------|-------|-------------|------------------|
| 3.2.1 On Focus | A | Focus doesn't trigger unexpected change | Auto-submitting on focus |
| 3.2.2 On Input | A | Input doesn't trigger unexpected change | Auto-navigating on select change |
| 3.2.3 Consistent Navigation | AA | Navigation consistent across pages | Menu order changes per page |
| 3.2.4 Consistent Identification | AA | Same function = same label | "Search" vs "Find" for same action |

### 3.3 Input Assistance

| Criterion | Level | Requirement | Common Violation |
|-----------|-------|-------------|------------------|
| 3.3.1 Error Identification | A | Errors described in text | Red border only, no message |
| 3.3.2 Labels or Instructions | A | Labels for required input | Placeholder as only label |
| 3.3.3 Error Suggestion | AA | Suggest corrections | "Invalid input" without guidance |
| 3.3.4 Error Prevention | AA | Reversible submissions for legal/financial | No confirmation for payment |
| 3.3.7 Redundant Entry | A | Don't ask for same info twice | Re-entering address in checkout |
| 3.3.8 Accessible Authentication | AA | No cognitive function test for login | CAPTCHA without audio alternative |

## Robust

### 4.1 Compatible

| Criterion | Level | Requirement | Common Violation |
|-----------|-------|-------------|------------------|
| 4.1.2 Name, Role, Value | A | Custom controls have accessible name and role | Custom dropdown without ARIA |
| 4.1.3 Status Messages | AA | Status updates announced without focus change | Toast without `aria-live` |
