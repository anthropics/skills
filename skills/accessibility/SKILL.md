---
name: accessibility
description: Build accessible web interfaces that work for people with motor, cognitive, visual, and communication disabilities. Covers WCAG 2.2 AA compliance, motor accessibility patterns from AAC (Augmentative and Alternative Communication) development, keyboard navigation, screen reader compatibility, and inclusive testing methodology.
---

Build interfaces that work for everyone — not just sighted mouse users. Accessibility spans motor, cognitive, visual, and communication needs. This skill goes beyond "add alt text and check contrast" into real-world patterns from building AAC (Augmentative and Alternative Communication) tools for non-verbal individuals, informed by the clinical practices of Tobii Dynavox, PRC-Saltillo, and AssistiveWare, and grounded in WCAG 2.2.

## When to Use This Skill

- Building or reviewing any web UI
- Adding interactive components (modals, forms, menus, custom widgets)
- Working with dynamic content (SPAs, real-time updates, live data)
- Any project where users may have motor, cognitive, visual, or communication disabilities

## Core Principles

1. **Accessibility is not just vision.** Motor, cognitive, communication, and sensory needs all matter.
2. **Build for the full spectrum.** Keyboard-only users, switch access users, screen reader users, people with cognitive differences — all use the same web.
3. **Never rely on a single modality.** Not color alone. Not hover alone. Not mouse alone. Not sound alone.
4. **Test with real assistive technology.** Automated tools catch about 30% of issues. The rest requires manual testing.
5. **Accessible design is good design.** Curb cuts help everyone — captions help people in loud rooms, keyboard nav helps power users, clear layouts help everyone.

## Motor Accessibility

Motor accessibility is chronically underserved. Most guides skip it. These patterns come from building AAC communication systems for people with severe motor impairments.

### Touch Targets
- **Minimum 44x44px** for all interactive elements (WCAG 2.5.5)
- **48x48px on mobile** — fingers are less precise than cursors
- Add padding around targets, not just visual size — the tap area matters
- Space interactive elements at least 8px apart to prevent accidental activation

### Keyboard-Only Navigation
- Every interactive element must be **reachable and operable via keyboard alone**
- Tab moves between elements, Enter/Space activates, Escape dismisses
- Arrow keys navigate within composite widgets (tabs, menus, grids)
- Never require mouse hover, drag, or right-click as the only way to do something

### Switch Access
Switch users navigate by scanning — the interface highlights elements one at a time, and the user activates a switch to select.

- **One-switch mode**: Auto-scan advances through elements; single switch = select
- **Two-switch mode**: One switch = next, other switch = select
- **Design for scanning groups**: Organize elements in logical clusters (navigation, content, actions) so scanning doesn't require stepping through every element individually
- **Predictable layouts**: Grid-based layouts work best — random/overlapping positioning breaks scanning
- **Linear order matters**: DOM order must match visual order. CSS layout tricks that reorder visually but not in the DOM confuse switch users.

### Alternative Input Devices

Eye gaze trackers, head tracking, sip-and-puff devices, and joystick controllers all typically map to keyboard events. **If your UI works fully with a keyboard, it works with most alternative input devices.** This is why keyboard accessibility is the foundation of motor accessibility.

**Eye gaze** (infrared tracking of iris position):
- Selection via dwell: user looks at an element for a configurable duration (300–2000ms, start at 800ms) to activate it
- Requires generous hit areas — gaze is less precise than a mouse cursor
- Elements should not trigger on hover alone — dwell-click users will accidentally activate hover menus
- Screen can be divided into gaze zones for scroll control (look at top edge = scroll up)
- Calibration typically uses 9 points, collecting samples at each to build a screen coordinate mapping

**Head tracking** (camera tracks reflective dots or facial features):
- Maps head movement to mouse cursor position with dwell-click selection
- Similar to eye gaze but generally less precise — needs even larger targets
- Cursor jitter is common — apply smoothing (Kalman-like filtering) to gaze/head predictions

**Sip-and-puff** (air pressure through a tube):
- Sip = one action (e.g., advance/next), puff = another (e.g., select)
- Maps to keyboard events — software interprets pressure as key presses
- Requires full keyboard accessibility — no multi-key shortcuts, no mouse-only interactions

**Switch scanning timing** (configurable per user):
- Auto-scan interval: 500–3000ms (start at 1500ms, adjust based on user speed)
- Selection dwell: 200–1000ms (how long the switch must be held to confirm)
- Faster users can reduce intervals; users with slower motor control need longer intervals
- Always allow users to configure these values — there is no single correct timing

### Drag-and-Drop
- Always provide a keyboard alternative: arrow keys + Enter, or a menu-based "move to" action
- Sortable lists need "move up" / "move down" buttons as keyboard alternatives
- Never make drag-and-drop the only way to reorder or organize content

### Timing and Precision
- **Never require timed responses.** Always allow users to extend or disable time limits (WCAG 2.2.1)
- **Debounce click/tap events** to handle tremor — distinguish intentional clicks from accidental touches
- **Don't trigger actions on hover** — dwell-click users will accidentally activate hover-triggered menus
- Provide generous click/tap areas and avoid requiring precise cursor positioning

### Fatigue Detection

Motor fatigue degrades accuracy over time. Adaptive interfaces can detect and respond to fatigue in real time:

- **Metrics to monitor**: Response time (primary signal), error rate (missed targets, repeated taps), pause frequency (longer pauses between actions)
- **Weighted formula**: Response time (50%), error rate (30%), pause frequency (20%)
- **Adaptive responses**: As metrics degrade, enlarge touch targets, slow scanning intervals, reduce the number of options shown, increase spacing between elements
- **Implementation**: Track a rolling window of the last 10-20 interactions. Compare against the user's baseline from their first few minutes of use.

### Pointer Gestures and Cancellation

WCAG 2.1 requires alternatives for complex pointer interactions:

- **2.5.1 Pointer Gestures (Level A)**: Any functionality using multipoint (pinch) or path-based (swipe) gestures must also work with single-point activation (tap/click). People with motor disabilities may only be able to perform single-tap gestures.
- **2.5.2 Pointer Cancellation (Level A)**: Don't trigger actions on the down-event (mousedown/touchstart). Use up-events (mouseup/touchend/click) so users can abort by moving away. This is critical for tremor — users who accidentally tap can move their finger away to cancel.
- **2.5.4 Motion Actuation (Level A)**: Don't require shaking, tilting, or device gestures. If you support them, provide button alternatives and let users disable motion triggers.

### AAC Color Coding (Modified Fitzgerald Key)

Communication boards follow the Modified Fitzgerald Key — the dominant color-coding standard in AAC. Two systems exist (Modified Fitzgerald Key and Goossens'/Crain/Elder), but Modified Fitzgerald Key is more widely used:

| Color | Word Type | Example |
|-------|-----------|---------|
| Green | Verbs (actions) | go, want, eat |
| Orange | Nouns (things) | ball, cup, dog |
| Yellow | Pronouns | I, you, he, she |
| Blue | Adjectives (descriptors) | big, hot, happy |
| Brown | Adverbs (manner) | quickly, here |
| Purple | Questions | who, what, where |
| Pink | Prepositions, social words | in, on, hello, please |
| Red | Important, negation, emergency | stop, no, help, more |
| White/Gray | Determiners, conjunctions | the, a, and, or |

Respect these conventions in any communication-focused interface. Users and clinicians rely on color consistency across tools. Before using color coding, verify the user doesn't have a color vision deficiency that would affect their perception of the chosen colors.

### Spatial Consistency for Muscle Memory

Fixed positions for recurring actions build motor memory and eventually automaticity (performing the action without conscious thought about location):

- **Communication boards**: Core vocabulary (WHO/WHAT/WHERE/WHEN) should always occupy the same spatial positions across all pages/screens
- **Navigation elements**: Search, home, back, and primary actions should never move between pages — users with motor impairments develop muscle memory for frequently-used controls
- **Grid layouts**: Keep the same grid dimensions across pages. Changing grid size forces motor re-planning, which is cognitively and physically expensive for switch and gaze users.
- **General principle**: Consistency between pages leads to motor-plan development. The more consistent the layout, the less motor and cognitive effort required over time.

## Cognitive Accessibility

- **Consistent navigation**: Same layout on every page, predictable behavior, visible breadcrumbs
- **Plain language**: Short sentences, common words, avoid jargon — explain technical terms when needed
- **Dyslexia-friendly options**: Offer increased letter-spacing (0.12em+), word-spacing (0.16em+), relaxed line height (1.5+), and medium font weight. See `reference/accessibility.css` for a `.dyslexia-friendly` class.
- **Dyslexia font stack**: `Atkinson Hyperlegible, Lexend, OpenDyslexic, Aptos, Calibri, sans-serif`. Atkinson Hyperlegible (Braille Institute — designed for low vision, distinct letterforms), Lexend (research shows ~20% reading fluency improvement over Times New Roman), OpenDyslexic (weighted letterforms to reduce rotation), Aptos (Microsoft's accessibility-focused default). Offer as a user preference, not a forced default.
- **Reduced motion**: Respect `prefers-reduced-motion` — disable all animations and transitions. See `reference/accessibility.css` for the media query pattern. Provide on-page controls too — not all users know about OS-level settings.
- **Visible focus**: Bold, high-contrast (3:1 minimum) focus outlines so users always know where they are in the page
- **Error prevention**: Confirm destructive actions, validate inline before submission, provide clear recovery paths with specific guidance
- **Chunking**: Break content into small, digestible sections with descriptive headings — don't present walls of text
- **Predictability**: Buttons should do what they say. Links should go where they describe. Don't surprise users.
- **Memory support**: Don't require users to remember information from a previous step. Show context inline. Avoid multi-step processes that depend on recalling earlier choices.
- **Attention support**: Minimize distractions. No auto-playing media, no flashing content, no unexpected pop-ups. Allow users to pause or suppress non-critical notifications.

## Visual Accessibility

### Contrast
- **Normal text**: 4.5:1 contrast ratio against background
- **Large text** (18px+ regular, or 14px+ bold): 3:1 contrast ratio
- **UI components and graphics**: 3:1 contrast ratio for borders, icons, and interactive states

### Color Independence
Never convey information through color alone. Add icons, patterns, text labels, or shapes alongside color:
- Status indicators: green dot + "Active" text label
- Form errors: red border + error icon + text message
- Data visualizations: color + pattern fills + direct labels

### Specialized Vision Needs
- **CVI (Cortical Visual Impairment)**: Support high-contrast themes — yellow text on black background works well
- **Photophobia**: Offer low-brightness themes with muted colors
- **Color blindness**: Test with deuteranopia (red-green, ~8% of males) and protanopia simulators. Never use red/green as the only differentiator.

### Alt Text

Four styles for different contexts:

- **Concise** (social media, thumbnails): ~125 characters. Describe the essential content and purpose. "Bar chart showing renewable energy adoption doubling between 2020 and 2025"
- **Detailed** (documentation, educational content): ~300 characters. Describe purpose first, then visual details. "Scatter plot comparing student test scores to study hours. Positive correlation visible — students studying 10+ hours score 20% higher on average. Outliers at low study hours suggest other factors."
- **Functional** (interface elements): Describe what it does, not what it looks like. "Submit form" not "Blue button with arrow icon"
- **Neurodivergent** (social/emotional support): Explicitly describe facial expressions AND their likely meanings ("smiling, suggesting friendliness"), spell out body language, describe social cues and power dynamics, flag potential misunderstandings. Helps autistic users and others who find nonverbal cues difficult to interpret.

Rules:
- Decorative images: empty `alt=""` always — never omit the attribute entirely
- Charts and graphs: describe the trend or insight, not every data point
- Complex images: use `aria-describedby` pointing to a longer text description nearby
- Icons with text labels: `alt=""` on the icon (the label does the work)
- Icons without text labels: `alt="Description of action"` or `aria-label`

Output validation (post-processing generated alt text):
- Strip common prefixes: "alt text:", "description:", "image shows:", "a photo of", "an image of"
- Ensure terminal punctuation — add a period if the text doesn't end with `.` `!` or `?`
- Truncate at sentence boundaries, never mid-word — readability over character count
- Normalize whitespace and fix sentence spacing (single space after periods)
- Never wrap the output in quotation marks
- Length limits: ~125 characters for social media; 125–300 characters for web content depending on context

### System Integration
- **Forced colors mode**: Windows High Contrast mode overrides your styles. Test that borders, outlines, and focus indicators remain visible. See `reference/accessibility.css` for the `forced-colors` media query. Use the `forced-colors: active` media query (the `-ms-high-contrast` query is deprecated). Embrace CSS system colors (`Canvas`, `CanvasText`, `LinkText`, `ButtonFace`, etc.) which auto-adapt.
- **Contrast mode**: Use `@media (prefers-contrast: more)` to provide increased contrast when the OS requests it. This is distinct from forced colors — it enhances your existing theme rather than overriding it.
- **Text scaling**: UI must remain functional at 200% browser zoom with no content loss or overlap (WCAG 1.4.4)
- **No images of text**: Use real text styled with CSS. Images of text can't be resized, searched, or read by screen readers.

## Screen Reader Compatibility

### Semantic Structure
- Use proper landmarks: `<header>`, `<nav>`, `<main>`, `<aside>`, `<footer>`
- Use `aria-label` to differentiate multiple landmarks of the same type (e.g., "Primary navigation" vs "Footer navigation")
- Heading hierarchy: h1 then h2 then h3 — never skip levels. Every section needs a heading.
- Use `<button>` for actions, `<a>` for navigation — not `<div onclick>` or `<span role="button">`

### Dynamic Content
- **Live regions**: Use `aria-live="polite"` for status updates (results count, save confirmation), `"assertive"` for errors and urgent alerts
- **Route changes in SPAs**: Manage focus — move it to the new page's main heading or content area after navigation
- **Loading states**: Use `aria-busy="true"` on containers being updated, announce completion via live region

### Forms
- Every input needs a visible `<label>` element associated via `for`/`id`, or `aria-label` for icon-only inputs
- Group related fields with `<fieldset>` and `<legend>`
- Error messages: associate with `aria-describedby`, announce with `aria-live`
- Required fields: use `aria-required="true"` and visible indicator (not just an asterisk)

### Data Tables
- Use `<th>` with `scope="col"` or `scope="row"` for header cells
- Add `<caption>` describing the table's purpose
- For complex tables, use `id`/`headers` attributes to associate data cells with their headers

See `reference/patterns.md` for copy-paste implementations of focus traps, roving tabindex, screen reader announcements, and skip links.

## Communication and Speech

- **No voice-only interfaces**: Always provide text or touch alternatives to voice input
- **Captions and transcripts**: All audio and video content needs synchronized captions. Provide full transcripts for audio-only content.
- **AAC integration**: If building communication tools, follow the Modified Fitzgerald Key color conventions above and support standard symbol systems (PCS by Tobii Dynavox, SymbolStix by n2y, Blissymbolics by BCI — 6,000+ symbols with Unicode code points)
- **Text-to-speech considerations**: Keep text content well-structured so TTS reads it in logical order. Avoid layout tables and CSS order tricks that break reading flow.

## WCAG 2.2 AA Checklist

Use this as a quick audit checklist when reviewing any interface. Includes WCAG 2.2 criteria (marked with *2.2*).

### Perceivable
- [ ] Images have descriptive alt text (or empty `alt=""` for decorative)
- [ ] Video has synchronized captions
- [ ] Color is not the sole means of conveying information
- [ ] Text contrast meets 4.5:1 (normal) / 3:1 (large)
- [ ] Text resizable to 200% without loss
- [ ] No images of text

### Operable
- [ ] All functionality available via keyboard
- [ ] No keyboard traps — focus can always move away
- [ ] Skip navigation link present
- [ ] Page titles are descriptive
- [ ] Focus indicator visible on every interactive element
- [ ] No time limits (or user can extend)
- [ ] No content flashing more than 3 times per second
- [ ] Multipoint/path-based gestures have single-point alternatives (2.5.1)
- [ ] Down-events don't trigger actions — use up-events for pointer cancellation (2.5.2)
- [ ] *2.2* Focus is not entirely obscured by sticky headers, banners, or overlays (2.4.11)
- [ ] *2.2* Interactive targets are at least 24x24px with adequate spacing (2.5.8)
- [ ] *2.2* Dragging operations have single-pointer alternatives (2.5.7)
- [ ] *2.2* Help mechanisms are consistent across pages (3.2.6)

### Understandable
- [ ] `<html lang="en">` (or appropriate language) is set
- [ ] Navigation is consistent across pages
- [ ] Form inputs have clear labels and instructions
- [ ] Error messages are specific and suggest fixes
- [ ] *2.2* Redundant entry: don't require re-entering information already provided (3.3.7)

### Robust
- [ ] HTML validates (no duplicate IDs, proper nesting)
- [ ] ARIA attributes used correctly (roles, states, properties)
- [ ] Custom controls expose name, role, and value to assistive technology
- [ ] Status messages are programmatically determinable

## Testing

Automated tools catch about 30% of accessibility issues. Manual testing is essential.

### Automated (Run First)
```bash
# Lighthouse (built into Chrome DevTools)
npx lighthouse <url> --only-categories=accessibility

# axe-core (more thorough)
npx @axe-core/cli <url>

# pa11y (CI-friendly)
npx pa11y <url>
```

### Included Scripts

This skill includes 10 standalone Python scripts (stdlib only — no pip install needed) for targeted audits. All accept HTML files as arguments and support `--format json` for CI integration.

| Script | Domain | What it checks |
|--------|--------|---------------|
| `contrast-checker.py` | Visual | WCAG contrast ratio between two hex colors |
| `cvi-contrast-check.py` | CVI / Low vision | CVI-safe contrast (10:1+), photophobia, deuteranopia presets |
| `alt-text-audit.py` | Visual / SR | Missing, empty, or suspicious alt text on images |
| `heading-outline.py` | Cognitive / SR | Heading hierarchy — skipped levels, missing h1, empty headings |
| `landmark-audit.py` | SR | ARIA landmark structure — missing main, unlabeled duplicates |
| `link-text-audit.py` | SR / Cognitive | Vague link text ("click here"), empty links, image-only links |
| `focus-order-check.py` | Motor / Keyboard | Positive tabindex, non-focusable interactive elements, aria-hidden conflicts |
| `target-size-check.py` | Motor | Undersized touch targets (WCAG 2.5.8: 24px AA, 44px AAA) |
| `color-only-check.py` | Color blindness | Patterns where color is the sole information carrier |
| `timing-audit.py` | Motor / Cognitive | setTimeout, autoplay, animations without reduced-motion support |

```bash
# Run individual checks
python3 scripts/contrast-checker.py "#333333" "#f5f5f5"
python3 scripts/cvi-contrast-check.py --preset cvi
python3 scripts/alt-text-audit.py index.html
python3 scripts/heading-outline.py index.html
python3 scripts/landmark-audit.py index.html
python3 scripts/link-text-audit.py index.html
python3 scripts/focus-order-check.py --show-all index.html
python3 scripts/target-size-check.py --threshold 44 index.html
python3 scripts/color-only-check.py index.html
python3 scripts/timing-audit.py index.html app.js styles.css

# Run all HTML audits at once
for script in scripts/*-audit.py scripts/*-check.py; do
  python3 "$script" index.html
done

# JSON output for CI pipelines
python3 scripts/alt-text-audit.py --format json index.html | jq '.issues'
```

### Manual Testing Checklist
1. **Keyboard**: Tab through the entire page. Can you reach and operate every interactive element? Is focus order logical? Is the focus indicator always visible?
2. **Screen reader**: Test with NVDA (Windows), VoiceOver (Mac/iOS), or TalkBack (Android). Are all elements announced correctly? Do dynamic updates get announced?
3. **Zoom**: Set browser zoom to 200%. Does anything overflow, overlap, or become inaccessible?
4. **Motion**: Enable `prefers-reduced-motion` in your OS or browser dev tools. Do all animations stop?
5. **Color**: Use a color blindness simulator (Chrome DevTools > Rendering > Emulate vision deficiency). Is all information still conveyed?
6. **Switch simulation**: Tab through the page one element at a time. Does the order make sense for someone who can only go forward? Are elements grouped logically?
7. **Forced colors**: Enable Windows High Contrast mode or emulate it (Edge DevTools > Rendering > Emulate forced-colors: active). Are borders, outlines, and focus indicators still visible?
8. **Target size**: Measure interactive elements — are they at least 24x24px (WCAG 2.2 AA) or 44x44px (AAA)?
9. **Cognitive walkthrough**: Can a first-time user complete the primary task without documentation? Are error states clear and recoverable?

### Common Issues and Fixes

| Issue | Who It Affects | Fix |
|-------|---------------|-----|
| Missing alt text | Screen reader users | Add descriptive `alt` attribute |
| Low contrast text | Low vision, aging eyes | Increase to 4.5:1 ratio |
| No focus indicator | Keyboard/switch users | Add `:focus-visible` outline (3px+) |
| Missing form labels | Screen reader users | Associate `<label>` with `for` attribute |
| Div-based buttons | All AT users | Use `<button>` element instead |
| Hover-only content | Motor impaired, touch users | Make content keyboard/touch accessible |
| Auto-playing media | Cognitive, screen reader | Add pause/stop controls, no autoplay |
| Missing skip link | Keyboard/switch users | Add skip link as first focusable element |
| ARIA misuse | Screen reader users | Remove ARIA if native HTML works; validate roles |
| Inaccessible modals | Keyboard/switch users | Use native `<dialog>` with `showModal()` — handles focus automatically. For custom modals: trap focus, Escape to close, restore focus on dismiss |
| Small touch targets | Motor impaired, tremor | Minimum 24x24px (WCAG 2.2 AA), 44x44px preferred, 48px on mobile |
| Actions on pointer down | Motor impaired, tremor | Use `click` events (up-event), not `mousedown`/`touchstart` — allows cancellation by moving away |
| Hover-only menus | Eye gaze, switch users | Open menus on click/Enter, not hover. Hover menus fire accidentally with dwell-click |
| Inconsistent layout | Motor impaired, cognitive | Keep navigation and key actions in fixed positions across all pages — muscle memory matters |
