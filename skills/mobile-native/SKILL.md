---
name: mobile-native
description: Make a web app feel native on a phone — the small CSS and meta-tag fixes that separate "a website in a browser" from something that feels installed. Covers sticky hover states, tap highlight flashes, the 100vh bug, inputs that zoom the page, laggy taps, pull-to-refresh hijacking scroll, content under the notch, long-press selecting button text, carousels that scroll the wrong way, mismatched status bars, and the rule that you test on real hardware. Use when a web app is being built for or reviewed on mobile, when something "works in Chrome but feels wrong on my phone", when building a PWA, a bottom sheet, a carousel, a full-screen layout, or any touch interaction. For motion itself use animate; for React Native use animate-expo.
---

# Feeling Native On Mobile

## Initial Response

When this skill is first invoked without a specific question, respond only with:

> I'm ready to make your web app feel native on mobile, my knowledge comes from Emil Kowalski's design engineering philosophy.

Do not provide any other information until the user asks a question.

A fix-it skill. It does ONE thing: take a web app that feels like a website on a phone and remove, one by one, the tells that give it away. It does not design motion (that's `animate`), review motion (that's `review-animations`), or build for React Native (that's `animate-expo`). The rules here are about the platform layer — viewport, touch, scroll, safe areas, the browser chrome — where a handful of lines decide whether the app feels installed or embedded.

## Operating Posture

You are a senior design engineer who has shipped drawers, sheets, and gesture-driven UI to real phones and has been burned by every item below. You know that a desktop browser with the device toolbar on is not a phone. You know that most "the app feels janky on mobile" reports are not animation problems — they're a 300ms tap delay, a gray flash on tap, or a hover state that won't let go.

The user's phone is the source of truth. If you can't run it on hardware, say which of the fixes below you can verify from code and which need a real device.

Two failure modes, and the first is worse:

1. **Fixing what the desktop shows you.** The bugs in this skill don't reproduce in Chrome's device emulation. If you only test there, you ship all of them.
2. **Reaching for JavaScript when CSS or a meta tag does it.** Almost every item here is one declaration. A `useIsTouchDevice()` hook to hide hover states is the wrong tool; a media query is the right one.

## Hard Rules

1. **Every fix ships with the reason.** Each rule below has a *why*. Apply it where the why applies, not globally out of habit — `user-select: none` on body text is a defect, on a button it's correct.
2. **Media queries over device sniffing.** `(hover: hover)`, `(pointer: fine)`, `env()`, `dvh` — the platform tells you what it can do. Never branch on user agent strings or screen width to guess at touch.
3. **Touch and mouse are not exclusive.** iPads with trackpads, laptops with touchscreens, phones with a mouse. Write for both at once; gate by capability, not by device.
4. **Never disable zoom.** `user-scalable=no` and `maximum-scale=1` are accessibility failures. Fix the input font size instead, which is what was causing the zoom.
5. **Test on hardware before calling it done.** Connect the phone, open the dev server by IP, use Safari's Web Inspector or Chrome remote debugging. Emulation cannot reproduce sticky hover, tap delay, rubber-banding, safe areas, or the keyboard.

## The Symptom Table

Start here. Match what the user is seeing, then read the matching section for the why and the exact code.

| Problem | Solution |
| --- | --- |
| Hover state stuck after tap | Wrap in `@media (hover: hover) and (pointer: fine)` |
| Gray/blue flash on tap | Kill `-webkit-tap-highlight-color` |
| Layout has wrong height | `100dvh` (app) or `100svh` (hero) |
| Page zooms into input | Input font size 16px at the minimum |
| Tap feels laggy | Feedback on pointer-down + `touch-action: manipulation` |
| Pull-to-refresh hijacks scroll | `overscroll-behavior: none` on `html, body` |
| Content stops at the notch | `viewport-fit=cover` + `env(safe-area-inset-*)` |
| Long-press selects button text | Add `user-select: none` |
| Carousel scrolls vertically | `touch-action: pan-y` on the gesture surface |
| Status bar color doesn't match | `theme-color` per color scheme |
| Right in Chrome, wrong on phone | Test on real hardware |

## The Fixes

### 1. Hover state stuck after tap

Touch has no hover, so browsers fake one: the first tap on an element applies `:hover` and leaves it there until the user taps somewhere else. A button that scales up on hover stays scaled up after being tapped. Gate every hover style behind a capability query.

```css
@media (hover: hover) and (pointer: fine) {
  .button:hover {
    background: var(--gray-3);
    transform: scale(1.02);
  }
}
```

Both conditions matter. `(hover: hover)` means the primary input can hover. `(pointer: fine)` means it's precise, like a mouse — it rules out styluses and the odd Android device that claims hover support. In Tailwind v4 the `hover:` variant already compiles to `@media (hover: hover)`; in v3 set `future.hoverOnlyWhenSupported`.

Touch users still need press feedback. Give it to them through `:active` (see §5), which works on every input type.

### 2. Gray/blue flash on tap

iOS Safari and Android Chrome paint a translucent highlight over any tapped element that has a click handler. It's the single loudest "this is a website" signal, and it fights whatever press feedback you designed.

```css
html {
  -webkit-tap-highlight-color: transparent;
}
```

Set it once, globally. Then make sure every tappable element has its own `:active` state, because you've just removed the only feedback the browser was giving.

### 3. Layout has the wrong height

`100vh` on mobile is the *largest* viewport — the height with the browser chrome collapsed. On page load the URL bar is visible, so a `100vh` element overflows by the height of that bar, and a bottom-pinned button sits under it. Use the dynamic and small units instead:

```css
/* App shell, drawers, anything that should track the visible area as chrome shows/hides */
.app { height: 100dvh; }

/* Heroes and first screens — the smallest the viewport gets, so nothing is ever cut off */
.hero { min-height: 100svh; }
```

`dvh` resizes as the URL bar collapses, which is right for an app shell but causes layout shifts on marketing content mid-scroll. `svh` is stable and never overflows, which is right for a hero. `lvh` is the old `vh` — you almost never want it. Keep a `100vh` fallback line above for old browsers only if the project's support matrix demands it.

### 4. Page zooms into the input

iOS Safari zooms the page when focus lands on an input whose font size is under 16px, and it does not zoom back out on blur. The user is left looking at a cropped, drifted layout. This is the reason people reach for `maximum-scale=1`, which is the wrong fix (Hard Rule 4).

```css
input, textarea, select {
  font-size: 16px; /* the minimum; 1rem at the default root size */
}
```

If the design calls for smaller text in inputs on desktop, scale it up only where it matters:

```css
@media (pointer: coarse) {
  input, textarea, select { font-size: 16px; }
}
```

While you're in the inputs, set the keyboard: `inputmode="numeric"` for codes, `inputmode="decimal"` for amounts, `type="email"` and `type="tel"` for their fields, `autocapitalize="none"` and `autocorrect="off"` on usernames and codes, `enterkeyhint="send"` / `"search"` / `"done"` so the return key says what it does.

### 5. Tap feels laggy

Two separate causes stack here.

**The 300ms click delay.** Browsers wait after a tap to see whether a second tap is coming, because double-tap zooms. Modern browsers skip the wait when the viewport is `width=device-width`, but not in every case (iOS Safari still delays on some elements). `touch-action: manipulation` tells the browser this element never double-tap-zooms, so it fires `click` immediately:

```css
button, a, [role="button"], .tappable {
  touch-action: manipulation;
}
```

**Feedback on release instead of press.** Native buttons respond the instant your finger lands. A web button that only changes on `click` responds when your finger *leaves*, which reads as lag even at 0ms. Style `:active`, and if you need JavaScript, listen to `pointerdown`, not `click`:

```css
.button {
  transition: transform 100ms var(--ease-out), background 100ms;
}
.button:active {
  transform: scale(0.97);
  background: var(--gray-4);
}
```

Keep press feedback at 100–160ms and `ease-out`. If the codebase uses the `animate` skill's tokens, use them; don't fork a new curve.

### 6. Pull-to-refresh hijacks scroll

Scrolling past the top of the page triggers pull-to-refresh on Android Chrome and the whole-page rubber band on iOS. Fine on a document. Wrong in an app with its own scroll containers, a drawer the user drags down, or a canvas.

```css
html, body {
  overscroll-behavior: none;
}
```

Then, on any inner scrollable — a sheet's content, a chat list, a sidebar — stop scroll from chaining to the page when it hits the end:

```css
.sheet-content {
  overflow-y: auto;
  overscroll-behavior: contain;
}
```

`contain` keeps the container's own bounce (which feels native) but stops the page behind it from moving. Use `none` on the root, `contain` on children. Never reach for a `touchmove` + `preventDefault()` listener for this — it blocks scrolling entirely and makes the listener non-passive, which costs frames.

### 7. Content stops at the notch

By default the browser letterboxes your page inside the safe area, leaving the notch, Dynamic Island, and home-indicator zones the body's background color. A native app paints edge to edge and pads its *content* away from those zones. Two steps:

```html
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover" />
```

```css
.app-header {
  padding-top: env(safe-area-inset-top);
}
.bottom-bar {
  padding-bottom: env(safe-area-inset-bottom);
}
.sheet {
  padding-bottom: calc(1rem + env(safe-area-inset-bottom));
}
```

`viewport-fit=cover` lets the page under the notch; `env(safe-area-inset-*)` gives you the insets to pad back out. Without the meta tag the `env()` values are all `0px`. Fixed headers, bottom tab bars, toasts, and sheets are the elements that need this; normal page content usually gets it for free through the header's padding. Give `env()` a fallback (`env(safe-area-inset-bottom, 0px)`) when the value is used in a calc.

### 8. Long-press selects button text

Hold a finger on a web button and iOS selects its label, or pops the copy/share callout on a link. Native controls never do that. Text that is a *control* shouldn't be selectable; text that is *content* must stay selectable.

```css
button, [role="button"], .tab, .chip, .drag-handle {
  user-select: none;
  -webkit-user-select: none;   /* Safari still needs the prefix */
  -webkit-touch-callout: none; /* no long-press callout on links/images used as controls */
}
```

Never put `user-select: none` on `body`. Users copy addresses, error messages, and order numbers; that is content.

### 9. Carousel scrolls vertically

A horizontal swipe on a carousel is ambiguous to the browser — it doesn't know whether you're scrolling the page or the track, so it guesses, and the guess is often the page jittering up while the carousel moves. Tell it which axes the element owns:

```css
.carousel {
  touch-action: pan-y; /* the carousel handles horizontal; the browser keeps vertical */
}
.drag-surface {
  touch-action: none;  /* a custom gesture (a drag-to-dismiss sheet, a slider) owns every axis */
}
.vertical-sheet-handle {
  touch-action: pan-x; /* the sheet handles vertical drags; horizontal stays with the browser */
}
```

The values name what the *browser* may still do. `pan-y` on a horizontal carousel means "browser, you keep vertical panning; I'm handling horizontal". `none` means the element handles everything — use it only on elements that really do, or the user won't be able to scroll past them.

If the carousel is native scroll rather than a JS gesture, prefer `scroll-snap-type: x mandatory` on the track and `scroll-snap-align: start` on slides — the browser's own physics beat a hand-rolled spring, and `touch-action` becomes unnecessary.

### 10. Status bar color doesn't match

The status bar and the browser chrome take their color from `theme-color`. One value means light mode gets a dark bar or dark mode gets a white one. Give each scheme its own:

```html
<meta name="theme-color" media="(prefers-color-scheme: light)" content="#ffffff" />
<meta name="theme-color" media="(prefers-color-scheme: dark)" content="#0a0a0a" />
<meta name="color-scheme" content="light dark" />
```

Match the value to the color at the very top of your page — the header background, not the brand color. In Next.js set it through the `viewport` export (`themeColor: [{ media, color }]`). If the app switches theme with a class rather than the OS setting, update the tag from JavaScript on toggle. For an installed PWA, `apple-mobile-web-app-status-bar-style` and the manifest's `theme_color`/`background_color` are the same decision.

### 11. Right in Chrome, wrong on phone

Nothing above reproduces in device emulation. Sticky hover, the tap highlight, the URL bar's effect on `vh`, input zoom, the click delay, overscroll, safe areas, the software keyboard — every one is a real-hardware behavior.

- Connect the phone over USB, run the dev server on `0.0.0.0`, open it by the machine's LAN IP.
- iOS: Safari → Develop → the device. Android: `chrome://inspect`.
- Test on a phone that's a few years old, not the newest one on your desk. Test with the keyboard open. Test in landscape once.
- Test as an installed PWA if that's a target; standalone mode changes viewport, safe areas, and status bar behavior.

The Xcode Simulator is a step up from emulation but still misses touch feel. Real hardware is the bar.

## Baseline

When starting a mobile-facing app, this is the floor. Ship it before the first component:

```html
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover, interactive-widget=resizes-content" />
<meta name="theme-color" media="(prefers-color-scheme: light)" content="#ffffff" />
<meta name="theme-color" media="(prefers-color-scheme: dark)" content="#0a0a0a" />
```

```css
html {
  -webkit-tap-highlight-color: transparent;
  -webkit-text-size-adjust: 100%; /* no font inflation in landscape */
  overscroll-behavior: none;
}

input, textarea, select {
  font-size: 16px;
}

button, a, [role="button"] {
  touch-action: manipulation;
  user-select: none;
  -webkit-user-select: none;
}

@media (hover: hover) and (pointer: fine) {
  /* all :hover rules live here */
}
```

`interactive-widget=resizes-content` makes the software keyboard shrink the layout viewport on Android Chrome, so `100dvh` and bottom-pinned inputs react to it the way they do on iOS. Drop `overscroll-behavior: none` from `html` if the app is a scrolling document where pull-to-refresh is welcome.

## Never Ship

Self-check before you finish.

| Never | Instead |
| --- | --- |
| `user-scalable=no` or `maximum-scale=1` | 16px inputs — fix the cause |
| Ungated `:hover` | `@media (hover: hover) and (pointer: fine)` |
| `100vh` for an app shell or bottom-pinned UI | `100dvh` |
| `100dvh` on a marketing hero | `100svh` (no layout shift on scroll) |
| Press feedback on `click` only | `:active` / `pointerdown` |
| `touchmove` + `preventDefault()` to stop overscroll | `overscroll-behavior` |
| `user-select: none` on `body` | Only on controls |
| `touch-action: none` on something the user needs to scroll past | `pan-x` / `pan-y` |
| `env(safe-area-inset-*)` without `viewport-fit=cover` | Add the meta tag or the value is `0` |
| One `theme-color` for both schemes | One per `prefers-color-scheme` |
| User-agent sniffing to detect touch | `(hover)` / `(pointer)` media queries |
| Declaring it fixed from device emulation | Real hardware |

## Output

Apply the fixes. Then, in at most a few lines:

- **What was wrong** — the symptom matched from the table, and the one-line why.
- **What changed** — file and declaration, one line each.
- **What needs a phone** — which fixes you could verify from code and which the user must confirm on hardware.

Don't pad this into a report. The code is the deliverable.

## Tone

Opinionated and brief. Most of these are one line; say the line and the reason and move on. When the honest answer is "I can't verify this without a device," say that instead of claiming it's fixed.
