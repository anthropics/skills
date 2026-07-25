---
name: apple-hig-expert
description: "Audits and designs iOS/macOS/watchOS/visionOS interfaces against the Apple Human Interface Guidelines, including the Liquid Glass design language (announced WWDC25, shipped with iOS 26/macOS Tahoe, Sept 2025). Use when reviewing an Apple-platform mockup or app for HIG compliance, checking contrast or tap-target sizes, or designing native-feeling Apple UI (e.g., 'audit my iOS app against the HIG', 'is this text readable on Liquid Glass?')."
license: MIT
metadata:
  version: 1.1.0
  author: Alireza Rezvani
  category: design
  updated: 2026-06-11
---

# Apple HIG Expert

Design and audit apps against the Apple Human Interface Guidelines (HIG, [developer.apple.com/design/human-interface-guidelines](https://developer.apple.com/design/human-interface-guidelines)), including the **Liquid Glass** design language. HIG content evolves with each OS release — when a claim matters, verify against the live HIG pages cited in `references/`.

## Before Starting

If `product-context.md` or `ios-design-context.md` exists, read it before asking questions. Then gather:

1. **Platform target**: iOS, macOS, watchOS, or visionOS?
2. **Current state**: new design or auditing an existing mockup/code?
3. **App category**: utility, productivity, game, social, etc.

## Modes

- **Mode 1 — Design from scratch**: pick the platform navigation paradigm and layout primitives first (see `references/platform-specifics.md`), then apply typography and semantic color (`references/visual-design.md`).
- **Mode 2 — HIG audit**: fill in `templates/hig-audit-template.md`, run `scripts/hig_checker.py` on every measurable element, and deliver a scored report (see Worked example below).

## The Compliance Tool

`scripts/hig_checker.py` (stdlib-only) has three subcommands:

```bash
# 1. Contrast ratio (WCAG formula; pass >= 4.5:1 for normal text)
python3 scripts/hig_checker.py contrast "#8E8E93" "#FFFFFF"
# -> Contrast Ratio: 3.26 [FAILED]

# 2. Tap-target size (pass >= 44x44 pt per HIG)
python3 scripts/hig_checker.py target 32 32
# -> Tap Target: 32x32 [FAILED]

# 3. Batch audit from JSON -> scorecard (starts at 100, -10 per violation)
python3 scripts/hig_checker.py batch audit.json
```

Batch input shape:

```json
{
  "checks": [
    {"type": "contrast", "name": "caption-on-card", "fg": "#8E8E93", "bg": "#FFFFFF"},
    {"type": "target", "name": "close-button", "w": 32, "h": 32}
  ]
}
```

**Scorecard rubric:** the batch score starts at 100 and subtracts 10 per failed check; violations are listed by element name. 90-100 = ship, 70-80 = fix before release, below 70 = systematic rework. Checks the tool cannot measure (VoiceOver labels, Dynamic Type behavior, Reduce Transparency) are assessed manually via the audit template and tagged with confidence.

## Worked example: iOS settings-screen audit

**Input:** mockup with body text `#1C1C1E` and captions `#8E8E93` on white cards, a 32x32 pt close button, and a 343x50 pt primary CTA.

**Run:**

```bash
python3 scripts/hig_checker.py batch audit.json
```

**Output (real):**

```json
{
  "score": 80,
  "violations": [
    "Contrast 3.26 fails for caption-on-card",
    "Target 32x32 small for close-button"
  ]
}
```

**Findings → fixes (bottom line first):**

> **HIG score 80/100 — two fixes before release.**
> 1. Captions fail contrast (3.26 < 4.5). Use `.secondaryLabel` (semantic color) instead of hardcoded `#8E8E93`, or darken to ≥ `#6E6E73` on white. 🟢 verified by tool.
> 2. Close button is 32x32 pt (< 44x44 minimum). Keep the glyph small but expand the hit region to 44x44 with padding/`contentShape`. 🟢 verified by tool.
> 3. Manual check: the card uses an ultra-thin material over a photo background — re-test caption contrast against the *busiest* underlying region and with Reduce Transparency on. 🟡 needs device test.

## Core Design Principles

1. **Liquid Glass** — translucent material hierarchy (announced at WWDC25, June 2025; shipped Sept 2025 across iOS 26, iPadOS 26, macOS Tahoe, watchOS 26, tvOS 26, visionOS 26). In SwiftUI, apply it via the `glassEffect` view modifier; keep hierarchy between content and controls. See `references/visual-design.md`.
2. **Accessibility first** — VoiceOver labels on every element, 44x44 pt minimum targets, 4.5:1 contrast for normal text (3:1 large text), Dynamic Type support. See `references/accessibility.md`.
3. **Platform ergonomics** — tab bars/thumb reach on iOS, sidebars + menu bar + shortcuts on macOS, ornaments + gaze states on visionOS, glanceable vertical layouts on watchOS. See `references/platform-specifics.md`.

## Proactive Triggers

Surface these WITHOUT being asked: low contrast over translucent layers; interactive elements under 44 pt; icon buttons with no accessibility label; density overload (no breathing room between glass layers).

## Communication

- **Bottom line first** — compliance status before details.
- **What + Why + How** — "Expand the hit region (What) because 32 pt targets fail the HIG minimum (Why); pad to 44x44 via contentShape (How)."
- **Confidence tagging** — 🟢 tool-verified / 🟡 needs device test / 🔴 assumed.

## Related Skills

- **ui-design-system**: token-based component systems (not platform HIG rules).
- **ux-researcher-designer**: persona/research validation (not visual styling).
- **landing-page-generator**: web marketing pages, not native apps.
