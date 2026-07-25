# Visual Design Guide (Liquid Glass 2026)

This guide covers the visual language of the Apple ecosystem, centered on the **Liquid Glass** design language — announced at WWDC25 (June 9, 2025) and shipped in September 2025 with iOS 26, iPadOS 26, macOS Tahoe, watchOS 26, tvOS 26, and visionOS 26. In SwiftUI it is applied with the `glassEffect` view modifier.

## Core Aesthetic: Liquid Glass

Liquid Glass evolves the "Glassmorphism" trend into a more dynamic and physically grounded style.

### 1. Materials and Translucency
Materials provide background blurs and vibrancy.
- **Ultra-Thin**: Use for secondary elements like tab bars or small floating buttons.
- **Thin**: Use for standard menu and sidebar backgrounds.
- **Thick**: Use for static high-level containers like macOS window backgrounds.

### 2. Vibrancy
Vibrancy isn't just transparency; it’s a filter that pulls primary colors from the background to make text more readable.
- **Vibrant Primary**: For headlines and body text.
- **Vibrant Secondary**: For captions and secondary info.

## Color Palette

### Semantic Colors
Always use Apple's semantic color system (`systemBlue`, `systemRed`) rather than hardcoded hex values to support:
- Light / Dark Mode.
- High Contrast Mode.
- Dynamic color adjustments in 2026 systems.

### 2. Gradients
Liquid Glass uses subtle, non-distracting gradients to imply surface curvature.

## Typography: San Francisco

Apple uses the **San Francisco (SF)** family across all platforms.

| Variant | Platform | Usage |
|---------|----------|-------|
| **SF Pro** | iOS, macOS | System standard for performance and legibility. |
| **SF Compact** | watchOS | Optimized for small screens (the Camera app uses SF Compact Rounded as of iOS 26). |
| **SF Mono** | Dev tools | Monospaced variant for code. |
| **New York** | All | Serif companion family for editorial contexts. |

Only the families on [developer.apple.com/fonts](https://developer.apple.com/fonts/) (SF Pro, SF Compact, SF Mono, SF Arabic/Hebrew and other language extensions, New York) are available to developers. "SF Camera" was an internal face used in Apple's Camera app, never a public download — do not specify it in design systems.

### Dynamic Type
You MUST support Dynamic Type.
- Use system text styles (e.g., `Title 1`, `Body`, `Caption 1`).
- Design for scale; UI should remain usable when font size is at 300%.

## Spacing and Grid

### The 8pt Rule
All spacing should be increments of 8 (8pt, 16pt, 24pt, 32pt).
- **Margins**: Typically 16pt or 24pt for standard layouts.
- **Tap Targets**: 44pt minimum vertical height.

### Margin Logic
- **iOS**: Match the Dynamic Island or Safe Area insets.
- **watchOS**: Maximize the bezel-less display by using rounded corner layouts.


## Sources

- Apple HIG — Materials: https://developer.apple.com/design/human-interface-guidelines/materials
- Apple HIG — Typography: https://developer.apple.com/design/human-interface-guidelines/typography
- Apple HIG — Color: https://developer.apple.com/design/human-interface-guidelines/color
- Apple HIG — Layout: https://developer.apple.com/design/human-interface-guidelines/layout
- Apple Fonts (official SF/New York downloads): https://developer.apple.com/fonts/
- "Meet Liquid Glass" (WWDC25 session 219): https://developer.apple.com/videos/play/wwdc2025/219/
- Apple Newsroom, June 9 2025 — new software design announcement: https://www.apple.com/newsroom/2025/06/apple-introduces-a-delightful-and-elegant-new-software-design/
