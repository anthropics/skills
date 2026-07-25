# Accessibility Compliance Guide

Accessibility isn't a feature; it's a foundational standard. Apple's design philosophy requires apps to be fully usable by everyone, regardless of their physical or cognitive abilities.

## The 4 Pillars of Accessibility

### 1. Perceivable
Information and UI components must be presentable to users in ways they can perceive.
- **VoiceOver**: Provide meaningful accessibility labels and hints. Avoid "Button 1". Use "Submit Order" with hint "Double tap to place your order."
- **Visuals**: Don't rely on color alone to convey meaning (e.g., use icons + color for errors).

### 2. Operable
User interface components and navigation must be operable.
- **Tap Targets**: 44x44 points minimum.
- **Motor Control**: Support Switch Control and AssistiveTouch.

### 3. Understandable
Information and the operation of the user interface must be understandable.
- **Predictability**: Use standard Apple UI patterns (Tab Bars, Sidebars) so users already know how they work.

### 4. Robust
Content must be robust enough to be interpreted by a wide variety of user agents, including assistive technologies.

## Technical Requirements (2026)

### Dynamic Type
Apps must respond to system-wide font size changes.
- **Scaling Layouts**: Use Auto Layout or SwiftUI `VStack`/`HStack` that wrap content when fonts get large.
- **No Clipped Text**: Text should never be truncated unnecessarily.

### Contrast Ratios
- **Normal Text**: 4.5:1 minimum against its background.
- **Large Text**: 3:1 minimum.
- **Liquid Glass Exception**: Be extremely careful with translucency (vibrancy). If a background is too busy, reduce transparency for accessibility.

### Haptics & Audio
- Provide haptic feedback for primary actions (success, failure, selection change).
- Ensure all audio content has captions or visual equivalents.

## Checklist for Designers

- [ ] Does the app work in Grayscale mode?
- [ ] Are all buttons at least 44pt tall?
- [ ] Is every icon labeled for VoiceOver?
- [ ] Does the layout remain usable at the largest Dynamic Type size?
- [ ] Have you tested with "Reduce Transparency" enabled in system settings?


## Sources

- Apple HIG — Accessibility: https://developer.apple.com/design/human-interface-guidelines/accessibility
- Apple HIG — Buttons (44x44 pt minimum hit region): https://developer.apple.com/design/human-interface-guidelines/buttons
- Apple HIG — Typography (Dynamic Type text styles): https://developer.apple.com/design/human-interface-guidelines/typography
- Apple Accessibility for developers: https://developer.apple.com/accessibility/
- WCAG 2.x contrast minimums (4.5:1 / 3:1), which the HIG color guidance mirrors: https://www.w3.org/WAI/WCAG22/Understanding/contrast-minimum.html
