# Platform Specific Guidelines

While Apple aims for a unified aesthetic (Liquid Glass), each platform has unique ergonomics and hardware constraints.

## iOS (iPhone)
Designed for one-handed operation and touch-first input.
- **Bottom Navigation**: Primary controls should be reachable by the thumb at the bottom (Tab Bars, Toolbars).
- **Safe Area**: Avoid placing UI near the Dynamic Island or the home indicator.
- **Dynamic Island**: Use Live Activities and the Dynamic Island for high-value background status (e.g., timers, delivery status).

## macOS (Desktop)
Designed for precision cursor input and multitasking.
- **Sidebars**: Use for primary navigation.
- **Menu Bar**: Always provide standard File, Edit, and View menus.
- **Windowing**: Support multi-window environments and Split View.
- **Keyboard Shortcuts**: Every primary action must have a `Cmd` + [Key] equivalent.

## visionOS (Spatial Computing)
Designed for eyes (gaze) and hands (gestures).
- **Windows**: Have a physical presence in space. They cast shadows and reflect light.
- **Ornaments**: Floating controls that attach to the edge of a window.
- **Gaze-Contingent Feedback**: Elements should react (subtle hover state) when the user looks at them.
- **Z-Axis**: Use depth to prioritize content. Closer items are more important.

## watchOS (Wrist)
Designed for "Glances" — 2 to 5 second interactions.
- **Vertical Layout**: Scroll everything vertically using the Digital Crown.
- **Complications**: Design for the watch face to provide high-value data at a glance.
- **Full-Bleed Images**: Use the entire screen to reduce the perception of bezels.

## Platform Differences Table

| Feature | iOS | macOS | visionOS |
|---------|-----|-------|----------|
| **Navigation** | Tab Bar / Nav Bar | Sidebar / Menu Bar | Ornaments / Sidebars |
| **Input** | Touch / Voice | Mouse / Trackpad / Keys | Eyes (Gaze) / Hands |
| **Typical Dist.** | 6 - 12 inches | 18 - 30 inches | Infinite (Arm's length) |
| **Aesthetic** | High density | High precision | Spatially grounded |


## Sources

- Apple HIG — Designing for iOS: https://developer.apple.com/design/human-interface-guidelines/designing-for-ios
- Apple HIG — Designing for macOS: https://developer.apple.com/design/human-interface-guidelines/designing-for-macos
- Apple HIG — Designing for visionOS: https://developer.apple.com/design/human-interface-guidelines/designing-for-visionos
- Apple HIG — Designing for watchOS: https://developer.apple.com/design/human-interface-guidelines/designing-for-watchos
- Apple HIG — Ornaments (visionOS): https://developer.apple.com/design/human-interface-guidelines/ornaments
- Apple HIG — Live Activities / Dynamic Island: https://developer.apple.com/design/human-interface-guidelines/live-activities
