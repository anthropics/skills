---
name: watermark-guide
description: Watermark configuration guide for baoyu-xhs-images
---

# Watermark Guide

## Position Diagram

```
┌─────────────────────────────┐
│                  [top-right]│
│                             │
│                             │
│         IMAGE CONTENT       │
│                             │
│                             │
│[bottom-left][bottom-center][bottom-right]│
└─────────────────────────────┘
```

## Position Recommendations

| Position | Best For | Avoid When |
|----------|----------|------------|
| `bottom-right` | Default choice, most common | Key info in bottom-right |
| `bottom-left` | Right-heavy layouts | Key info in bottom-left |
| `bottom-center` | Centered designs | Text-heavy bottom area |
| `top-right` | Bottom-heavy content | Title/header in top-right |

## Content Format

| Format | Example | Style |
|--------|---------|-------|
| Handle | `@username` | Most common for XHS |
| Text | `MyBrand` | Simple branding |
| Chinese | `小红书:用户名` | Platform specific |
| URL | `myblog.com` | Cross-platform |

## Best Practices

1. **Consistency**: Use same watermark across all images in series
2. **Legibility**: Ensure watermark readable on both light/dark areas
3. **Size**: Keep subtle - should not distract from content

## Prompt Integration

When watermark is enabled, add to image generation prompt:

```
Include a subtle watermark "[content]" positioned at [position].
The watermark should be legible but not distracting from the main content.
```

## Common Issues

| Issue | Solution |
|-------|----------|
| Watermark invisible | Adjust position or check contrast |
| Watermark too prominent | Change position or reduce size |
| Watermark overlaps content | Change position |
| Inconsistent across images | Use session ID for consistency |
