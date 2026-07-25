# Color Contrast Guide

## Contrast Checker Usage

The `contrast_checker.py` script validates color pairs against WCAG 2.2 contrast requirements.

```bash
# Check a single color pair
python scripts/contrast_checker.py --fg "#777777" --bg "#ffffff"

# Output:
# Foreground: #777777 | Background: #ffffff
# Contrast Ratio: 4.48:1
# AA Normal Text (4.5:1): FAIL
# AA Large Text (3.0:1):  PASS
# AAA Normal Text (7.0:1): FAIL
# Suggested alternative: #767676 (4.54:1 - passes AA)

# Scan a CSS file for all color pairs
python scripts/contrast_checker.py --file src/styles/globals.css

# Scan Tailwind classes in components
python scripts/contrast_checker.py --tailwind src/components/
```

## Common Contrast Fixes

| Original Color | Contrast on White | Fix | New Contrast |
|----------------|------------------|-----|--------------|
| `#aaaaaa` | 2.32:1 | `#767676` | 4.54:1 (AA) |
| `#999999` | 2.85:1 | `#767676` | 4.54:1 (AA) |
| `#888888` | 3.54:1 | `#767676` | 4.54:1 (AA) |
| `#777777` | 4.48:1 | `#757575` | 4.60:1 (AA) |
| `#66bb6a` | 3.06:1 | `#2e7d32` | 5.87:1 (AA) |
| `#42a5f5` | 2.81:1 | `#1565c0` | 6.08:1 (AA) |
| `#ef5350` | 3.13:1 | `#c62828` | 5.57:1 (AA) |

## Tailwind CSS Accessible Palette Mapping

| Inaccessible Class | Contrast on White | Accessible Alternative | Contrast |
|---------------------|------------------|----------------------|----------|
| `text-gray-400` | 2.68:1 | `text-gray-600` | 5.74:1 |
| `text-blue-400` | 2.81:1 | `text-blue-700` | 5.96:1 |
| `text-green-400` | 2.12:1 | `text-green-700` | 5.18:1 |
| `text-red-400` | 3.04:1 | `text-red-700` | 6.05:1 |
| `text-yellow-500` | 1.47:1 | `text-yellow-800` | 7.34:1 |

## Screen Reader Utility Class

Every project should include this utility class for visually hiding content while keeping it accessible to screen readers:

```css
/* Visually hidden but accessible to screen readers */
.sr-only {
  position: absolute;
  width: 1px;
  height: 1px;
  padding: 0;
  margin: -1px;
  overflow: hidden;
  clip: rect(0, 0, 0, 0);
  white-space: nowrap;
  border-width: 0;
}

/* Allow the element to be focusable when navigated to via keyboard */
.sr-only-focusable:focus,
.sr-only-focusable:active {
  position: static;
  width: auto;
  height: auto;
  padding: inherit;
  margin: inherit;
  overflow: visible;
  clip: auto;
  white-space: inherit;
}
```

Tailwind CSS includes this as `sr-only` by default. For other frameworks:
- **Angular**: Add to `styles.scss`
- **Vue**: Add to `assets/global.css`
- **Svelte**: Add to `app.css`
