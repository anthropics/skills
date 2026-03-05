# Font Usage Guide

Complete guide for using the frontend-arsenal font collection.

## Installation Methods

### Method 1: Google Fonts CDN (Easiest)

```html
<!-- In your HTML head -->
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>

<!-- Inter + JetBrains Mono -->
<link href="https://fonts.googleapis.com/css2?family=Inter:wght@100..900&family=JetBrains+Mono:wght@100..800&display=swap" rel="stylesheet">

<!-- Geist (Vercel's font) -->
<link href="https://fonts.googleapis.com/css2?family=Geist:wght@100..900&family=Geist+Mono:wght@100..900&display=swap" rel="stylesheet">
```

### Method 2: Fontsource NPM (Best for bundlers)

```bash
# Install fonts
npm install @fontsource/inter @fontsource/jetbrains-mono @fontsource/space-grotesk

# Or all at once
npm install @fontsource/inter @fontsource/plus-jakarta-sans @fontsource/geist-sans @fontsource/geist-mono @fontsource/merriweather @fontsource/jetbrains-mono @fontsource/space-grotesk
```

```typescript
// In your entry file (main.tsx, layout.tsx, etc.)
import '@fontsource/inter/400.css';
import '@fontsource/inter/500.css';
import '@fontsource/inter/600.css';
import '@fontsource/inter/700.css';

import '@fontsource/jetbrains-mono/400.css';
import '@fontsource/jetbrains-mono/500.css';

import '@fontsource/space-grotesk/500.css';
import '@fontsource/space-grotesk/700.css';
```

### Method 3: Nerd Fonts (For terminal/coding)

```bash
# macOS with Homebrew
brew tap homebrew/cask-fonts
brew install --cask font-jetbrains-mono-nerd-font
brew install --cask font-fira-code-nerd-font
brew install --cask font-hack-nerd-font

# Windows (Chocolatey)
choco install nerd-fonts-hack
choco install nerd-fonts-firacode

# Arch Linux
yay -S nerd-fonts-jetbrains-mono nerd-fonts-fira-code
```

## Font Pairings by Use Case

### 1. Enterprise Dashboard
```css
:root {
  --font-sans: 'Inter', system-ui, -apple-system, sans-serif;
  --font-mono: 'JetBrains Mono', 'SF Mono', monospace;
  --font-display: 'Space Grotesk', sans-serif;
}

body { font-family: var(--font-sans); }
h1, h2 { font-family: var(--font-display); }
code { font-family: var(--font-mono); }
```

### 2. Developer Tools / IDE
```css
:root {
  --font-ui: 'Plus Jakarta Sans', system-ui, sans-serif;
  --font-code: 'JetBrainsMono Nerd Font', 'JetBrains Mono', monospace;
  --font-terminal: 'FiraCode Nerd Font', 'Fira Code', monospace;
}

/* UI Elements */
.sidebar, .toolbar { font-family: var(--font-ui); }

/* Code Editor */
.editor { 
  font-family: var(--font-code);
  font-feature-settings: 'liga' 1, 'calt' 1; /* Enable ligatures */
}

/* Terminal */
.terminal { font-family: var(--font-terminal); }
```

### 3. Creative Portfolio
```css
:root {
  --font-body: 'Geist Sans', system-ui, sans-serif;
  --font-headings: 'Clash Display', sans-serif;
  --font-accent: 'Syne', sans-serif;
  --font-mono: 'Geist Mono', monospace;
}

.hero-title { 
  font-family: var(--font-headings);
  font-weight: 700;
  letter-spacing: -0.02em;
}

.nav-links { font-family: var(--font-accent); }
```

### 4. Editorial / Blog
```css
:root {
  --font-serif: 'Merriweather', Georgia, serif;
  --font-sans: 'Inter', system-ui, sans-serif;
  --font-mono: 'IBM Plex Mono', monospace;
  --font-display: 'DM Serif Display', Georgia, serif;
}

article p { font-family: var(--font-serif); }
article h1 { font-family: var(--font-display); }
figcaption { font-family: var(--font-sans); }
```

### 5. SaaS Marketing Site
```css
:root {
  --font-primary: 'Poppins', system-ui, sans-serif;
  --font-secondary: 'Manrope', sans-serif;
  --font-mono: 'Geist Mono', monospace;
}

/* Headlines use Poppins for personality */
h1, h2, .cta-button { font-family: var(--font-primary); }

/* Body uses Manrope for readability */
body { font-family: var(--font-secondary); }
```

## Nerd Fonts: Icons in Code

Nerd Fonts combine regular fonts with thousands of icons from:
- Devicons (development tools)
- Font Awesome (general icons)
- Material Design (Google icons)
- Weather Icons
- Octicons (GitHub)
- Powerline symbols

### Common Glyphs

```html
<!-- File type icons -->
<span>󰉋</span> <!-- folder -->
<span>󰈙</span> <!-- file text -->
<span>󰌠</span> <!-- git -->
<span>󰘧</span> <!-- code -->

<!-- Status icons -->
<span>󰄬</span> <!-- check -->
<span>󰅙</span> <!-- error -->
<span>󰌵</span> <!-- warning -->
<span>󰋽</span> <!-- info -->

<!-- Tool icons -->
<span>󰨞</span> <!-- docker -->
<span>󱃾</span> <!-- kubernetes -->
<span>󰛓</span> <!-- react -->
<span>󰛦</span> <!-- typescript -->
```

### Using with CSS

```css
.nerd-icon {
  font-family: 'JetBrainsMono Nerd Font', monospace;
  font-size: 1.2em;
}

/* File tree styling */
.file-tree .folder::before {
  content: '󰉋';
  font-family: 'JetBrainsMono Nerd Font';
  margin-right: 0.5em;
}

.file-tree .file-js::before {
  content: '󰌠';
  font-family: 'JetBrainsMono Nerd Font';
  color: #f7df1e; /* JS yellow */
}
```

## Performance Optimization

### 1. Preconnect to Font CDNs
```html
<head>
  <link rel="preconnect" href="https://fonts.googleapis.com">
  <link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
  <!-- Font links -->
</head>
```

### 2. Use Variable Fonts (when available)
```html
<!-- Inter as variable font (one file, all weights) -->
<link href="https://fonts.googleapis.com/css2?family=Inter:wght@100..900&display=swap" rel="stylesheet">
```

### 3. Font Display Strategy
```css
@font-face {
  font-family: 'CustomFont';
  src: url('font.woff2') format('woff2');
  font-display: swap; /* Show fallback until loaded */
}
```

### 4. Preload Critical Fonts
```html
<link rel="preload" href="/fonts/GeistSans.woff2" as="font" type="font/woff2" crossorigin>
```

### 5. Subset Fonts (Advanced)
```bash
# Using glyphhanger to subset fonts
npx glyphhanger --subset=*.woff2 --formats=woff2 --css
```

## Framework Integration

### React / Next.js

```tsx
// layout.tsx
import { Inter, JetBrains_Mono } from 'next/font/google';

const inter = Inter({ 
  subsets: ['latin'],
  variable: '--font-sans',
});

const jetbrainsMono = JetBrains_Mono({ 
  subsets: ['latin'],
  variable: '--font-mono',
});

export default function RootLayout({ children }) {
  return (
    <html className={`${inter.variable} ${jetbrainsMono.variable}`}>
      <body className="font-sans">{children}</body>
    </html>
  );
}
```

```css
/* globals.css */
@layer base {
  body {
    font-family: var(--font-sans), system-ui, sans-serif;
  }
  
  code, pre {
    font-family: var(--font-mono), monospace;
  }
}
```

### Tailwind CSS

```javascript
// tailwind.config.js
module.exports = {
  theme: {
    extend: {
      fontFamily: {
        sans: ['var(--font-sans)', 'system-ui', 'sans-serif'],
        mono: ['var(--font-mono)', 'monospace'],
        display: ['var(--font-display)', 'sans-serif'],
      },
    },
  },
};
```

```html
<!-- Usage -->
<p class="font-sans text-base">Body text</p>
<code class="font-mono text-sm">Code snippet</code>
<h1 class="font-display text-4xl">Headline</h1>
```

## Accessibility

### Minimum Requirements
- Body text: minimum 16px (1rem)
- Line height: 1.5 minimum for body
- Contrast: 4.5:1 for normal text, 3:1 for large text

### Dyslexia Considerations
```css
@media (prefers-reduced-data: no-preference) {
  /* Offer OpenDyslexic as an option */
  body.dyslexia-mode {
    font-family: 'OpenDyslexic', sans-serif;
    line-height: 1.8;
    word-spacing: 0.16em;
  }
}
```

### Motion Preferences
```css
@media (prefers-reduced-motion: reduce) {
  /* Disable font transitions */
  * {
    transition: none !important;
  }
}
```

## Troubleshooting

### FOUT/FOIT Prevention
```css
/* Flash of Unstyled Text strategy */
@font-face {
  font-family: 'Inter';
  src: url('inter.woff2') format('woff2');
  font-display: swap; /* Recommended */
  /* or font-display: optional; for faster but may not load */
}
```

### Font Weight Mismatch
```css
/* If 500 looks too bold, use numeric values */
.medium-text {
  font-weight: 450; /* Some variable fonts support this */
}
```

### Nerd Font Glyphs Not Showing
```css
/* Ensure fallback fonts have the glyphs */
.nerd-font {
  font-family: 'JetBrainsMono Nerd Font', 'JetBrains Mono', monospace;
  /* The second fallback won't have icons but maintains monospace */
}
```

## Complete Token Reference

All fonts are available as design tokens in `font-collection.json`:

```typescript
import { tokens } from '@frontend-arsenal/tokens';

// Font families
const sansFont = tokens.typography.families.sans.inter.$value;
const monoFont = tokens.typography.families.mono['jetbrains-mono'].$value;
const nerdFont = tokens.typography.families.nerd['nerd-mono'].$value;

// Font sizes
const baseSize = tokens.typography.sizes.base.$value; // "1rem"
const heroSize = tokens.typography.sizes['7xl'].$value; // "4.5rem"

// Font weights
const normal = tokens.typography.weights.normal.$value; // 400
const bold = tokens.typography.weights.bold.$value; // 700

// Line heights
const bodyLeading = tokens.typography.lineHeights.relaxed.$value; // 1.625
```
