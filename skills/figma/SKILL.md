---
name: figma
description: Figma design bridge for Claude Code. Browse files, extract components, download assets, extract design tokens, and generate code for Tailwind, React, Vue, Svelte, React Native, Flutter, and CSS. Use when user mentions Figma, design tokens, Figma-to-code, or wants to convert designs to components.
argument-hint: "[figma-url-or-file-key]"
allowed-tools:
  - Bash
  - Read
  - Write
  - Edit
  - WebSearch
  - WebFetch
  - mcp__figma__get_figma_data
  - mcp__figma__download_figma_images
---
# figma

Universal Figma-to-code skill for Claude Code. Uses the `figma-developer-mcp` server to browse designs, download assets, extract design tokens, and generate production-ready code for 7 frameworks.

## Prerequisites

### 1. Figma API Key

Get a personal access token from [Figma Developer Settings](https://www.figma.com/developers/api#access-tokens).

### 2. MCP Server Configuration

Add this to your project's `.mcp.json` (or copy from `.mcp.json.example`):

```json
{
  "mcpServers": {
    "figma": {
      "command": "npx",
      "args": ["-y", "figma-developer-mcp", "--stdio"],
      "env": {
        "FIGMA_API_KEY": "<your-figma-api-key>"
      }
    }
  }
}
```

After adding the key, run **"Developer: Reload Window"** in VS Code (or restart Claude Code CLI).

### 3. Python 3.8+

Required for the token extraction and code generation scripts. No pip dependencies needed — stdlib only.

```bash
python3 --version
```

---

## Workflow 1: Browse & Inspect Figma Files

### Get the File Key

Extract the file key from any Figma URL:

```
https://www.figma.com/design/<FILE_KEY>/...
https://www.figma.com/file/<FILE_KEY>/...
```

### Browse the Full File

```
mcp__figma__get_figma_data(fileKey: "<FILE_KEY>")
```

Returns pages, frames, components, layout info, text content, fills, strokes, effects, and component instances.

### Inspect a Specific Node

```
mcp__figma__get_figma_data(fileKey: "<FILE_KEY>", nodeId: "1234:5678")
```

Node IDs come from Figma URLs (`?node-id=1234:5678`) or from browsing the file tree. Formats: `1234:5678`, `1234-5678`, or `I5666:180910;1:10515` for nested instances.

Use the optional `depth` parameter to limit tree traversal depth.

---

## Workflow 2: Download Assets

Export PNG or SVG assets from specific nodes:

```
mcp__figma__download_figma_images(
  fileKey: "<FILE_KEY>",
  localPath: "/absolute/path/to/assets/",
  nodes: [
    { "nodeId": "1234:5678", "fileName": "hero-image.png" },
    { "nodeId": "2345:6789", "fileName": "logo.svg" }
  ]
)
```

**Parameters:**

| Parameter | Description |
|-----------|-------------|
| `localPath` | Absolute path to save directory (created if missing) |
| `nodes[].nodeId` | Figma node ID to export |
| `nodes[].fileName` | Local filename with `.png` or `.svg` extension |
| `nodes[].imageRef` | Required for image fills (raster photos); leave blank for vectors |
| `pngScale` | Export scale for PNGs (default: 2 for retina) |

**Tips:**
- Use `.svg` for icons and illustrations — crisp at any size
- Use `.png` for photos and complex raster images
- Set `pngScale: 3` for mobile @3x assets
- Set `pngScale: 1` for web thumbnails

---

## Workflow 3: Extract Design Tokens

Automatically extract colors, typography, spacing, shadows, gradients, and border-radius from Figma data into reusable token files.

### Step 1: Save Figma Data to JSON

After fetching data with `get_figma_data`, save the response to a file:

```bash
# Claude will save the Figma API response as JSON
# Example: figma-data.json
```

### Step 2: Run the Token Extractor

```bash
# CSS custom properties (default)
python3 ${CLAUDE_SKILL_DIR}/scripts/extract_tokens.py --input figma-data.json --format css --output tokens.css

# Tailwind config
python3 ${CLAUDE_SKILL_DIR}/scripts/extract_tokens.py --input figma-data.json --format tailwind --output tailwind-tokens.js

# JSON tokens
python3 ${CLAUDE_SKILL_DIR}/scripts/extract_tokens.py --input figma-data.json --format json --output tokens.json

# SCSS variables
python3 ${CLAUDE_SKILL_DIR}/scripts/extract_tokens.py --input figma-data.json --format scss --output _tokens.scss
```

**Supported formats:**

| Format | Output | Use Case |
|--------|--------|----------|
| `css` | `:root { --color-*: ...; }` | Any web project |
| `tailwind` | `theme.extend` config block | Tailwind CSS projects |
| `json` | Raw token JSON | Design systems, Style Dictionary |
| `scss` | `$color-*: ...;` | SCSS/Sass projects |

**What gets extracted:**
- **Colors** — all solid fills with layer name as token name
- **Typography** — font family, size, weight, line-height, letter-spacing
- **Spacing** — padding and gap from auto-layout frames
- **Border Radius** — uniform and per-corner values
- **Shadows** — drop shadows and inner shadows
- **Gradients** — linear, radial, and angular gradients with stops

---

## Workflow 4: Convert Figma to Code

Generate framework-specific code from Figma nodes.

### Step 1: Save Node Data

Fetch a specific frame/component and save the JSON response.

### Step 2: Run the Code Generator

```bash
# Tailwind/HTML (default)
python3 ${CLAUDE_SKILL_DIR}/scripts/figma_to_code.py --input node.json --framework tailwind

# React (JSX + Tailwind)
python3 ${CLAUDE_SKILL_DIR}/scripts/figma_to_code.py --input node.json --framework react --name HeroSection

# Vue SFC
python3 ${CLAUDE_SKILL_DIR}/scripts/figma_to_code.py --input node.json --framework vue --name HeroSection

# Svelte
python3 ${CLAUDE_SKILL_DIR}/scripts/figma_to_code.py --input node.json --framework svelte --name HeroSection

# React Native
python3 ${CLAUDE_SKILL_DIR}/scripts/figma_to_code.py --input node.json --framework react-native --name HeroSection

# Flutter (Dart)
python3 ${CLAUDE_SKILL_DIR}/scripts/figma_to_code.py --input node.json --framework flutter --name HeroSection

# Plain CSS + HTML
python3 ${CLAUDE_SKILL_DIR}/scripts/figma_to_code.py --input node.json --framework css
```

**Supported frameworks:**

| Framework | Output | Layout Model |
|-----------|--------|-------------|
| `tailwind` | HTML + Tailwind classes | Flexbox via utilities |
| `react` | JSX component + Tailwind | Flexbox via utilities |
| `vue` | Vue SFC `<template>` + Tailwind | Flexbox via utilities |
| `svelte` | Svelte component + Tailwind | Flexbox via utilities |
| `react-native` | RN component + StyleSheet | Flexbox via StyleSheet |
| `flutter` | Dart StatelessWidget | Row/Column/Container |
| `css` | HTML + CSS classes | Flexbox via CSS |

---

## Workflow 5: Full Component Pipeline

Combine all workflows for a complete Figma-to-code pipeline:

1. **Browse** the file to find the target frame or component
2. **Inspect** the specific node to understand structure
3. **Extract tokens** for the design system (colors, fonts, spacing)
4. **Generate code** for your framework
5. **Download assets** (images, icons) referenced in the design
6. **Integrate** — paste tokens into your config, code into your components, assets into your project

---

## Workflow 6: Smart Figma Community Discovery & Retrieval

This workflow turns Claude into an expert design sourcer. Instead of just searching, Claude must deeply understand the user's project, run multiple targeted searches, evaluate results against specific criteria, and then retrieve the actual design data.

### Step 1: Build a Project Profile

Before searching, gather or infer these details from the conversation context and the user's codebase:

| Signal | How to Detect |
|--------|--------------|
| **Project type** | Read package.json, existing routes, folder structure, or ask: dashboard, e-commerce, SaaS, mobile app, landing page, blog, portfolio, social platform, admin panel, etc. |
| **Framework** | Check package.json for react/vue/svelte/next/nuxt/flutter, or existing component files |
| **Style direction** | Check existing CSS/Tailwind config for colors, fonts, border-radius patterns: minimal, bold, corporate, playful, glassmorphism, brutalist, dark mode, etc. |
| **Components needed** | Infer from the task: navbar, hero, pricing table, dashboard charts, cards, forms, modals, sidebars, footers, onboarding flows, etc. |
| **Color palette** | Extract from existing tailwind.config, CSS variables, or brand assets in the project |
| **Typography** | Check existing font imports, Google Fonts links, or Tailwind font config |
| **Responsive needs** | Mobile-first? Desktop dashboard? Both? Check existing breakpoints |
| **Industry/domain** | Finance, health, food, travel, education, fitness, real estate, etc. — affects visual language |

Summarize the profile internally before searching. Example:
> "Building a SaaS dashboard in React + Tailwind. Dark theme, Inter font, blue/purple palette. Needs: sidebar nav, data tables, chart cards, user settings page. Finance domain."

### Step 2: Multi-Strategy Search

Run **at least 3 different searches** to cast a wide net. Tailor queries to the profile:

**Search A — By project type + quality signals:**
```
site:figma.com/community/file "<project-type> UI kit" OR "<project-type> design system"
```

**Search B — By specific components needed:**
```
site:figma.com/community/file "<component-1>" "<component-2>" UI kit
```

**Search C — By style/aesthetic + industry:**
```
site:figma.com/community/file "<style>" "<industry>" dashboard OR app template
```

**Search D (optional) — By design system / framework match:**
```
site:figma.com/community/file "<framework>" components OR "design system" 2024 OR 2025 OR 2026
```

**Category-specific search patterns:**

| Project Type | Search Queries |
|-------------|---------------|
| SaaS Dashboard | `"admin dashboard" UI kit`, `"analytics dashboard" components`, `"SaaS" "design system"` |
| E-commerce | `"e-commerce" UI kit`, `"product page" "shopping cart" template`, `"online store" design system` |
| Mobile App | `"mobile app" UI kit`, `"iOS" OR "Android" app template`, `"mobile" "design system"` |
| Landing Page | `"landing page" template`, `"marketing" "hero section"`, `"startup" landing page` |
| Blog/Content | `"blog" template`, `"content" "editorial" design`, `"magazine" layout` |
| Social Platform | `"social media" app UI`, `"chat" "messaging" UI kit`, `"feed" "stories" template` |
| Finance/Fintech | `"fintech" UI kit`, `"banking" "finance" dashboard`, `"crypto" "trading" UI` |
| Health/Wellness | `"health" "medical" UI kit`, `"fitness" app template`, `"wellness" dashboard` |
| Real Estate | `"real estate" "property" UI kit`, `"listing" template` |
| Education | `"e-learning" "education" UI kit`, `"LMS" "course" template` |
| Restaurant/Food | `"food delivery" UI kit`, `"restaurant" app template` |

### Step 3: Deep Evaluation

For each promising result, use `WebFetch` to load the Figma Community page and extract:

1. **File description** — Does it mention the components/features the user needs?
2. **Likes and duplicates count** — Higher = more trusted (prefer 1K+ duplicates for UI kits)
3. **Last updated date** — Prefer files updated within the last 12 months
4. **Preview screenshots** — Do they show the components the user needs?
5. **Creator credibility** — Established design teams, agencies, or prolific creators
6. **Completeness** — Full design system vs. single-page template
7. **Responsiveness** — Does it include mobile + desktop variants?
8. **Component coverage** — Score against the user's specific needs

**Scoring criteria (rank each 1-5):**

| Criteria | Weight | What to Check |
|----------|--------|---------------|
| Component match | High | Has the specific components the user needs |
| Style match | High | Visual direction matches the project profile |
| Completeness | Medium | Full system vs. partial template |
| Recency | Medium | Updated recently, uses modern patterns |
| Popularity | Low | Duplicate/like count (social proof) |
| Responsiveness | Medium | Includes mobile + desktop variants |

### Step 4: Present Top Recommendations

Present the **top 3** options to the user with clear reasoning:

For each recommendation, show:
- **Name and link** to the Community page
- **Why it's a good match** — specific components it has that the user needs
- **What's included** — pages, components, design tokens
- **Style assessment** — how well the visual direction matches
- **Any gaps** — what's missing that would need to be built manually
- **Duplicate count** — social proof

Example format:
> **1. [Dashboard UI Kit Pro](community-url)** — 12K duplicates
> Best match for your dark-theme SaaS dashboard. Includes sidebar navigation, data tables, chart cards, and settings page — all in dark mode with a blue accent palette. Missing: finance-specific chart types. You'd need to adapt the generic charts.

### Step 5: Duplicate & Retrieve

Once the user picks a file:

1. **Provide the direct Community link** and tell them:
   > "Open this link, click **'Open in Figma'** (or **'Get a copy'**), and it will be duplicated to your drafts. Once it's in your account, give me the URL of the duplicated file."

2. **Extract the file key** from the duplicated file URL:
   ```
   https://www.figma.com/design/<FILE_KEY>/...
   ```

3. **Browse the full file** to map its structure:
   ```
   mcp__figma__get_figma_data(fileKey: "<FILE_KEY>", depth: 2)
   ```

4. **Identify the most relevant frames** — Match pages/frames to the user's component needs. List them:
   > "Found these relevant frames:
   > - `Sidebar Navigation` (node 123:456)
   > - `Data Table` (node 234:567)
   > - `Chart Card` (node 345:678)"

5. **Extract design tokens** from the full file:
   ```bash
   python3 ${CLAUDE_SKILL_DIR}/scripts/extract_tokens.py --input figma-data.json --format <user-format> --output tokens.<ext>
   ```

6. **Generate code** for each relevant component the user needs:
   ```bash
   python3 ${CLAUDE_SKILL_DIR}/scripts/figma_to_code.py --input <node>.json --framework <user-framework> --name <ComponentName>
   ```

7. **Download assets** (icons, images, illustrations) from the design:
   ```
   mcp__figma__download_figma_images(fileKey, nodes, localPath)
   ```

8. **Integrate into the user's project** — Place tokens in their config, components in their component directory, assets in their assets folder. Adapt the generated code to use the user's existing patterns and naming conventions.

### Step 6: Adapt to Project Conventions

After retrieving design data, do NOT just dump raw generated code. Adapt it:

- **Match naming conventions** — If the user's project uses `kebab-case` filenames and `PascalCase` components, follow that
- **Use existing tokens** — If the project already has a color system, map the Figma colors to existing tokens instead of adding new ones
- **Follow project structure** — Put components where the project's other components live
- **Merge design tokens** — Don't overwrite existing tokens; merge new ones in, flagging conflicts
- **Preserve existing patterns** — If the project uses a specific state management, router, or styling approach, integrate with that

---

## Figma-to-Code Conversion Reference

### Layout (Auto-Layout)

| Figma Property | Tailwind | React Native | Flutter | CSS |
|---------------|----------|-------------|---------|-----|
| Auto-layout: Horizontal | `flex flex-row` | `flexDirection: 'row'` | `Row()` | `display: flex; flex-direction: row;` |
| Auto-layout: Vertical | `flex flex-col` | `flexDirection: 'column'` | `Column()` | `display: flex; flex-direction: column;` |
| Gap: 16 | `gap-4` | `gap: 16` | `SizedBox(height: 16)` | `gap: 16px;` |
| Padding: 24 | `p-6` | `padding: 24` | `EdgeInsets.all(24)` | `padding: 24px;` |
| Align: Center/Center | `justify-center items-center` | `justifyContent: 'center', alignItems: 'center'` | `MainAxisAlignment.center, CrossAxisAlignment.center` | `justify-content: center; align-items: center;` |
| Fill container | `w-full` | `flex: 1` | `Expanded()` | `width: 100%;` |
| Hug contents | `w-fit` | `alignSelf: 'flex-start'` | `IntrinsicWidth()` | `width: fit-content;` |

### Typography

| Figma Property | Tailwind | React Native | Flutter | CSS |
|---------------|----------|-------------|---------|-----|
| Font: Inter 600 16px | `font-semibold text-base` | `fontWeight: '600', fontSize: 16` | `TextStyle(fontWeight: FontWeight.w600, fontSize: 16)` | `font-weight: 600; font-size: 16px;` |
| Line height: 1.5 | `leading-normal` | `lineHeight: 24` | `height: 1.5` | `line-height: 1.5;` |
| Letter spacing: 0.05em | `tracking-wider` | `letterSpacing: 0.8` | `letterSpacing: 0.8` | `letter-spacing: 0.05em;` |
| Align: Center | `text-center` | `textAlign: 'center'` | `textAlign: TextAlign.center` | `text-align: center;` |

### Colors & Fills

| Figma Property | Tailwind | React Native | Flutter | CSS |
|---------------|----------|-------------|---------|-----|
| Solid fill #3B82F6 | `bg-[#3B82F6]` | `backgroundColor: '#3B82F6'` | `Color(0xFF3B82F6)` | `background-color: #3B82F6;` |
| Text color #1F2937 | `text-[#1F2937]` | `color: '#1F2937'` | `Color(0xFF1F2937)` | `color: #1F2937;` |
| Opacity: 50% | `opacity-50` | `opacity: 0.5` | `Opacity(opacity: 0.5)` | `opacity: 0.5;` |

### Effects

| Figma Property | Tailwind | React Native | Flutter | CSS |
|---------------|----------|-------------|---------|-----|
| Drop shadow (4px blur) | `shadow` | `shadowRadius: 4, elevation: 2` | `BoxShadow(blurRadius: 4)` | `box-shadow: 0 2px 4px rgba(0,0,0,0.1);` |
| Drop shadow (10px blur) | `shadow-lg` | `shadowRadius: 10, elevation: 5` | `BoxShadow(blurRadius: 10)` | `box-shadow: 0 4px 10px rgba(0,0,0,0.15);` |

### Borders & Corners

| Figma Property | Tailwind | React Native | Flutter | CSS |
|---------------|----------|-------------|---------|-----|
| Border-radius: 8 | `rounded-lg` | `borderRadius: 8` | `BorderRadius.circular(8)` | `border-radius: 8px;` |
| Border-radius: 9999 | `rounded-full` | `borderRadius: 9999` | `BorderRadius.circular(9999)` | `border-radius: 9999px;` |
| Border: 1px solid | `border border-[color]` | `borderWidth: 1, borderColor: color` | `Border.all(width: 1)` | `border: 1px solid color;` |

---

## Quick Reference

| Task | Command |
|------|---------|
| Browse full file | `get_figma_data(fileKey)` |
| Inspect a node | `get_figma_data(fileKey, nodeId)` |
| Download PNG @2x | `download_figma_images(fileKey, nodes: [{nodeId, fileName: "x.png"}], localPath)` |
| Download SVG | `download_figma_images(fileKey, nodes: [{nodeId, fileName: "x.svg"}], localPath)` |
| Download @3x | `download_figma_images(fileKey, nodes, localPath, pngScale: 3)` |
| Extract CSS tokens | `python3 ${CLAUDE_SKILL_DIR}/scripts/extract_tokens.py -i data.json -f css -o tokens.css` |
| Extract TW tokens | `python3 ${CLAUDE_SKILL_DIR}/scripts/extract_tokens.py -i data.json -f tailwind -o tw.js` |
| Generate React code | `python3 ${CLAUDE_SKILL_DIR}/scripts/figma_to_code.py -i node.json -f react -n MyComponent` |
| Generate Flutter | `python3 ${CLAUDE_SKILL_DIR}/scripts/figma_to_code.py -i node.json -f flutter -n MyWidget` |

---

## Tips

1. **Always browse first** — Fetch the full file before drilling into nodes to understand the structure
2. **Use node IDs from URLs** — When a user shares a link with `?node-id=X:Y`, pass that directly as `nodeId`
3. **SVG for icons, PNG for photos** — Use `.svg` for vector graphics, `.png` for raster images
4. **Retina by default** — `pngScale: 2` is the default; use `3` for mobile @3x
5. **Extract tokens early** — Run token extraction on the full file to build your design system before generating component code
6. **Component names matter** — Use `--name` flag with the code generator for clean component names
7. **Pipe for speed** — Both scripts accept stdin: `cat data.json | python3 ${CLAUDE_SKILL_DIR}/scripts/extract_tokens.py -f css`
8. **Iterate** — Generated code is a starting point; refine layout, add interactivity, and connect to your state management
9. **Community discovery is context-first** — Always build a project profile before searching Figma Community. A generic search yields generic results; a targeted search finds exactly what the user needs.
10. **Adapt, don't dump** — When pulling from Community files, adapt code to the user's existing project conventions, token system, and file structure. Never blindly overwrite existing design tokens or patterns.
