---
name: figma
description: Figma design bridge for Claude Code. Browse files, extract components, download assets, extract design tokens, and generate code for Tailwind, React, Vue, Svelte, React Native, Flutter, and CSS. Use when user mentions Figma, design tokens, Figma-to-code, or wants to convert designs to components.
argument-hint: "[figma-url-or-file-key]"
license: Complete terms in LICENSE.txt
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

## Workflow 6: Discover Figma Community Resources

When the user needs design inspiration, templates, or UI kits from Figma Community:

1. **Search Figma Community** — Use web search to find relevant community files:
   - Search for: `site:figma.com/community "<topic> UI kit"` or `site:figma.com/community "<topic> design system"`
   - Look for files with high duplication counts and recent updates
2. **Evaluate results** — Check that the community file matches the user's framework, style, and project needs
3. **Extract the file key** — From the community file URL: `https://www.figma.com/community/file/<FILE_KEY>/...`
4. **Note**: Community files must be duplicated to the user's Figma account before they can be accessed via the API. Instruct the user to click "Open in Figma" / "Duplicate" on the community page first.
5. **Then proceed** with Workflow 1 to browse and extract from the duplicated file

**Example searches by project type:**
- Dashboard: `"dashboard UI kit" OR "admin panel" site:figma.com/community`
- E-commerce: `"e-commerce" OR "shopping" UI kit site:figma.com/community`
- Mobile app: `"mobile app" OR "iOS" OR "Android" UI kit site:figma.com/community`
- Landing page: `"landing page" OR "marketing" template site:figma.com/community`
- Design system: `"design system" OR "component library" site:figma.com/community`

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
