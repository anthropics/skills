---
name: designlang
description: Reverse-engineer any website into a complete design system. Use this skill when the user wants to extract design tokens, palette, typography, shadows, motion, or component anatomy from a public URL; generate an agent-native DESIGN.md; clone a site's design as a runnable Next.js starter; or compare local tokens against a deployed site (drift detection). Outputs DTCG W3C tokens plus emitters for Tailwind, CSS variables, Figma variables, shadcn/ui, React, Vue, Svelte, iOS SwiftUI, Android Compose, Flutter, and WordPress.
license: MIT — see LICENSE.txt
---

# designlang

`designlang` is an open-source CLI + MCP server that reverse-engineers any
public website into a complete design system. It runs Playwright against the
target URL, classifies the page (intent, material, library), extracts every
token (colors, typography, spacing, radii, shadows, motion, anatomy, voice),
and emits ~25 files including a single agent-native `DESIGN.md`.

## When to use

Use this skill when the user asks to:
- **Extract design tokens** from a website (`"give me Stripe's design tokens"`).
- **Generate a `DESIGN.md`** for an existing site so an AI agent can faithfully
  rebuild it (`"create an AGENTS.md-style design doc for vercel.com"`).
- **Clone a site's design** as a working Next.js starter
  (`"give me a Next.js app that looks like linear.app"`).
- **Detect drift** between local tokens and production
  (`"is my Tailwind config still in sync with my deploy?"`).
- **Iterate on tokens** conversationally
  (`"sharpen the radii"` / `"make it brutalist"` / `"swap primary to #ff4800"`).

## How to invoke

The CLI works without install via `npx`:

```bash
npx designlang <url>                           # extract everything
npx designlang clone <url>                     # generate a working Next.js repo
npx designlang ci <url> --tokens ./tokens.json # PR-comment drift bot
npx designlang chat <url>                      # REPL over the extraction
npx designlang studio                          # local web studio
npx designlang mcp                             # stdio MCP server
```

Outputs land in `./design-extract-output/` by default.

## Output formats

| File | Purpose |
|---|---|
| `*-DESIGN.md` | Single-file, 8-section, YAML front-matter agent-native artifact |
| `*-design-tokens.json` | DTCG W3C primitive + semantic + composite |
| `*-tailwind.config.js` | Tailwind v4-ready preset |
| `*-variables.css` | CSS custom properties |
| `*-figma-variables.json` | Figma Variable collection import |
| `*-shadcn-theme.css` / `*-theme.js` | shadcn / React themes |
| `ios/DesignTokens.swift` / `android/Theme.kt` / `flutter/design_tokens.dart` | Native platform tokens |
| `*-anatomy.tsx` | Typed React stubs from variant × size × state matrices |
| `*-motion-tokens.json` | Easing families, duration scale, springs |
| `*-voice.json` | Tone, pronoun posture, CTA verbs, heading style |

## MCP server

Add to `~/.cursor/mcp.json` or `claude_desktop_config.json`:

```json
{
  "mcpServers": {
    "designlang": {
      "command": "npx",
      "args": ["-y", "designlang", "mcp"]
    }
  }
}
```

The MCP server exposes the most recent extraction as live resources
(`designlang://latest/tokens`, `designlang://latest/regions`,
`designlang://latest/components`, `designlang://latest/css-health`,
`designlang://latest/design-md`).

## Spec

The `DESIGN.md` format is published as an open spec at
<https://designlang.app/spec> (CC BY 4.0).

## Source

- Repository: <https://github.com/Manavarya09/design-extract>
- npm: <https://www.npmjs.com/package/designlang>
- Web: <https://designlang.app>
