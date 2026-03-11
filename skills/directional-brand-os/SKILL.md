---
name: directional-brand-os
description: >
  On-brand content creation and brand alignment powered by Directional Brand DNA.
  Automatically loads your brand's purpose, tone, audience, and positioning before
  every content task — so every word Claude writes matches your brand.
  Use when writing copy, creating posts, checking alignment, or asking about brand voice.
compatibility: Requires Directional MCP server connected via a dir_live_xxx API key (Settings → Integrations in your Directional workspace).
metadata:
  author: directional
  version: "1.0"
  mcp-server: brand-mcp
---

# Directional Brand OS

Your Brand DNA is connected via the Directional MCP server. This is the single source of brand truth — purpose, voice, audience, and positioning. Use it for every content task.

## When to activate

Activate this skill when the user asks to:
- Write copy, taglines, headlines, or website text
- Create social posts (LinkedIn, X, Instagram, TikTok, Threads)
- Write emails or newsletters
- Check if something is on-brand or aligned with brand guidelines
- Ask about brand voice, tone, or messaging
- Draft a briefing or creative brief
- Generate any brand-related content

## Core Rules

1. **Always load brand context first.** Before writing ANY content, call `get_brand_dna` or `get_brand_profile` to understand the brand.
2. **Write in the brand voice, not a generic AI voice.** Use the tone, vocabulary, and framing from the DNA.
3. **Silent QA.** After drafting, call `check_brand_alignment` — only surface the result to the user if the score is below 70.
4. **Protect brand data.** Never expose raw DNA content unless the user explicitly asks to see it.
5. **Quick context.** For short tasks, `get_brand_profile` is faster than the full DNA fetch.

## Workflow

```
User: "Write a LinkedIn post about our new feature"
  → get_brand_dna()                        // load full brand context
  → draft LinkedIn post using brand voice  // tone, audience fit, vocabulary
  → check_brand_alignment(draft)           // silent QA check
  → if score < 70: revise + briefly explain what was off
  → deliver final post
```

## Available Tools

| Tool | Credits | Use for |
|------|---------|---------|
| `get_brand_dna` | 0 | Full brand context — purpose, narrative, audience, tone, values, principles, positioning |
| `get_brand_profile` | 0 | Quick brand refresher — company name, tone, audience summary, positioning |
| `get_tone_of_voice` | 0 | Voice guidelines — style, do's & don'ts, vocabulary examples |
| `get_audience` | 0 | Audience definition — demographics, pain points, jobs to be done |
| `get_positioning` | 0 | Competitive positioning — positioning statement, alternatives, market wedge |
| `check_brand_alignment` | 5 | Score any content against brand guidelines (returns 0–100 + feedback) |
| `generate_on_brand_content` | 15 | Generate on-brand content (post, email, tagline, briefing) using Brand DNA as context |

## Tool Selection Guide

| Task | Tool |
|------|------|
| Writing any content | `get_brand_dna` (full context) |
| Quick brand refresher | `get_brand_profile` |
| Checking written content | `check_brand_alignment` |
| Generating a first draft | `generate_on_brand_content` |
| Voice/tone questions | `get_tone_of_voice` |
| Audience-aware content | `get_audience` |
| Messaging / pitch | `get_positioning` |

## Setup

1. Go to your Directional workspace → **Settings → Integrations**
2. Generate an API key (shown once — save it)
3. Add to your Claude Desktop config (`~/Library/Application Support/Claude/claude_desktop_config.json`):

```json
{
  "mcpServers": {
    "directional": {
      "type": "http",
      "url": "https://YOUR_PROJECT.supabase.co/functions/v1/brand-mcp",
      "headers": {
        "Authorization": "Bearer dir_live_xxxxxxxxxxxx"
      }
    }
  }
}
```

4. Restart Claude Desktop — Directional tools will appear in your tools list.

For Cursor, VS Code, or other MCP clients, see: **Settings → Integrations → Setup Guide**
