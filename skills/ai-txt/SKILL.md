---
name: ai-txt
description: Generate or audit ai.txt, robots.txt (AI-crawler rules), llms.txt, and TDM opt-out files for websites and web apps. Use this skill whenever the user mentions ai.txt, blocking AI training / AI crawlers, GPTBot / ClaudeBot / CCBot / Perplexity / Applebot-Extended / Google-Extended, llms.txt, TDMRep, or wants to stop AI from hallucinating about their product — even if they don't explicitly ask for an "ai.txt file". Also trigger when the user asks to review, audit, or check an existing robots.txt or ai.txt for AI-crawler coverage.
---

# ai-txt

Generate and audit the small family of text files that control or inform AI systems about a website: `robots.txt` (with AI user-agents), aitxt.ing-style `/ai.txt`, `llms.txt`, Spawning-style `/ai.txt`, and `/.well-known/tdmrep.json`.

The user almost always says "ai.txt" but means one of four different goals. Pick the right file(s) for the goal — don't just write whatever matches the filename.

## Disambiguate before writing

"ai.txt" is an overloaded name for three unrelated specs, and none of them is what most users actually need. Before generating anything, pin down which **goal** the user has. Ask briefly if it isn't clear from context.

| User's goal (plain words)                                       | File(s) you should produce                                                        |
| --------------------------------------------------------------- | --------------------------------------------------------------------------------- |
| "Block ChatGPT / Claude / AI from training on my site"          | `robots.txt` with per-vendor user-agents. **This is the only one crawlers read.** |
| "Stop AI assistants from making up features/pricing for my app" | aitxt.ing-style `/ai.txt` (Markdown + YAML frontmatter)                           |
| "Give AI assistants a tour of my docs so they cite correctly"   | `llms.txt`                                                                        |
| "EU legal opt-out from text-and-data-mining (CDSM Art. 4)"      | `/.well-known/tdmrep.json` (optionally paired with robots.txt)                    |
| "I was told to put an ai.txt in Spawning format"                | Spawning-style `/ai.txt` — but flag §"Spawning caveats" below first               |

A mobile/web app marketing site usually wants **robots.txt + aitxt.ing `/ai.txt`** together: robots.txt does the actual blocking, the aitxt.ing file prevents hallucination about the product. Recommend both unless the user pushes back.

### Why this matters

- The robots.txt approach is the only one with broad vendor compliance in 2026. OpenAI, Anthropic, Google, Perplexity, Common Crawl, Apple, Meta, ByteDance all document robots.txt — not ai.txt — as the canonical opt-out.
- The aitxt.ing spec (Markdown at `/ai.txt`) has no notion of "blocking". It's anti-hallucination context. Don't produce one when the user asked to block training.
- Spawning-format `/ai.txt` (robots-style with User-Agent/Allow/Disallow) has tiny compliance; Spawning itself has acknowledged this. Anything it would accomplish is already handled by robots.txt entries. Only produce one if the user explicitly insists.

## Generate mode

### 1. Understand the site

Before writing, gather the minimum you need. Ask if unknown:

- **Root URL** (for the `Sitemap:` line, aitxt.ing `scope`, tdm-policy URL).
- **What the site is** (marketing page, docs, SaaS, e-commerce, blog). Drives the aitxt.ing body content.
- **Is AI search traffic desirable?** Most publishers want to block *training* but allow *search/retrieval* bots (OAI-SearchBot, PerplexityBot, etc.) because those drive referral traffic. Default to this split unless the user says "block everything".
- **Region/legal posture.** If they care about EU CDSM Art. 4 defensibility, also generate `tdmrep.json`.

### 2. Produce the file(s)

Pull the template from `references/examples.md` and the current user-agent list from `references/user-agents.md`. Don't hand-type bot names from memory — the list changes and some old names are deprecated traps (`anthropic-ai`, `claude-web`).

Each generated file should:

- Open with a short `#` comment explaining what the file is and what it's for, so a future maintainer who opens the file knows instantly.
- Include a `Sitemap:` line in robots.txt when the URL is known.
- For aitxt.ing `/ai.txt`, write **factual, verifiable** content about the product (what it offers, what it does **not** offer, pricing source of truth). The whole point is anti-hallucination — speculative marketing copy defeats it. If you don't know the facts, ask.
- Save to the path the user can upload directly (e.g. `public/robots.txt`, `public/ai.txt`, `public/llms.txt`, `public/.well-known/tdmrep.json`) when a project directory is available. If not, emit the content and tell the user where to put each file.

### 3. Tell the user what you did and what's left

After generating, summarize in 1–3 bullets: which files, where they go, what you assumed. Flag any values the user should change before shipping (e.g. sitemap URL, policy URL).

## Audit mode

When the user asks to check/review an existing `robots.txt` or `ai.txt`, read the file and report against `references/user-agents.md`. Typical findings:

- **Missing AI user-agents** — especially recent ones: `GPTBot`, `OAI-SearchBot`, `ChatGPT-User`, `ClaudeBot`, `Claude-SearchBot`, `Claude-User`, `PerplexityBot`, `Perplexity-User`, `CCBot`, `Google-Extended`, `Applebot-Extended`, `Bytespider`, `Meta-ExternalAgent`, `Amazonbot`.
- **Deprecated tokens** still in the file: `anthropic-ai` and `claude-web` were retired in 2024; keeping them is harmless but misleading.
- **Applebot-Extended trap** — if the file has rules for `Googlebot` but *no* explicit `Applebot-Extended` rule, Applebot falls back to following Googlebot rules. Most users don't want this. Call it out.
- **Training vs. search mixed up** — if `GPTBot` is allowed but `OAI-SearchBot` is disallowed, that's the inverse of what most sites want. Explain and offer a fix.
- **Wrong file for the goal** — e.g. the site has a Spawning-format `/ai.txt` but no robots.txt AI rules. The ai.txt does almost nothing alone; the robots.txt is what actually gates training crawlers.
- **HTTP 5xx / missing file** — RFC 9309 treats 5xx as "do not crawl" but missing (404) as "fully allowed". If the user's concern is blocking, a missing file is not safe.

Report findings as a prioritized list: blockers first, then improvements, then nits. Offer to patch the file.

## Spawning caveats

If the user specifically asks for Spawning-format `/ai.txt`:

- It's real, documented, and used by a handful of tools (Hugging Face, Stability AI were launch partners in 2023). Generating it is fine.
- But tell the user plainly that `robots.txt` entries for `GPTBot`, `ClaudeBot`, `CCBot`, etc. already cover the same training opt-out with much broader compliance. Spawning's ai.txt is at best a belt-and-suspenders addition.
- Do not substitute Spawning format when the user wanted aitxt.ing. They look nothing alike — Spawning is robots.txt-style directives, aitxt.ing is Markdown.

## Quick reference pointers

- `references/user-agents.md` — current (Apr 2026) AI user-agent table, deprecated tokens, IP-range endpoints for spoof verification. Read this before generating or auditing any robots.txt.
- `references/examples.md` — copy-paste templates for all five file types with inline notes on what to customize.

## Output principles

- Plain text, LF line endings, UTF-8. No BOM.
- Comment lines start with `#` in robots.txt and Spawning ai.txt; Markdown comments (`<!-- -->`) are fine in aitxt.ing `/ai.txt` and llms.txt but usually unnecessary.
- Keep files short. robots.txt over a few KB is a code smell; aitxt.ing recommends under ~10 KB.
- Never invent bot names or IP ranges. If you're not sure, say so and check `references/user-agents.md`.
