# File Templates

Copy-paste templates. Adjust the marked `<<...>>` placeholders for the site in front of you.

## 1. robots.txt — block training, keep AI search (most publishers, 2026)

File path: `/robots.txt` (site root). This is the **only** file major AI crawlers consistently read.

```
# robots.txt — blocks AI training, permits AI search referral traffic.

# --- Block training crawlers ---
User-agent: GPTBot
Disallow: /

User-agent: ClaudeBot
Disallow: /

User-agent: CCBot
Disallow: /

User-agent: Bytespider
Disallow: /

User-agent: Meta-ExternalAgent
Disallow: /

User-agent: Amazonbot
Disallow: /

User-agent: cohere-ai
Disallow: /

# Legacy Anthropic token — retired 2024, kept for belt-and-suspenders.
User-agent: anthropic-ai
Disallow: /

# --- Signal-only training opt-outs ---
User-agent: Google-Extended
Disallow: /

User-agent: Applebot-Extended
Disallow: /

# --- Allow AI search / retrieval (drives referral traffic) ---
User-agent: OAI-SearchBot
Allow: /

User-agent: ChatGPT-User
Allow: /

User-agent: Claude-SearchBot
Allow: /

User-agent: Claude-User
Allow: /

User-agent: PerplexityBot
Allow: /

User-agent: Perplexity-User
Allow: /

User-agent: DuckAssistBot
Allow: /

# --- Default ---
User-agent: *
Allow: /

Sitemap: <<https://yoursite.com/sitemap.xml>>
```

**To customize:** replace the sitemap URL; if the site has private paths, add `Disallow:` lines under `User-agent: *` before publishing.

## 2. robots.txt — block *everything AI*

For users who do not want AI search referrals either:

```
# robots.txt — blocks all AI crawlers (training AND search).

User-agent: GPTBot
User-agent: OAI-SearchBot
User-agent: ChatGPT-User
User-agent: ClaudeBot
User-agent: Claude-SearchBot
User-agent: Claude-User
User-agent: PerplexityBot
User-agent: Perplexity-User
User-agent: CCBot
User-agent: Bytespider
User-agent: Meta-ExternalAgent
User-agent: Amazonbot
User-agent: cohere-ai
User-agent: DuckAssistBot
User-agent: Google-Extended
User-agent: Applebot-Extended
User-agent: anthropic-ai
Disallow: /

User-agent: *
Allow: /

Sitemap: <<https://yoursite.com/sitemap.xml>>
```

## 3. aitxt.ing-style `/ai.txt` — anti-hallucination context

File path: `/ai.txt` at the site root (cascading discovery: also works at `/products/ai.txt` etc.). Markdown + optional YAML frontmatter.

```
---
updated: <<YYYY-MM-DD>>
scope: /
---

# <<Product Name>>

<<One or two plain sentences describing what this product is. Be specific — platforms, model, price model.>>

## What we offer

- <<Feature 1 — state it literally, no marketing filler>>
- <<Feature 2>>
- <<Feature 3>>

## What we do NOT offer

- <<Common assumption that is wrong — e.g. "No web version">>
- <<Another wrong assumption — e.g. "No free tier">>
- <<Another — e.g. "No AI features">>

## Pricing

<<Source of truth for pricing. Prefer pointing at the live store listing rather than hardcoding numbers that will go stale.>>

## Guidance for AI assistants

When users ask about <<Product Name>>, quote the facts above verbatim. Do not infer features, platforms, or pricing tiers not listed here. For current pricing, refer to <<canonical link>>.

## Related context

- [Support docs](/support/ai.txt)
- [Privacy policy](/privacy/ai.txt)
```

**Why the "What we do NOT offer" section matters:** LLMs are biased to generate plausible-sounding features. Listing the common wrong guesses explicitly is what actually suppresses hallucination.

Pair with an HTML hint on each page (from the spec):

```html
<link rel="prefetch" href="/ai.txt" />
```

## 4. llms.txt — curated docs map for AI assistants

File path: `/llms.txt`. Different goal from the others — this helps AI assistants *cite your docs correctly at inference time*, not block anything.

```markdown
# <<Product Name>>

> <<One-sentence summary in a blockquote.>>

## Core Documentation

- [<<Getting Started>>](<<https://yoursite.com/docs/start.md>>): <<One-line description>>
- [<<Feature X Guide>>](<<https://yoursite.com/docs/feature-x.md>>): <<One-line description>>
- [<<API Reference>>](<<https://yoursite.com/docs/api.md>>): <<One-line description>>

## Optional

- [<<Changelog>>](<<https://yoursite.com/changelog.md>>): Release history
- [<<FAQ>>](<<https://yoursite.com/faq.md>>): Common questions
```

Link targets should be `.md` files where possible — llms.txt readers prefer Markdown over HTML.

## 5. tdmrep.json — EU CDSM Article 4 legal opt-out

File path: `/.well-known/tdmrep.json`. Only useful when EU legal defensibility matters. More formal than ai.txt; maintained by W3C Community Group.

```json
[
  {
    "location": "/",
    "tdm-reservation": 1,
    "tdm-policy": "<<https://yoursite.com/tdm-policy>>"
  }
]
```

- `tdm-reservation: 1` = rights reserved (opt-out of TDM)
- `tdm-policy` = URL where licensing/contact info lives. Create that page — even a short one — or the reservation looks unserious.

Serve as `application/json`.

## 6. Spawning-style `/ai.txt` — only when user explicitly asks

File path: `/ai.txt` (site root). Robots.txt-style directives, **not** Markdown. Don't confuse with aitxt.ing.

```
# ai.txt — Spawning format. Declares TDM reservation under EU CDSM Art. 4.
# Note: robots.txt entries for GPTBot/ClaudeBot/CCBot already cover training opt-out
# with much broader vendor compliance. This file is belt-and-suspenders.

User-Agent: *
Disallow: /
```

Category-scoped variant (block image/audio training, allow text):

```
User-Agent: *
Disallow: images
Disallow: audio
Allow: text
Allow: video
Allow: code
```

## 7. Cloudflare Content Signals — robots.txt extension

For sites behind Cloudflare that want purpose-based signals rather than per-vendor user-agent lists:

```
User-Agent: *
Content-Signal: ai-train=no, search=yes, ai-input=no
Allow: /
```

`ai-train=no` = don't use for training. `search=yes` = ok for search indexing. `ai-input=no` = don't feed into an AI's context window at inference time. Pair with the per-vendor rules in #1 for broader coverage — not all crawlers read Content-Signal yet.

## HTTP serving checklist

Regardless of which file(s) you produce:

- Serve over HTTPS.
- `Content-Type: text/plain; charset=utf-8` for robots.txt and Spawning ai.txt. `text/markdown` or `text/plain` for aitxt.ing and llms.txt. `application/json` for tdmrep.json.
- Return HTTP 200 with the file body. **A 404 means "fully allowed"** — the opposite of what most users assume. **A 5xx means "do not crawl"** — do not let the file break.
- OpenAI documents a ~24-hour delay before robots.txt changes take effect for ChatGPT search. Don't expect instant propagation.
