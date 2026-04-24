# AI User Agents — Reference (April 2026)

Source: `aitxt.md` §3.2. Use this list when generating or auditing `robots.txt`. Do not rely on memory — vendor lists drift.

## Verified AI user-agent tokens

Grouped by purpose. "Signal-only" means the vendor does not actually crawl with this token — disallowing it only suppresses training use of content collected by other means.

### Training crawlers (block these if the goal is "no AI training")

| Token                           | Vendor       | Honors robots.txt?   | Notes                                                                       |
| ------------------------------- | ------------ | -------------------- | --------------------------------------------------------------------------- |
| `GPTBot`                        | OpenAI       | Yes                  | Training data for ChatGPT / GPT models                                      |
| `ClaudeBot`                     | Anthropic    | Yes                  | Training data                                                               |
| `CCBot`                         | Common Crawl | Yes                  | Dataset building; feeds many downstream AI trainers                         |
| `Bytespider`                    | ByteDance    | Historically noisy   | TikTok search/recommendation/AI                                             |
| `Meta-ExternalAgent`            | Meta         | Yes (mostly)         | Training-adjacent                                                           |
| `Amazonbot`                     | Amazon       | Yes                  | Alexa / AI training                                                         |
| `cohere-ai`                     | Cohere       | Unconfirmed          | Training                                                                   |
| `cohere-training-data-crawler`  | Cohere       | Unconfirmed          | Training                                                                   |
| `Ai2Bot`, `Ai2Bot-Dolma`        | Ai2          | Yes                  | Training                                                                    |
| `Google-Extended`               | Google       | Yes (signal only)    | Opts out of Gemini/Vertex training. **Does NOT affect Google Search.**      |
| `Applebot-Extended`             | Apple        | Yes (signal only)    | Opts out of Apple Intelligence training. See inheritance trap below.        |

### Search / retrieval bots (usually ALLOW — they drive referral traffic)

| Token               | Vendor     | Honors robots.txt?                            | Purpose                            |
| ------------------- | ---------- | --------------------------------------------- | ---------------------------------- |
| `OAI-SearchBot`     | OpenAI     | Yes                                           | ChatGPT search indexing            |
| `Claude-SearchBot`  | Anthropic  | Yes                                           | Claude search indexing             |
| `PerplexityBot`     | Perplexity | Yes (documented violations exist)             | Perplexity answer engine           |
| `DuckAssistBot`     | DuckDuckGo | Yes                                           | DuckAssist                         |

### User-initiated fetches (the user typed a URL; handling varies)

| Token                   | Vendor     | Honors robots.txt?                                            |
| ----------------------- | ---------- | ------------------------------------------------------------- |
| `ChatGPT-User`          | OpenAI     | Partially — may bypass robots.txt for user-directed URLs      |
| `Claude-User`           | Anthropic  | Yes                                                           |
| `Perplexity-User`       | Perplexity | Documented to ignore robots.txt when user provides URL        |
| `meta-externalfetcher`  | Meta       | May bypass robots.txt on user context                         |
| `GoogleAgent-Mariner`   | Google     | May ignore robots.txt per Google's stated policy              |
| `Google-NotebookLM`     | Google     | Same                                                          |
| `GoogleAgent-URLContext`| Google     | Same                                                          |
| `Google-Firebase`       | Google     | Same                                                          |

## Deprecated tokens (retired in 2024 — harmless but outdated)

- `anthropic-ai` — replaced by `ClaudeBot` family
- `claude-web` — replaced by `ClaudeBot` family

If you see these in a user's file during an audit, flag them as no-ops and suggest replacing with the current `ClaudeBot` / `Claude-SearchBot` / `Claude-User` split.

## Traps to watch for during audits

### Applebot-Extended inheritance

If `robots.txt` has rules for `Googlebot` but **no** explicit `Applebot-Extended` rule, Applebot-Extended falls back to following `Googlebot` rules. Most sites want Googlebot allowed (for Google Search) but Apple Intelligence training blocked — inheritance silently defeats that. Always write an explicit `Applebot-Extended` rule when `Googlebot` is mentioned.

### Google-Extended is signal-only

`Google-Extended` is not a crawler — blocking it does not stop any HTTP request. It only tells Google not to use content (that it already fetched with Googlebot) for Gemini/Vertex training. Don't suggest it as a "block Googlebot from AI" solution; it's orthogonal to Googlebot entirely.

### Training allowed + search blocked

If a `robots.txt` has `GPTBot: Allow` and `OAI-SearchBot: Disallow`, that is almost certainly backwards — the user is giving away training data while cutting themselves off from ChatGPT search referral traffic. Flag loudly.

### Spoofing

HUMAN Security reports ~5.7% of requests presenting an AI-crawler user-agent are spoofed. robots.txt is advisory; IP verification is the real defense.

## IP-range endpoints (for spoof verification at the firewall / WAF layer)

- OpenAI: `https://openai.com/gptbot.json`, `https://openai.com/searchbot.json`, `https://openai.com/chatgpt-user.json`
- Common Crawl: `https://index.commoncrawl.org/ccbot.json` (also supports reverse-DNS, e.g. `18-97-14-84.crawl.commoncrawl.org`)
- Perplexity: `https://www.perplexity.com/perplexitybot.json`, `https://www.perplexity.com/perplexity-user.json`

These are the vendor-published JSON ranges; use them if the user is setting up server-side blocking rather than just publishing robots.txt.

## Recommended default block-list (most publishers, April 2026)

For "block AI training, keep AI search referral traffic":

**Disallow:** `GPTBot`, `ClaudeBot`, `CCBot`, `Bytespider`, `Meta-ExternalAgent`, `Amazonbot`, `cohere-ai`, `Google-Extended`, `Applebot-Extended`, `anthropic-ai` (legacy, belt-and-suspenders).

**Allow:** `OAI-SearchBot`, `ChatGPT-User`, `Claude-SearchBot`, `Claude-User`, `PerplexityBot`, `Perplexity-User`, `DuckAssistBot`.

**Default** (`User-agent: *`): `Allow: /`.

See `examples.md` for the concrete template.
