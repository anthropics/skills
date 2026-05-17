---
name: ai-tells-validator
description: Detects and rewrites "AI-sounding" text. Invoke when you are about to ship cold-outbound email, marketing copy, LinkedIn DMs, blog drafts, or any prose where a reader would lose trust if it read as ChatGPT default. Pulls the freshest version of the Wikipedia "Signs of AI writing" catalog before every run. Supports two ops — `validate` (find tells) and `rewrite` (call Claude to clean a draft until the validator passes).
---

# ai-tells-validator

A flagging + rewriting skill grounded in **the live** `Wikipedia:Signs_of_AI_writing`. The skill prefetches the article on every invocation so banned-word lists stay current as the community catches new tells, then enforces them with hard, deterministic regex.

## When to use

Invoke this skill before sending or publishing any of:

- Cold outbound emails (any touch in a sequence).
- LinkedIn DMs / connection notes.
- Marketing-page copy, landing-page hero text.
- Founder posts, customer-facing announcements.
- Auto-generated blog drafts.

Do not use for:

- Internal code comments or commit messages (different bar; signs-of-AI doesn't translate).
- Conversational chat with the user.
- Long-form technical documentation (the rule-of-three pattern is genuinely useful in docs).

## How to invoke

**Validate (find tells):**

```sh
node ~/.claude/skills/ai-tells-validator/scripts/validate.mjs < draft.txt
# or
echo "your text" | node ~/.claude/skills/ai-tells-validator/scripts/validate.mjs
```

Exit code is **0** when the text is clean and **1** when any tell fires. JSON output goes to stdout:

```json
{
  "ok": false,
  "tells": [
    { "tag": "banned_word:delve", "quote": "…we delve into…", "category": "word" },
    { "tag": "punctuation:em_dash_overuse", "quote": "3 em-dashes", "category": "punctuation" }
  ],
  "word_count": 84,
  "source_freshness": "fetched 2026-05-17T15:12:00Z (3 min ago)"
}
```

**Rewrite (clean a draft until it passes):**

```sh
node ~/.claude/skills/ai-tells-validator/scripts/rewrite.mjs < draft.txt
```

Calls `claude -p` with the freshest banned list in the system prompt and retries up to 3 times if the output still contains tells. The cleaned text goes to stdout; full report (attempts, tells eliminated, final findings) goes to stderr.

## Flags (both CLIs)

- `--fresh` — force refetch of the Wikipedia source (default: refetch if cache > 1h old).
- `--cache-ok` — use the cached copy unconditionally (skip network).
- `--source <url>` — override the source page (default `https://en.wikipedia.org/wiki/Wikipedia:Signs_of_AI_writing`).
- `--max-em-dashes <n>` — relax the em-dash cap (default: 1).
- `--allow <tag,tag>` — suppress specific tell tags (e.g. `--allow banned_word:landscape` if your domain is geography).

## What it catches

Pulled live from the Wikipedia article + hardcoded augmentations:

- **Words**: `delve`, `tapestry`, `intricate`, `landscape`, `meticulous`, `pivotal`, `robust`, `showcase`, `testament`, `underscore`, plus the modern SaaS-pitch vocabulary (`leverage`, `streamline`, `transformative`, `unlock`, `empower`, `seamless`, `synergy`, ...).
- **Phrases**: `I hope this email finds you well`, `circling back`, `just checking in`, `in conclusion`, `plays a vital role`, `value proposition`, `looking forward to hearing`, ...
- **Patterns**:
  - Negative parallelism (`not X, but Y` / `aren't X — they're Y`).
  - Rule-of-three adjective lists (`clear, sourced, and trustworthy`).
  - Trailing participle clauses (`, ensuring X`, `, driving Y`).
  - `Whether you're X or Y…`, `Excited to ___`.
- **Punctuation**: em-dash overuse (≥2 per message), smart/curly quotes.
- **Structure**: `---` thematic breaks inside body copy.

## What it does NOT catch

- Factual hallucinations. Run a separate fact-check pass.
- Voice mismatch with a personal brand. Pair with a per-author voice prompt.
- Tone-deaf framing. The validator catches form, not judgment.

## Implementation notes

- **Prefetch policy**: the Wikipedia page is fetched at every CLI invocation by default. A 1-hour mtime cache at `~/.cache/ai-tells-validator/wiki.md` prevents repeat hits within a session. `--fresh` busts the cache; `--cache-ok` skips the network entirely (useful for CI / offline).
- **Parse strategy**: the Wikipedia page is plain wikitext; the parser pulls bullet entries under known section headings, plus a hardcoded list of always-banned items the article doesn't yet name explicitly.
- **Retry loop in rewrite**: Claude is called with the failing tells in the user prompt. After 3 failed attempts the original text is returned unchanged with `exit_code = 2`.

## Install

```sh
mkdir -p ~/.claude/skills
git clone https://github.com/<you>/ai-tells-validator ~/.claude/skills/ai-tells-validator
```

That's it — Claude Code auto-discovers the skill on next session.

## Run tests

```sh
cd ~/.claude/skills/ai-tells-validator
node --test tests/
```

## Source of truth

Catalog: <https://en.wikipedia.org/wiki/Wikipedia:Signs_of_AI_writing>. The skill refetches before every run.
