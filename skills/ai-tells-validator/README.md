# ai-tells-validator

A Claude Code skill (and standalone CLI) that **flags and rewrites AI-sounding text** — grounded in the live Wikipedia [`Signs of AI writing`](https://en.wikipedia.org/wiki/Wikipedia:Signs_of_AI_writing) catalog.

It refetches that page on every run, parses the bulleted lists into a structured rule set, augments with a hardcoded set of SaaS-pitch tells the article doesn't yet name, and enforces every rule with deterministic regex. Output is JSON for `validate` and clean text for `rewrite`.

If you're shipping cold-outbound, marketing copy, LinkedIn DMs, or any prose where "this reads as ChatGPT" is a trust-killer, this is your last-mile gate.

---

## Install

As a Claude Code skill:

```sh
mkdir -p ~/.claude/skills
git clone https://github.com/<you>/ai-tells-validator ~/.claude/skills/ai-tells-validator
```

Claude Code auto-discovers it on next session.

As a standalone CLI:

```sh
git clone https://github.com/<you>/ai-tells-validator
cd ai-tells-validator
npm link   # optional — gives you `ai-tells-validate` and `ai-tells-rewrite` on PATH
```

No `npm install` step needed. The skill has zero runtime dependencies (Node 20+, native fetch, native test runner).

---

## Quick start

```sh
# Find tells in a draft
echo "We delve into the intricate landscape of fraud detection." | node scripts/validate.mjs
# → exit 1, JSON report of every violation

# Rewrite a draft until it passes
cat draft.txt | node scripts/rewrite.mjs > clean.txt
# → exit 0 on success; stderr has the rewrite report
```

---

## What it catches

The validator merges two sources of rules:

1. **Live Wikipedia catalog** — bulleted items pulled from sections like "Overused words", "Common phrases", "AI vocabulary", "Promotional language". Refreshed on every run with a 1-hour mtime cache.
2. **Hardcoded augmentation** — modern SaaS-pitch vocabulary and canned email tropes the Wikipedia article doesn't yet name explicitly (`leverage`, `unlock`, `seamless`, `value proposition`, `looking forward to hearing`, etc.).

Both feed the same finding categories:

| Category | Examples |
|---|---|
| `banned_word:*` | `delve`, `tapestry`, `intricate`, `transformative`, `paradigm`, `leverage`, `unlock`, `seamless`, `synergy` |
| `banned_phrase:*` | `I hope this finds you well`, `circling back`, `just checking in`, `in conclusion`, `plays a vital role`, `value proposition`, `looking forward to hearing` |
| `pattern:negative_parallelism` | `Not just X, but Y` / `aren't X — they're Y` |
| `pattern:rule_of_three` | `clear, sourced, and trustworthy` |
| `pattern:participle_tail` | `, ensuring X` / `, driving Y` / `, reinforcing Z` |
| `pattern:whether_youre` | `Whether you're X or Y…` |
| `pattern:excited_to` | `Excited to ___` |
| `punctuation:em_dash_overuse` | More than 1 em-dash per message |
| `punctuation:smart_quotes` | `"curly"` instead of `"straight"` |
| `structure:thematic_break` | `---` inside body copy |

Every category includes the offending quote so you can read what tripped the rule.

---

## CLIs

### `validate`

```
ai-tells-validate [flags] < input.txt
```

Flags:

| Flag | Default | What |
|---|---|---|
| `--fresh` | — | Force refetch of the source catalog. |
| `--cache-ok` | — | Use cached catalog only; skip network (CI / offline). |
| `--source <url>` | Wikipedia | Override source URL. |
| `--file <path>` | — | Read input from a file. |
| `--allow <tag,tag>` | — | Suppress specific findings (e.g. `banned_word:landscape` if your domain is geography). |
| `--max-em-dashes <n>` | `1` | Cap em-dashes per message. |

Exit codes:

- `0` clean
- `1` tells found
- `2` infrastructure error

### `rewrite`

```
ai-tells-rewrite [flags] < draft.txt > clean.txt
```

Same flags as `validate`, plus:

| Flag | Default | What |
|---|---|---|
| `--max-retries <n>` | `3` | How many times to re-prompt Claude on failure. |
| `--model <alias>` | `sonnet` | Claude model alias. |
| `--voice <constraint>` | — | One-line voice/brand note injected into the rewrite prompt. |

Calls `claude -p` with the freshest banned list in the system prompt and the failing tells in the user prompt. Stops as soon as the validator passes. If retries exhaust, returns the original text and exits `2` — better to surface the failure than silently ship.

---

## Prefetch policy

The Wikipedia catalog is refetched **on every CLI invocation** by default, capped by a 1-hour mtime cache at `~/.cache/ai-tells-validator/wiki.md` to avoid hammering Wikipedia when the same CLI is called in a tight loop.

- `--fresh` busts the cache (e.g. when you know an editor just landed a new banned word).
- `--cache-ok` skips the network entirely. Use this in CI or when running fully offline.
- The fetcher falls back to the cached copy when the network is down, with a warning on stderr.

Source is the MediaWiki `action=parse&prop=wikitext` endpoint — the parser consumes wikitext, not rendered HTML, which is more stable across the article's frequent re-organizations.

---

## Why bother

Reviewers who spot one `delve` or one `not just X, but Y` lose trust in the whole message. The cost of catching it (one retry, ~3s of Claude) is dramatically lower than the cost of shipping it once. We hit this concretely: a 44-recipient outbound campaign that looked fine on inspection failed the validator on 38/44 drafts — almost all em-dash overuse. Without the gate, that's 38 obvious tells shipped to senior buyers.

The Wikipedia catalog is community-maintained and gets refreshed faster than any local rule list — which is why the skill prefetches.

---

## Tests

```sh
node --test tests/validator.test.mjs
```

13 tests cover hardcoded rules, parsing fixtures, and the `--allow` suppression path.

---

## Limitations

- **Factual hallucinations** are out of scope. Run a separate fact-check.
- **Voice mismatch** isn't caught. Pair this with a per-author voice prompt (`--voice "founder-led, lowercase, no buzzwords"`).
- **Tone-deaf framing** isn't caught — only form, not judgment.
- The Wikipedia parser is forgiving (best-effort + hardcoded backstop). If a section heading is renamed, the parser falls back on the hardcoded baseline rather than missing entries entirely.

---

## License

MIT. See `LICENSE`.
