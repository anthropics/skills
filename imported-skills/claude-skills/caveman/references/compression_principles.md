# Compression Principles for LLM Output

This reference answers exactly one decision: **what should be cut and what must stay when compressing LLM output for token efficiency?**

Pair with `scripts/caveman_compressor.py` for deterministic application.

## Matt Pocock's Foundational Insight

> "Respond terse like smart caveman. All technical substance stay. Only fluff die."
>
> — Matt Pocock, caveman SKILL.md

The crucial distinction: **substance** vs **fluff**. Caveman mode is aggressive about fluff and conservative about substance. Confusion between the two creates either bloated responses (under-cutting) or hallucinated answers (over-cutting).

## What Counts as Fluff (Safe to Drop)

| Category | Examples | Why safe to drop |
|---|---|---|
| **Articles** | a, an, the | Grammatical scaffolding; meaning preserved without them |
| **Filler** | just, really, basically, actually, simply, obviously | Add no information; speakers use as verbal pauses |
| **Pleasantries** | sure!, certainly, of course, happy to help | Social lubrication; cost tokens with zero info gain |
| **Hedging** | might, maybe, perhaps, likely, possibly | Either qualify with data or remove; vague hedging is fake precision |
| **Metatalk** | as you can see, worth noting, that said | Self-referential commentary about the response itself |
| **Verbose phrases** | "implementation of a solution for" → "fix"; "in order to" → "to" | Phrase-level redundancy |

## What Counts as Substance (Must Stay)

| Category | Examples | Why preserve |
|---|---|---|
| **Technical terms** | `useMemo`, NULL, HTTP/2, OAuth2 | Exact names matter; abbreviation breaks identifiers |
| **Code blocks** | All ```...``` regions | Syntactically meaningful; whitespace + characters matter |
| **Inline code** | `useState`, `auth_token` | Same as code blocks |
| **Quoted strings** | "expected value", 'string literal' | Exact text matters |
| **Error messages** | "TypeError: cannot read property X" | Diagnostic precision required |
| **Numbers + units** | 200ms, 4kb, 99.9% | Exactness matters for engineering decisions |
| **Causal claims** | "X causes Y" — can be compressed to "X -> Y" | The relationship is the substance |

## The Abbreviation Cost-Benefit

Abbreviating common technical terms saves tokens but only when:
1. The abbreviation is universally understood (DB, auth, config, fn — yes; ETL, ORM — maybe; "imp" for implementation — no)
2. The reader has full context (caveman responses are usually mid-conversation)
3. The exact term isn't being introduced (don't abbreviate the FIRST use of a term)

Matt's abbreviation list is conservative + universal:
- DB, auth, config, req, res, fn, impl, env, deps, repo, docs, app

## Causality Arrows: The Compression Win

Replacing verbose causality with arrows is high-leverage:

| Verbose | Caveman | Savings |
|---|---|---|
| "X leads to Y" (3 words) | "X -> Y" (1 unit) | 67% |
| "which causes Y to happen" (5 words) | "-> Y" (2 units) | 60% |
| "because of X, Y happens" (5 words) | "Y <- X" (2 units) | 60% |

Arrows are unambiguous + compact + preserve causality (not just adjacency).

## Compression Anti-Patterns

1. **Dropping subject pronouns at all costs** — "Bug in auth" is fine. "Auth bug, fix soon" loses clarity. Keep enough syntax to disambiguate.
2. **Over-abbreviating** — "MWMV" instead of "memory write/memory verify" forces reader to expand mentally; net cognitive cost goes up.
3. **Dropping units** — "Response takes 200" — 200 what? ms? bytes? Keep units always.
4. **Compressing security warnings** — Matt's explicit exception. A truncated security warning is worse than no caveman mode.
5. **Dropping examples** — "Bug in auth. Fix." — what bug? what fix? Caveman keeps the substance, just removes the wrapping.

## Compression vs Clarity Tradeoff

Compression is a tax on the reader. The trade-off is worth it when:
- The reader has the context to fill in the gaps (mid-conversation, technical peer)
- The information density is high enough to justify cognitive load
- The savings are meaningful (>20% token reduction)

Not worth it when:
- New context being established (introductions, first turns)
- Multi-step sequences where order matters
- Multi-stakeholder communication (caveman style confuses non-technical readers)
- Audio interfaces (caveman text reads badly when read aloud)

## How Much Compression Is Realistic?

Matt's claim is ~75% — this is the upper bound on extremely verbose responses (with multiple pleasantries + filler + hedging). Realistic ranges:

| Response type | Realistic compression |
|---|---|
| ChatGPT-style verbose response | 50-75% |
| Already-concise technical answer | 10-25% |
| Code-heavy response (most text is code) | 5-15% |
| Single-sentence answer | 0-30% |

The compressor in this skill targets 20-50% on typical mid-conversation responses, which is meaningful at scale.

## When This Reference Doesn't Help

- **Code minification** — different concern; this is about prose around code, not code itself
- **Prompt compression for inputs** — different mode; input compression has different rules
- **Speech synthesis** — caveman text reads poorly aloud
- **Marketing copy** — different goal; conversion > brevity

---

**Source authorities (non-exhaustive):**

- **Matt Pocock — caveman** (https://github.com/mattpocock/skills/, MIT) — the upstream source + rule set
- **Strunk & White — "The Elements of Style"** (1918) — Rule 17: "Omit needless words"
- **Plain Language Movement / Plain Writing Act of 2010** (https://www.plainlanguage.gov/) — government mandate for concise English; well-researched compression rules
- **Pinker, S. — "The Sense of Style"** (2014) — cognitive science of clear writing
- **Williams, J. — "Style: Toward Clarity and Grace"** (1995) — academic compression patterns
- **Anthropic — Prompt engineering for tokens** (https://docs.claude.com/en/docs/build-with-claude/prompt-engineering) — token-conscious patterns
- **OpenAI tokenizer documentation** — character-per-token ratios across cl100k_base / o200k_base
- **Pareto principle in writing** — 20% of words carry 80% of meaning
