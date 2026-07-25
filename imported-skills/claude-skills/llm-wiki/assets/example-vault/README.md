# Example Vault — "LLM Interpretability"

A minimal worked example to study before initializing your own.

**Not** a runnable vault — it's missing most files. The goal is to show what a healthy small vault looks like after ingesting 2-3 sources on one topic.

## Layout

```
example-vault/
├── raw/
│   └── assets/
├── wiki/
│   ├── index.md
│   ├── log.md
│   ├── entities/
│   │   └── anthropic.md
│   ├── concepts/
│   │   └── sparse-autoencoder.md
│   ├── sources/
│   │   └── monosemanticity.md
│   └── synthesis/
│       └── interpretability-overview.md
├── CLAUDE.md
└── AGENTS.md
```

## What to notice

1. **Every page has frontmatter.** This is what makes the index + lint scripts work.
2. **The source page is the single source of truth** for claims from that paper. Other pages cite it rather than duplicating content.
3. **`index.md` is organized by category**, not chronologically.
4. **`log.md` uses the standardized header format** `## [YYYY-MM-DD] <op> | <title>`.
5. **Cross-references are wikilinks**, not prose references. `[[sources/monosemanticity]]`, not "see the Monosemanticity paper".
6. **The synthesis page has a `How this synthesis has changed` section.** Append-only history so you can see the thesis evolve.
