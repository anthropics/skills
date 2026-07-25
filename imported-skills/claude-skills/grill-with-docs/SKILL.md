---
name: grill-with-docs
description: Docs-anchored grilling session — challenges a plan against the project's existing language (CONTEXT.md) and recorded decisions (docs/adr/), and updates those files inline as terminology and decisions crystallise. Use when user wants to stress-test a plan against documented domain language, or mentions "grill with docs".
license: MIT
metadata:
  derived_from: "https://github.com/mattpocock/skills/tree/main/skills/engineering/grill-with-docs"
  original_author: "Matt Pocock (@mattpocock)"
  original_license: MIT
  voice: "Matt Pocock — relentless, one-at-a-time, codebase-and-docs-first, ADRs only when 3 criteria are met"
  version: 1.0.0
---

# Grill with Docs

> Derived from [Matt Pocock's grill-with-docs](https://github.com/mattpocock/skills/tree/main/skills/engineering/grill-with-docs) (MIT, © 2026 Matt Pocock). Matt's interview discipline + docs-anchored grilling rules preserved verbatim under MIT. Additions in this repo: 3 stdlib validators (CONTEXT.md linter, ADR scanner, glossary↔code consistency check), 3 in-depth references each citing 7+ authoritative sources, `cs-grill-with-docs` agent, `/cs:grill-with-docs` command. See [Wrapper additions](#wrapper-additions) below.

<what-to-do>

Interview me relentlessly about every aspect of this plan until we reach a shared understanding. Walk down each branch of the design tree, resolving dependencies between decisions one-by-one. For each question, provide your recommended answer.

Ask the questions one at a time, waiting for feedback on each question before continuing.

If a question can be answered by exploring the codebase, explore the codebase instead.

</what-to-do>

<supporting-info>

## Domain awareness

During codebase exploration, also look for existing documentation:

### File structure

Most repos have a single context:

```
/
├── CONTEXT.md
├── docs/
│   └── adr/
│       ├── 0001-event-sourced-orders.md
│       └── 0002-postgres-for-write-model.md
└── src/
```

If a `CONTEXT-MAP.md` exists at the root, the repo has multiple contexts. The map points to where each one lives:

```
/
├── CONTEXT-MAP.md
├── docs/
│   └── adr/                          ← system-wide decisions
├── src/
│   ├── ordering/
│   │   ├── CONTEXT.md
│   │   └── docs/adr/                 ← context-specific decisions
│   └── billing/
│       ├── CONTEXT.md
│       └── docs/adr/
```

Create files lazily — only when you have something to write. If no `CONTEXT.md` exists, create one when the first term is resolved. If no `docs/adr/` exists, create it when the first ADR is needed.

## During the session

### Challenge against the glossary

When the user uses a term that conflicts with the existing language in `CONTEXT.md`, call it out immediately. "Your glossary defines 'cancellation' as X, but you seem to mean Y — which is it?"

### Sharpen fuzzy language

When the user uses vague or overloaded terms, propose a precise canonical term. "You're saying 'account' — do you mean the Customer or the User? Those are different things."

### Discuss concrete scenarios

When domain relationships are being discussed, stress-test them with specific scenarios. Invent scenarios that probe edge cases and force the user to be precise about the boundaries between concepts.

### Cross-reference with code

When the user states how something works, check whether the code agrees. If you find a contradiction, surface it: "Your code cancels entire Orders, but you just said partial cancellation is possible — which is right?"

### Update CONTEXT.md inline

When a term is resolved, update `CONTEXT.md` right there. Don't batch these up — capture them as they happen. Use the format in [CONTEXT-FORMAT.md](./CONTEXT-FORMAT.md).

`CONTEXT.md` should be totally devoid of implementation details. Do not treat `CONTEXT.md` as a spec, a scratch pad, or a repository for implementation decisions. It is a glossary and nothing else.

### Offer ADRs sparingly

Only offer to create an ADR when all three are true:

1. **Hard to reverse** — the cost of changing your mind later is meaningful
2. **Surprising without context** — a future reader will wonder "why did they do it this way?"
3. **The result of a real trade-off** — there were genuine alternatives and you picked one for specific reasons

If any of the three is missing, skip the ADR. Use the format in [ADR-FORMAT.md](./ADR-FORMAT.md).

</supporting-info>

## Wrapper Additions

The additions below are **not** part of Matt's upstream skill. They operationalize the upstream's rules into deterministic, stdlib-only validators that pair naturally with the interview loop.

### Workflow (with wrapper tools)

1. **Pre-flight (before the first question):**
   - Run `scripts/context_md_linter.py CONTEXT.md` if a `CONTEXT.md` exists — confirms the glossary is well-formed before grilling against it.
   - Run `scripts/adr_scanner.py docs/adr/` if `docs/adr/` exists — surfaces numbering gaps, malformed ADRs, status-frontmatter inconsistencies.
   - Run `scripts/glossary_code_consistency.py --context CONTEXT.md --code src/` — flags defined-but-unused terms (dead glossary) and code-only common nouns that may need definitions. Use these flags as opening grill questions.

2. **During the session (Matt's rules apply):**
   - One question per turn, walking depth-first.
   - When a term is sharpened: edit `CONTEXT.md` immediately; re-run `context_md_linter.py` if the edit is structural.
   - When an ADR is warranted: write it under `docs/adr/`; re-run `adr_scanner.py` to confirm numbering.

3. **Closing:**
   - Final `glossary_code_consistency.py` run to confirm no new orphan terms were introduced.
   - Summarize: terms added/refined, ADRs written, scenarios discussed, open items.

### Tools (stdlib-only)

| Tool | One-line role |
|---|---|
| `scripts/context_md_linter.py` | Validate `CONTEXT.md` against the CONTEXT-FORMAT.md structure. PASS/WARN/FAIL per rule. |
| `scripts/adr_scanner.py` | Walk `docs/adr/`, check `NNNN-slug.md` pattern, numbering integrity, body completeness. |
| `scripts/glossary_code_consistency.py` | Cross-reference bold terms in `CONTEXT.md` against codebase usage. Flag dead glossary + code-only common nouns. |

### References (citations behind each rule)

- [`references/ubiquitous_language.md`](references/ubiquitous_language.md) — why a glossary belongs in source control (Evans, Vernon, Khononov, Wlaschin, Brandolini, Avram & Marinescu, Fowler)
- [`references/adr_practice.md`](references/adr_practice.md) — when an ADR earns its keep (Nygard, Tyree & Akerman, Zimmermann Y-statements, MADR, ThoughtWorks Radar, adr-tools, Backstage)
- [`references/context_md_as_artifact.md`](references/context_md_as_artifact.md) — CONTEXT.md as living artifact (Khononov on language drift, Kernighan on naming, BoundedContext bliki, Confluent on data contracts, Brandolini on EventStorming glossary)

### Companion

- Agent: `cs-grill-with-docs` (see `../../agents/cs-grill-with-docs.md`)
- Command: `/cs:grill-with-docs` (see `../../commands/cs-grill-with-docs.md`)

---

**Version:** 1.0.0
**Derived:** Matt Pocock's grill-with-docs (MIT) + this repo's wrapper
