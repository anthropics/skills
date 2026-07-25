# Loop Library (vendored skill)

This folder is a **verbatim copy** of the `loop-library` skill from
[Forward-Future/loop-library](https://github.com/Forward-Future/loop-library)
(`skills/loop-library/`). `SKILL.md`, `agents/openai.yaml`,
`references/discover.md`, and `references/audit.md` are unchanged from upstream
(byte-for-byte). Licensed under the [MIT License](LICENSE) © Forward Future.

## What this skill is

An installable guide that helps an AI agent **discover, find, audit, repair,
adapt, or design repeatable agent loops** through conversation. A loop is a
bounded feedback system — what to do, how to check it, what to try next, and
when to stop — not permission for endless autonomy.

Invoke it by describing a task, e.g.:

```text
/loop-library Find a published loop for keeping our documentation current.
/loop-library Analyze this repo for repeated work and turn the best candidate into a loop.
/loop-library Audit this loop and repair only material problems: [paste loop]
```

## About the published loops

The individual published loops (the 26+ practitioner recipes) are **not** stored
in this folder, and they are **not** in the upstream Git tree either. Per the
upstream README they are "intentionally not committed to GitHub" — they live in
the live, database-backed catalog and are fetched at runtime:

- Catalog (Markdown): <https://signals.forwardfuture.ai/loop-library/catalog.md>
- Catalog (JSON): <https://signals.forwardfuture.ai/loop-library/catalog.json>

The skill reads this live catalog as the single source of truth when it
recommends a published loop. If the live catalog is unreachable, the skill
reports that published-loop discovery is temporarily unavailable rather than
substituting stale or memorized content — this is by design, so the catalog is
never forked out of date.

## Updating

Re-vendor from upstream when the skill changes:

```bash
npx skills add Forward-Future/loop-library --skill loop-library --agent claude-code -g -y
# or copy skills/loop-library/ from a fresh clone of Forward-Future/loop-library
```
