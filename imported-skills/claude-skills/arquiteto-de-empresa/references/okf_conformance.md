# OKF Conformance (Open Knowledge Format v0.1)

Reference for the rules that make the Company Architect's output a **conformant OKF bundle** — a knowledge base readable by humans and by agents, with no translation layer.

## What an OKF bundle is

A **bundle** is a directory of Markdown files (`.md`). Each file represents **one concept**. The concept's canonical identity is its **relative path without the extension**:

```
03-financeiro/unit-economics.md   →  concept "03-financeiro/unit-economics"
```

The folder hierarchy is just physical organization. The real **semantic** structure emerges from the **links** between concepts (the graph), which is usually richer than the folder tree.

## Rule 1 — Each file is a concept

One file, one concept. Do not merge "strategy + financial" into a single `.md`. If a concept grows too large, break it into smaller concepts and link them. This keeps the graph navigable and the diffs readable under version control (git).

## Rule 2 — YAML frontmatter with mandatory `type`

Every **concept** file opens with a `---` YAML frontmatter block containing, at minimum, the `type` field. The other fields are optional and extra keys are tolerated.

```yaml
---
type: Financial Model            # REQUIRED — see type_vocabulary.md
title: Unit Economics
description: CAC, LTV, payback, and contribution margin
tags: [financial, metrics]
timestamp: 2026-06-19T10:00:00Z  # ISO 8601, last significant update
resource: https://docs.google.com/spreadsheets/d/...   # canonical URI, if any
status: draft                     # tolerated extra: draft | in-review | approved
version: 0.1                       # tolerated extra
---
```

The `type` value comes from a controlled and consistent vocabulary — see [`type_vocabulary.md`](type_vocabulary.md). It is `type` that lets an agent filter "all concepts of type `Persona`" without reading the body.

## Rule 3 — Relations are markdown links in the body

Concepts link to each other with **normal markdown links** inside the text:

```markdown
Pricing derives from the [Value Proposition](../01-estrategia/proposta-de-valor.md)
and feeds the [Projections](projecoes.md).
```

These links form the **knowledge graph**. Do **not** declare dependencies as arrays in the frontmatter — the graph lives in the body, where the link has context. Prefer relative paths (resilient to moving the bundle).

## Rule 4 — `index.md` and `log.md` are reserved

Two names have special semantics and do **not** carry `type`:

- **`index.md`** — listing/summary of the folder's content (progressive disclosure). Every folder has its own; the root `index.md` is the dashboard for the whole bundle.
- **`log.md`** — append-only history of changes and decisions. Usually only at the root.

A conformant linter treats an `index.md`/`log.md` that has a `type` as an error, and a concept that does **not** have one as an error.

## Rule 5 — Readable by human and machine

Plain markdown. No runtime, no SDK, no database. A human reads it in an editor; an agent reads the same file and the frontmatter gives it the structure. That is the format's thesis: **the documentation is the interface**, the same for both.

## Naming conventions

- Lowercase, no accents, hyphen instead of space: `unit-economics.md`, `proposta-de-valor.md`.
- SOPs in the format `SOP-01-process-name.md`.
- Folders numbered by phase: `00-fundacao`, `01-estrategia`, … `11-governanca`.
- Every folder has an `index.md`.

## Content of the reserved files

- **Folder `index.md`:** 1 paragraph of the area's purpose + a `| Concept | What it is | type | status |` table with a link to each file.
- **Root `log.md`:** chronological entries `## 2026-06-19T10:00:00Z — <title>` with: what changed, decision made, discarded alternatives, rationale.

## Conformance checklist (what the linter checks)

- [ ] Every concept (`.md` that is not `index.md`/`log.md`) has frontmatter with a non-empty `type`.
- [ ] `type` belongs to the vocabulary in [`type_vocabulary.md`](type_vocabulary.md).
- [ ] `index.md` and `log.md` do **not** have `type`.
- [ ] Relative markdown links resolve to existing files.
- [ ] Names in kebab-case, no accents/spaces.
- [ ] Every folder has an `index.md`.

## Sources

1. **Open Knowledge Format (OKF) v0.1** — open specification for packaging knowledge as Markdown + YAML frontmatter, originating in the Google Cloud / AI agents context.
2. **agentskills.io — SKILL.md standard** — the `SKILL.md` convention with YAML frontmatter adopted by Claude Code, Codex, Gemini CLI, and Hermes Agent (the same contract as this repository).
3. **CommonMark Spec** (https://spec.commonmark.org/) — portable Markdown base used in the concept bodies.
4. **YAML 1.2 Spec** (https://yaml.org/spec/1.2.2/) — frontmatter syntax.
5. **ISO 8601** — `timestamp` format (`2026-06-19T10:00:00Z`).
6. **Zettelkasten / Niklas Luhmann** — the "one note = one concept" principle and knowledge as a graph of links, the conceptual foundation of the bundle.
7. **Docs-as-Code** (Anne Gentle, *Docs Like Code*) — documentation versioned, reviewed, and built like software; justifies the bundle in git.
