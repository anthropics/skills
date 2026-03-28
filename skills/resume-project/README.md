# resume-project

**A Claude Code skill that transforms engineering project experience into industrial-strength resume bullets with architectural depth.**

Most engineers describe *what* they built. This skill forces you to describe *why* you made each architectural decision, *what was broken before* your solution existed, and *what measurably improved* after. The result reads like a Staff Engineer wrote it.

---

## Two input modes

**Mode A — Code repository**
Point it at a codebase. The skill scans the architecture, maps data flows (Producer → Sidecar → Consumer), detects scale signals, then interviews you to fill in business context and quantified results.

**Mode B — Paste a description**
Already have bullet drafts? Paste them in. The skill audits for the 3 weakest points and asks targeted questions before rewriting.

---

## Core mechanism: Interceptor

Before generating any bullet, the Interceptor blocks if any of these are missing:

- **Before state** — what was broken or missing before your solution?
- **Decision rationale** — why this approach and not the alternative?
- **Quantified result** — what actually improved, and by how much?

No placeholders, no estimates — only what you can confirm.

---

## Output format

Bilingual (Chinese + English), with:

- `[Topic labels]` on each bullet
- **Decision sentences**: *"Abandoned X (reason) in favor of Y, via mechanism Z, achieving result W"*
- Nested sub-bullets for multi-tier systems
- `[TBD]` placeholders for unconfirmed metrics — a reminder to fill before submitting

Results accumulate in `~/.claude/resume-library.md` across sessions.

---

## Installation

```bash
# From ClawHub
npx clawhub install resume-project

# From GitHub
claude skill install https://github.com/wwaguai/resume-project-skill
```

## Usage

```
/resume-project
```

Then either paste a project description or provide a path to a codebase.

---

## Example transformation

**Before (typical):**
> Responsible for the search module, implemented full-text search using Elasticsearch with sharding.

**After (with this skill):**
> **[Distributed Cache Architecture]** Abandoned per-request DB queries (latency unbounded under write contention) in favor of a write-through cache layer with TTL-based invalidation, eliminating hot-path read amplification at peak load — reducing P99 from [TBD]ms to [TBD]ms with zero consistency incidents over [TBD] months.

---

## License

MIT
