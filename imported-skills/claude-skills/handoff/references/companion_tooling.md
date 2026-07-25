# Companion Tooling

Handoff-generation tools + cs-* wrapper layered on top of Matt's handoff skill.

## Validation Tools (stdlib Python)

| Tool | Purpose | Run when |
|---|---|---|
| `scripts/handoff_template_generator.py` | Generate a markdown scaffold tailored to next-session focus. Supports `--mktemp` for the path pattern Matt named | Starting a handoff document |
| `scripts/artifact_deduplicator.py` | Detect PRD/ADR/issue/commit content that should be replaced with a reference instead of inlined | Pre-flight check on a handoff draft |
| `scripts/skill_recommender.py` | Match handoff content to skills in this repo, ranked by signal strength | Producing the "Skills to use" section |

All three:
- Stdlib-only
- Run with embedded sample if no input provided
- Output text or JSON (`--output json`)

## The `mktemp` Path Pattern (Matt's Convention)

Matt's SKILL.md specifies:

> "Save it to a path produced by `mktemp -t handoff-XXXXXX.md` (read the file before you write to it)."

`handoff_template_generator.py --mktemp` honors this — uses `tempfile.mkstemp(prefix="handoff-", suffix=".md")` under the hood, returns the path so the caller can read-verify before writing the final content.

## cs-handoff-author Persona Agent

Lives at `../agents/cs-handoff-author.md`. Voice: continuity-focused, no-duplication-tolerated. The persona's hard rule: **if you find yourself typing content from a PRD/plan/ADR/issue, stop and replace with a reference**.

## `/cs:handoff` Slash Command

Lives at `../commands/cs-handoff.md`. Single-trigger handoff with argument hint per Matt's convention: `/cs:handoff <what-next-session-is-for>`.

## Why Wrap Matt's Original

Matt's handoff skill is intentionally minimal (1 paragraph). The wrapper adds:

1. **Tailored templates** — different next-session focuses (deploy/review/debug/design/test) emphasize different sections
2. **Dedup enforcement** — Matt's "do not duplicate" rule, programmatically checked
3. **Skill recommendation** — Matt says "suggest skills to be used" — the recommender automates this from handoff content

## Attribution

Original: [matt-pocock/skills/skills/productivity/handoff](https://github.com/mattpocock/skills/tree/main/skills/productivity/handoff) (MIT).

---

**Source authorities (non-exhaustive):**

- **Matt Pocock — handoff** (https://github.com/mattpocock/skills/, MIT) — the upstream source + mktemp convention + no-duplication rule
- **Anthropic — Multi-agent + session continuity patterns** (https://docs.claude.com/en/docs/agents) — handoff documentation patterns
- **Karpathy, A. — LLM Wiki pattern** (public commentary) — persistent context across sessions
- **Pinker, S. — "Sense of Style"** (2014) — write for the reader who lacks your context
- **Engineering team patterns — Runbook + Playbook discipline** — capturing context for the next on-call engineer
- **DRY principle (Hunt & Thomas, "The Pragmatic Programmer", 1999)** — Don't Repeat Yourself; references > copies
- **GitHub PR description conventions** — what context belongs in handoff vs PR vs ADR
