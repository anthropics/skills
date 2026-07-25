# Companion Tooling

Interrogation tools + cs-* wrapper layered on top of Matt's grill-me skill.

## Validation Tools (stdlib Python)

| Tool | Purpose | Run when |
|---|---|---|
| `scripts/decision_tree_extractor.py` | Scan a plan doc for decision branches (intent / choice / open / tradeoff / dependency / question) | Starting a grill session — see what's there to interrogate |
| `scripts/question_generator.py` | Generate forcing questions from extracted branches with recommended answers + dependency-aware ordering | Producing the question list for a grill session |
| `scripts/grill_session_tracker.py` | JSON-backed session storage in `~/.grill_sessions/` — track answers across turns, resume sessions | Running a multi-turn grill (most real grills) |

All three:
- Stdlib-only
- Run with embedded sample if no input provided
- Output text or JSON (`--output json`)

## Session Storage

`grill_session_tracker.py` persists state to `~/.grill_sessions/<name>.json`. This enables:
- Resume a grill across days
- Switch between concurrent grills (e.g., per project)
- Audit which decisions were resolved when
- Generate a "decisions locked" summary at end

## cs-grill-master Persona Agent

Lives at `../agents/cs-grill-master.md`. Voice: relentless, one-question-at-a-time, codebase-exploration-first.

The persona's hard rule: **never bundle questions**. Even when there are 10 obvious follow-ups, ask one, wait for answer, then ask the next.

## `/cs:grill-me` Slash Command

Lives at `../commands/cs-grill-me.md`. Activation pattern:

1. `/cs:grill-me <path-to-plan>` — start grill session on plan doc
2. Persona asks Q1 with recommended answer
3. User answers
4. Persona asks Q2
5. ...continues until all branches resolved

## Why Wrap Matt's Original

Matt's grill-me skill is intentionally minimal (3 sentences). The wrapper adds:

1. **Automatic branch extraction** — manually identifying decision branches is the slow part; the extractor does it deterministically
2. **Question templating** — consistent question patterns per branch kind (intent / choice / tradeoff)
3. **Session persistence** — grills span days; persistence prevents re-asking + losing context
4. **Recommendation defaults** — every question carries a recommended answer (per Matt's "provide your recommended answer" rule)

## Attribution

Original: [matt-pocock/skills/skills/productivity/grill-me](https://github.com/mattpocock/skills/tree/main/skills/productivity/grill-me) (MIT).

---

**Source authorities (non-exhaustive):**

- **Matt Pocock — grill-me** (https://github.com/mattpocock/skills/, MIT) — the upstream source
- **Socratic Method** (5th-century BC) — interrogation as truth-finding; one-question-at-a-time discipline
- **YC office hours format** (Y Combinator) — forcing questions for founders; "what's blocking this?" + "why this and not Y?"
- **Cockburn, A. — "Writing Effective Use Cases"** (2000) — exploring decision branches in requirements
- **Fournier, C. — "The Manager's Path"** (2017) — interview discipline for hard decisions
- **Larson, W. — "An Elegant Puzzle"** (2019) — engineering manager decision-making patterns
- **5 Whys (Toyota Production System)** — Sakichi Toyoda — sequential interrogation for root cause
