# Handoff Structure — Five Sections, One Template

The handoff doc has exactly five sections. Use these headers verbatim — the SessionStart hook and downstream tooling expect them.

## 1. Goal of next session

One or two sentences. Either taken from the user's `argument-hint` value, or inferred from the most recent unresolved thread in the conversation.

**Good:**
> Finish wiring the redaction linter into `/cs:handoff` and ship a draft PR before EOD.

**Bad:**
> Continue working on the handoff skill.

The bad version gives the next agent no end-state. The good version tells them when to stop.

## 2. State of play

Three labelled lists. Every bullet references an artifact (commit hash, PR, branch, file path, issue).

```
- Done:
  - <thing> — <artifact: commit hash, PR, file path>
- In flight:
  - <thing> — <where it lives now>
- Blocked:
  - <thing> — <what's blocking + who/what unblocks>
```

If `include_git_context: true` in config, the template generator pre-fills a quick git block (current branch, last commit, dirty file count). That block is informational; you still write the prose bullets above it.

## 3. Open decisions

Each decision is a question. Format:

```
- Q: <one-sentence question>
  - Options considered: <a>, <b>, <c>
  - Lean: <option or "no lean yet"> — <one-line reason>
  - Forcing constraint: <deadline / dependency / budget>
```

If there are no open decisions, write `- None.` Do not invent decisions to fill space.

## 4. Skills to use

Hard cap at 5. Each entry: skill name + one-line *why this session needs it*.

```
- <skill-name> — <why>
- <skill-name> — <why>
```

The `skill_recommender.py` script generates a starter list scored against the goal text. Edit it. The recommender is a starting point, not the answer.

## 5. Artifacts

Paths and URLs. No bodies.

```
- PR: https://github.com/org/repo/pull/123
- Branch: feature/handoff-skill
- PRD: documentation/implementation/handoff.md
- Issue: https://github.com/org/repo/issues/456
- ADR: documentation/adr/0023-handoff-storage.md
```

## Worked example

```markdown
---
generated_at: 2026-05-21T17:42:00Z
goal: "Finish wiring the redaction linter into /cs:handoff and ship a draft PR before EOD."
---

# Handoff — 2026-05-21

## Goal of next session

Finish wiring the redaction linter into `/cs:handoff` and ship a draft PR before EOD.

## State of play

- Done:
  - Redaction linter implemented and unit-tested — commit `a1b2c3d`
  - First-run setup walks 5 questions and writes config — commit `d4e5f6g`
- In flight:
  - Wiring `cs-handoff.md` command to call linter after template generator — uncommitted in `~/work/handoff/`
- Blocked:
  - SessionStart hook smoke test on macOS — need access to mac, waiting on @teammate

## Open decisions

- Q: Should the SessionStart hook surface the *latest* handoff or *all* handoffs from today?
  - Options considered: latest only, all-from-today, user-configurable
  - Lean: latest only — keeps context window small
  - Forcing constraint: ships in v1.0, can change in v1.1
- Q: Strict redaction mode by default, or warn?
  - Options considered: strict, warn
  - Lean: strict — Matt's redaction sentence implies hard enforcement
  - Forcing constraint: none; reversible in config

## Skills to use

- handoff — to update this doc when work continues
- code-review — to review the PR before opening it
- security-scan — to confirm no secrets are committed alongside the linter
- update-docs — to update README with the SessionStart hook installation step

## Artifacts

- Branch: claude/handoff-skill-review-LnSxe
- Draft PR (not yet opened): will target same branch
- SKILL.md: productivity/handoff/skills/handoff/SKILL.md
- Linter: productivity/handoff/skills/handoff/scripts/redaction_linter.py
- Inspired by: https://github.com/mattpocock/skills/tree/main/skills/productivity/handoff
```

That example is what a clean handoff looks like. Anything significantly longer is probably duplicating an artifact and should be trimmed.

## Sources

- Matt Pocock, *Handoff skill* (MIT) — the no-duplication discipline and the original four content rules.
- Karpathy, *Software 3.0 talk* (2025) — context engineering: optimize for what the next agent *cannot* recover.
- Anthropic, *Claude Code SessionStart hooks documentation* — surfacing prior context as data, not instructions.
- Google SRE Workbook, *Postmortem culture* — naming open decisions and their forcing constraints.
- DORA / Forsgren et al., *Accelerate* — referencing artifacts rather than narrating work.
