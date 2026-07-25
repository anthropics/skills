# Handoff Document Structure

This reference answers exactly one decision: **what sections does a handoff document need, and what content belongs in each?**

Pair with `scripts/handoff_template_generator.py` for the structured scaffold.

## Matt Pocock's Implicit Structure

Matt's SKILL.md names the components:

1. **Summary of current conversation** — what's been done
2. **Skills suggested for next session**
3. **References to artifacts** (PRDs, plans, ADRs, issues, commits, diffs) — NOT duplications
4. **Next-session focus** — if user passed an argument

This wrapper formalizes those into 5 standard sections.

## The Five Sections

### 1. Goal of next session

The single most important section. The next agent should be able to read this section alone and know what success looks like.

Pattern:
```
## Goal of next session

[2-3 sentences describing the outcome the next session must produce.]

Prompts to answer:
- [tailored to next-session focus: deployment / review / debug / design / test]
```

Bad: "Continue the work."
Good: "Open PR for the 3-skill batch (caveman, grill-me, handoff). Validate against karpathy-coder gate. Address any CI failures or review comments. Aim for green merge by EOD."

### 2. State of play

What's done vs in-progress vs blocking. The next agent needs this to avoid re-doing work or starting blocked work.

Pattern:
```
## State of play

**Done:**
- [list with paths/refs to artifacts]

**In progress:**
- [list mid-flight items + current branch/PR/file]

**Blocking:**
- [list blockers + who/what unblocks each]
```

Critical: be specific about paths + branches. "The auth refactor" is not enough; "`feature/auth-refactor` branch, last commit `abc1234`, blocked on CI" is.

### 3. Open decisions

Decisions the next agent must make (not "should consider" — must make). If a decision can be deferred, omit it.

Pattern:
```
## Open decisions

- [Decision 1: options + current lean + dependencies]
- [Decision 2: options + current lean + dependencies]
```

Each decision includes the user's current lean — saves the next agent from re-deriving.

### 4. Skills to use (next session)

Concrete list. Not "consider using ..." — name the skills.

Pattern:
```
## Skills to use (next session)

- `karpathy-coder` — for code-quality validation before PR
- `write-a-skill` — to validate any new SKILL.md against the 6-item checklist
- `ship-gate` — pre-production audit before merge
```

Run `skill_recommender.py` against the handoff to auto-populate this section.

### 5. Artifacts (reference only)

Paths + URLs. No inline content. This is the section where Matt's no-duplication rule is most often violated.

Pattern:
```
## Artifacts (reference only — do NOT duplicate)

- **PRD/Plan:** [path or URL]
- **ADRs:** [path]
- **Issues:** [#NNN]
- **Branch:** [name]
- **Open PRs:** [#NNN]
- **Recent commits:** [SHAs]
- **Validators run:** [results + links]
```

The next agent should be able to follow every link without needing additional context from the handoff.

## What Doesn't Belong in a Handoff

- **The full PRD** — link to it
- **The full ADR** — link to it
- **Issue descriptions** — `#NNN` reference is enough
- **Code snippets** — link to `file.py:42-80` with commit SHA
- **Long code blocks** — same; the file is the source of truth
- **The entire conversation history** — the next agent doesn't need every turn
- **Implementation details already captured in commits** — `git log` is the source

## How to Stay Within 100 Lines

A good handoff is ~50-100 lines. Beyond that signals duplication.

Tactics:
- Use reference markers `[name](url)` aggressively
- Compress "what's done" to bullet points with refs, not paragraphs
- Move detailed reasoning into ADRs; reference them in handoff
- Trust the next agent to read referenced docs

## Tailoring to Next-Session Focus

The `handoff_template_generator.py` detects keywords in the focus argument and tailors prompts:

| Focus keyword | Section emphasis | Tailored prompts |
|---|---|---|
| ship/deploy/PR | Deployment | Commands to ship, checks required, approvers, rollback |
| review/audit | Review | Checklist, sensitive files, similar patterns, past PR refs |
| debug/fix/investigate | Debug | Symptom, repro steps, tried-already, smallest case |
| design/plan/scope | Design | Outcome, constraints, rejected alternatives, reversibility |
| test/qa | Test | Test plan, existing coverage, edge cases, success measure |
| (other) | Default | Immediate action, blocker, files, open decisions |

## Anti-Patterns

1. **Handoff longer than the underlying PRD** — usually means duplication
2. **Handoff with no artifact references** — what's done if not in git?
3. **Handoff with vague decisions** — "should we use X?" without options + leans
4. **Handoff without next-session goal** — what is the next agent supposed to do?
5. **Handoff with stale paths** — branches deleted, files moved; verify before handing off
6. **Re-handing-off a handoff** — if Session B produces a handoff that just summarizes Session A's handoff, neither session did real work

## When This Reference Doesn't Help

- **Code-review handoff** — different format; PR review comments are the artifact
- **Customer-support handoff** — different domain; ticket templates apply
- **Live-meeting handoff** — different mode; verbal handoff + linked doc

---

**Source authorities (non-exhaustive):**

- **Matt Pocock — handoff** (https://github.com/mattpocock/skills/, MIT) — the 5-section structure (implicit)
- **DRY principle** (Hunt & Thomas, "The Pragmatic Programmer", 1999) — references > copies
- **Engineering runbook + playbook patterns** — on-call handoff discipline
- **Atlassian — Confluence page templates** — handoff page conventions
- **GitHub PR description templates** — what context goes where
- **Anthropic — Multi-agent continuity patterns** (https://docs.claude.com/en/docs/agents) — session continuity guidance
- **Kim et al. — "The Phoenix Project"** (2013) — shift-change handoff in DevOps
