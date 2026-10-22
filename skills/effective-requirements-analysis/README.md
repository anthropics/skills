# Effective Requirements Analysis

A requirements-analysis skill for B2B / enterprise product managers.

When a business stakeholder hands you a one-line request — "can you add an export button?", "customers keep complaining about double bookings" — you face a choice between two bad options: write a PRD full of guesses, or ask questions and look slow. This skill does the second thing, with structure.

**Core principle: a requirement is expectation minus current state.** What users ask for is always a *solution-level* requirement. Requirements analysis routes around the solution to recover the *problem-level* requirement — who, in what situation, is affected how, and what is lost — and only then proposes a solution that costs less.

**We are the solution experts; the customer is only the problem expert.**

## The iron rule: interview first, analyze second

Until the user has answered the first round of questions, the skill produces exactly two files — a **Clarification Question List** and an **Interview & Assumption Register**. Nothing else. No PRD, no flows, no feature list, no "working draft".

This is enforced by a gate, not by good intentions. A bundled script checks the artifacts directory at every stage and fails loudly when analysis conclusions leak into the interview files:

```bash
python3 scripts/check_artifacts.py <artifacts-dir> --stage G1   # only the two files, no conclusions inside
python3 scripts/check_artifacts.py <artifacts-dir> --stage G2   # identifier closure, traceability, S-xx compliance
python3 scripts/check_artifacts.py <artifacts-dir> --stage G3   # everything, plus prefix collisions
```

The gate checks **content, not file count**. Smuggling a domain model into an "appendix" of the register, or renaming a feature list to "Appendix: what we're doing this time", does not get past it — the script looks at what the content *is*.

## What it produces

Four requirement tracks — value, functional, data, non-functional — plus business rules and constraints, consolidated into a Requirements Specification. Supporting material:

| File | Purpose |
|---|---|
| `SKILL.md` | The method, the stage gates, the identifier system, common mistakes |
| `references/interview-playbook.md` | Questioning techniques and a bank of ready-to-ask questions |
| `references/task-playbook.md` | The 17 key analysis tasks and when each may be trimmed |
| `references/artifacts.md` | Templates for every artifact in the set |
| `templates/srs-outline.md` | Requirements Specification skeleton |
| `templates/daily-change.md` | Template for change / improvement requests |
| `scripts/check_artifacts.py` | Artifact self-check script (pure Python stdlib, no dependencies) |

## The identifier system

Every artifact is traceable through numbered records with a registered prefix:

| Prefix | Meaning |
|---|---|
| `Q-xx` | Question asked, awaiting an answer |
| `A-xx` | Fact confirmed by the user |
| `S-xx` | Analyst's assumption — with how to verify it and what happens if it fails |
| `T-xx` | Business term definition |
| `F-xx` / `NFR-xx` / `AC-xx` | Functional requirement / non-functional requirement / acceptance criterion |

Prefixes form **cohorts**, and a prefix may not be reused across unrelated cohorts. The script distinguishes two things people routinely conflate:

- **Collision** — one prefix meaning two unrelated things in two cohorts → **error**
- **Reference** — the same identifier restated across artifacts → fine, may be reworded but not repointed

Cohort membership is derived from the **column or section a record sits in**, not from what the record is called. That distinction matters: in `### Q-05 (frequency and scenario patterns)` the word "scenario" is the *question's name*, not a column, and treating it as one produces a pile of false collisions.

## Install

```bash
# Claude Code / Codex / Cursor / any Agent Skills-compatible agent
npx skills add yangdavip/effective-requirements-analysis-skill

# Claude Code plugin marketplace
/plugin marketplace add yangdavip/effective-requirements-analysis-skill
```

Or copy the `skills/effective-requirements-analysis/` folder into your agent's skills directory (`.claude/skills/`, `.agents/skills/`, `.codex/skills/`, `.gemini/skills/`, `.config/opencode/skills/`, …).

## Try it

> Our booking system keeps double-booking appointments. The front desk says we just need a cap on bookings per time slot. Help me work out what's actually needed here.

The skill will push back on the proposed solution, ask 5–8 questions with a concrete handle ("think of the last time this happened — roughly when, which slot, how many people showed up?"), and refuse to write anything else until you answer.

## Notes

- The script runs on Python 3.8+ with the standard library only — no dependencies.
- Chinese users: the description includes Chinese trigger words (需求分析, 需求澄清, 需求评审 …), so the skill activates on Chinese requests. The Chinese version of this skill, maintained in parallel, lives in the same repository.

## License

MIT — see `LICENSE`.
