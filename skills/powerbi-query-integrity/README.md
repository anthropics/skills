# powerbi-query-integrity

An Agent Skill that makes Claude (or any agent that supports the SKILL.md standard) check every Power BI DAX result for silent truncation, incomplete totals and stale data, while keeping context usage low.

**Author:** Alberto Ramón López Franco · **License:** MIT

## What it does

- Runs a one-row *census* query alongside every data query, in the same call.
- Validates row count, reconciles the grouped sum against the model's total, flags blank groups and reports data freshness.
- Prefers aggregation in DAX, TOPN + "Rest" rows and re-aggregation over pulling detail.
- Warns about snapshot tables, non-additive measures and security-filtered blanks.
- Ends each answer with a one-line control: `✓` or `⚠`.

## How it differs from other Power BI skills

Most Power BI skills validate the **DAX code or the model**: syntax, best practices, performance, relationships. This skill validates the **result the agent receives**: that it is complete, that it reconciles, and that it is current.

The two kinds work together. Use a DAX-writing skill to build the measure, and this one to trust the number it returns.

## Origin

Built from hands-on testing of a Power BI connector, which showed that results are cut at a default row cap with no warning. The fix is a pattern, not a tool: let the model compute, and check every summary against an independent control.

## Install

- **Claude apps:** zip the `powerbi-query-integrity` folder and upload it under Customize > Skills.
- **Claude Code:** copy the folder to `~/.claude/skills/` (personal) or `.claude/skills/` (project).

## Files

- `SKILL.md`: the protocol.
- `references/dax-patterns.md`: DAX templates (census, TOPN + Rest, snapshot filtering, freshness cross-check, pagination).
