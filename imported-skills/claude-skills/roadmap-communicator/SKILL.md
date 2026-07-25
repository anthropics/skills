---
name: roadmap-communicator
description: Use when preparing roadmap narratives, release notes, changelogs, or stakeholder updates tailored for executives, engineering teams, and customers.
---

# Roadmap Communicator

Create clear roadmap communication artifacts for internal and external stakeholders.

## When To Use

Use this skill for:
- Building roadmap presentations in different formats
- Writing stakeholder updates (board, engineering, customers)
- Producing release notes (user-facing and internal)
- Generating changelogs from git history
- Structuring feature announcements

## Roadmap Formats

1. Now / Next / Later
- Best for uncertainty and strategic flexibility.
- Communicate direction without false precision.

2. Timeline roadmap
- Best for fixed-date commitments and launch coordination.
- Requires active risk and dependency management.

3. Theme-based roadmap
- Best for outcome-led planning and cross-team alignment.
- Groups initiatives by problem space or strategic objective.

See `references/roadmap-templates.md` for templates.

## Stakeholder Update Patterns

### Board / Executive
- Outcome and risk oriented
- Focus on progress against strategic goals
- Highlight trade-offs and required decisions

### Engineering
- Scope, dependencies, and sequencing clarity
- Status, blockers, and resourcing implications

### Customers
- Value narrative and timing window
- What is available now vs upcoming
- Clear expectation setting

See `references/communication-templates.md` for reusable templates.

## Release Notes Guidance

### User-Facing Release Notes
- Lead with user value, not internal implementation details.
- Group by workflows or user jobs.
- Include migration/behavior changes explicitly.

### Internal Release Notes
- Include technical details, operational impact, and known issues.
- Capture rollout plan, rollback criteria, and monitoring notes.

## Changelog Generation

Use:
```bash
python3 scripts/changelog_generator.py --from v1.0.0 --to HEAD
```

Features:
- Reads git log range
- Parses conventional commit prefixes
- Groups entries by type (`feat`, `fix`, `chore`, etc.)
- Outputs markdown or plain text

## Feature Announcement Framework

1. Problem context
2. What changed
3. Why it matters
4. Who benefits most
5. How to get started
6. Call to action and feedback channel

## Communication Quality Checklist

- [ ] Audience-specific framing is explicit.
- [ ] Outcomes and trade-offs are clear.
- [ ] Terminology is consistent across artifacts.
- [ ] Risks and dependencies are not hidden.
- [ ] Next actions and owners are specified.
