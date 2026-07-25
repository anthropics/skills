---
name: tech-debt-tracker
description: Scan codebases for technical debt, score severity, track trends, and generate prioritized remediation plans. Use when users mention tech debt, code quality, refactoring priority, debt scoring, cleanup sprints, or code health assessment. Also use for legacy code modernization planning and maintenance cost estimation.
---

# Tech Debt Tracker

**Tier**: POWERFUL 🔥  
**Category**: Engineering Process Automation  
**Expertise**: Code Quality, Technical Debt Management, Software Engineering

## Overview

Tech debt is one of the most insidious challenges in software development - it compounds over time, slowing down development velocity, increasing maintenance costs, and reducing code quality. This skill provides a comprehensive framework for identifying, analyzing, prioritizing, and tracking technical debt across codebases.

Tech debt isn't just about messy code - it encompasses architectural shortcuts, missing tests, outdated dependencies, documentation gaps, and infrastructure compromises. Like financial debt, it accrues "interest" through increased development time, higher bug rates, and reduced team velocity.

## What This Skill Provides

This skill offers three interconnected tools that form a complete tech debt management system:

1. **Debt Scanner** - Automatically identifies tech debt signals in your codebase
2. **Debt Prioritizer** - Analyzes and prioritizes debt items using cost-of-delay frameworks
3. **Debt Dashboard** - Tracks debt trends over time and provides executive reporting

Together, these tools enable engineering teams to make data-driven decisions about tech debt, balancing new feature development with maintenance work.

## Quick Start — scan → prioritize → dashboard

All paths relative to this skill folder. The scanner's JSON output feeds the prioritizer directly; dated inventory snapshots feed the dashboard.

### 1. Scan the codebase

```bash
python3 scripts/debt_scanner.py /path/to/codebase --format json --output debt_inventory.json
```

Emits `debt_inventory.json` with `scan_metadata`, `summary`, `debt_items[]`, `file_statistics`, and `recommendations`. Report the `summary` counts to the user. (Dry run: `assets/sample_codebase`.)

### 2. Prioritize the backlog

```bash
python3 scripts/debt_prioritizer.py debt_inventory.json --framework wsjf --team-size 6 --sprint-capacity 20 --format json --output debt_priorities.json
```

Frameworks: `cost_of_delay` (default), `wsjf`, `rice`. Output contains `prioritized_backlog` (work top-down), `sprint_allocation` (paste into sprint planning), and `insights`.

### 3. Track trends over time

Keep dated snapshots (`debt_YYYY-MM-DD.json`), then:

```bash
python3 scripts/debt_dashboard.py --input-dir snapshots/ --period monthly --format both --output debt_dashboard
```

Or pass files explicitly (samples: `assets/historical_debt_2024-01-15.json assets/historical_debt_2024-02-01.json`). The dashboard reports trend direction and executive-ready summaries — use it to verify a cleanup sprint actually reduced debt.

### Verification loop

After a remediation sprint: re-run step 1, re-run step 3 with the new snapshot, and assert the targeted categories' counts dropped. A cleanup that doesn't move the dashboard is rework, not debt paydown.

## Technical Debt Classification Framework
→ See references/debt-frameworks.md for details (also: references/debt-classification-taxonomy.md, references/prioritization-framework.md, references/stakeholder-communication-templates.md)

## Common Pitfalls and How to Avoid Them

### 1. Analysis Paralysis
**Problem**: Spending too much time analyzing debt instead of fixing it.
**Solution**: Set time limits for analysis, use "good enough" scoring for most items.

### 2. Perfectionism
**Problem**: Trying to eliminate all debt instead of managing it.
**Solution**: Focus on high-impact debt, accept that some debt is acceptable.

### 3. Ignoring Business Context
**Problem**: Prioritizing technical elegance over business value.
**Solution**: Always tie debt work to business outcomes and customer impact.

### 4. Inconsistent Application
**Problem**: Some teams adopt practices while others ignore them.
**Solution**: Make debt tracking part of standard development workflow.

### 5. Tool Over-Engineering
**Problem**: Building complex debt management systems that nobody uses.
**Solution**: Start simple, iterate based on actual usage patterns.

Technical debt management is not just about writing better code - it's about creating sustainable development practices that balance short-term delivery pressure with long-term system health. Use these tools and frameworks to make informed decisions about when and how to invest in debt reduction.
