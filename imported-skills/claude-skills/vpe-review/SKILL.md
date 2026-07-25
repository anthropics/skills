---
name: "vpe-review"
description: "/cs:vpe-review <plan> — Throughput-first VP of Engineering interrogation of any plan that touches delivery, eng hiring, team structure, or production discipline. Use when cycle time balloons, DORA metrics slide, or before committing to an eng hiring wave or a reorg."
---

# /cs:vpe-review — VPE Forcing Questions

**Command:** `/cs:vpe-review <plan>`

The throughput-first VPE pressure-tests any plan touching eng operations. Six questions before any delivery commitment, eng hiring expansion, team restructure, or production-discipline change.

## When to Run

- Before quarterly delivery commitment (sprint planning, OKR review)
- Before approving an eng hiring plan
- Before restructuring eng teams (splitting/merging squads, adding tribes)
- Before deciding whether to hire a VPE separately from CTO (or merge them)
- When production incidents are increasing
- When sprint velocity is dropping but everyone says "we're working hard"

## The Six VPE Questions

### 1. What's the cycle time, and where does work wait?
**No DORA, no diagnosis.**
- Lead Time for Changes is the single best health metric
- If you can't decompose cycle time into stages, you can't fix the bottleneck
- Run `delivery_throughput_analyzer.py`

### 2. What's the DORA performance level on all 4 metrics?
**One Elite metric and three Lows = bad. Four Highs = healthy.**
- Deployment Frequency, Lead Time, MTTR, Change Failure Rate
- The worst metric defines overall level
- Fix lead time first; everything else follows

### 3. Where is the hiring funnel leaking?
**"Can't find good engineers" is wrong.**
- Specific stage is over-filtering OR top-of-funnel volume is too low OR offer-to-accept is broken
- Run `eng_hiring_funnel_calculator.py`
- If offer-to-accept < 70%, comp is below market or close discipline is weak

### 4. Is the team structure healthy for the headcount?
**5-9 ICs per squad; 5-8 ICs per EM; 4-6 EMs per director.**
- Run `eng_team_structure_designer.py`
- Manager-trigger fires when 5+ ICs have no dedicated EM
- Director-trigger fires when 3+ EMs report directly to VPE/CTO

### 5. What's the production discipline maturity?
**Level 1-5; aim for Level 3 at growth stage.**
- On-call rotation ≥ 6 people
- Severity-defined incident response with blameless postmortems
- SLOs on customer-facing services (pair with `engineering/slo-architect/`)
- Continuous deployment OR scheduled — not "usually one, sometimes the other"

### 6. Are we adding a VPE separately, or is CTO doing both?
**If CTO is spending > 50% on management vs strategy, VPE is needed.**
- Or: VPE complement when CTO is co-founder more comfortable with strategy
- VPE owns operating model; CTO owns architecture
- At small scale (< 20 eng), one person can do both

## Workflow

```bash
# 1. Delivery throughput
python ../../../skills/vpe-advisor/scripts/delivery_throughput_analyzer.py sprint_metrics.json

# 2. Hiring funnel
python ../../../skills/vpe-advisor/scripts/eng_hiring_funnel_calculator.py funnel.json

# 3. Team structure
python ../../../skills/vpe-advisor/scripts/eng_team_structure_designer.py team.json
```

## Output Format

```markdown
# VPE Review: <plan>
**Date:** YYYY-MM-DD

## The Decision Being Made
[throughput | hiring | structure | production | VPE-vs-CTO]

## Delivery Throughput (if applicable)
- DORA overall: Elite / High / Medium / Low
- Worst metric: <DF | LT | MTTR | FR>
- Bottleneck: <stage> (X% of cycle time)
- Top fix: <action + owner>

## Hiring Funnel (if applicable)
- End-to-end conversion: X%
- Weakest stage: <stage>
- Pipeline gap: +N candidates needed
- Top fix: <specific action>

## Team Structure (if applicable)
- Recommended: <informal pods / squads / tribes>
- Manager trigger fired: yes/no
- Director trigger fired: yes/no
- Action: <hire EM | hire director | split squad>

## Production Discipline (if applicable)
- Current maturity level: 1-5
- Next practice to add: <specific>
- SLO coverage: X / Y services

## Verdict
🟢 SHIP | 🟡 SHARPEN | 🔴 BLOCK

## Next Steps
[3 concrete actions]
```

## Routing

- `/cs:cto-review` — for architectural causes of throughput problems
- `cs-chro-advisor` agent — for hiring funnel comp/leveling issues
- `/cs:cfo-review` — for cost-per-hire envelope and eng budget
- `/cs:ciso-review` — for production discipline + compliance overlap
- `/cs:decide` — log the verdict
- `/cs:freeze 30` — on multi-year hiring commitments

## Related

- Agent: [`cs-vpe-advisor`](../../agents/cs-vpe-advisor.md)
- Skill: [`vpe-advisor`](../../../skills/vpe-advisor/SKILL.md)
- Adjacent: `../../../../engineering/slo-architect/`, `../../../../engineering/feature-flags-architect/`, `../../../../engineering/chaos-engineering/`

---

**Version:** 1.0.0
