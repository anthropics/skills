# Capacity Planning Brief — {{TEAM_NAME}}

> 20-minute fill-out. Bring this brief plus your last 90 days of ticket /
> case / work-item data and you have everything needed to produce a
> defensible Q+1 plan.

## Section 1 — Context (5 minutes)

- **Team name:** {{TEAM_NAME}}
- **Function:** [support / cx / bizops / finance-ops / it-ops]
- **Planning horizon:** [Q+1 / annual / 12-month rolling]
- **Current headcount:** {{CURRENT_FTE}}
- **Working hours/day:** {{WORKING_HOURS_PER_DAY}}
- **Top business event driving this plan:** _(growth target, peak season,
  M&A integration, regulatory change, etc.)_

## Section 2 — Demand (5 minutes)

Pull from your ticketing system (Zendesk, Intercom, Jira Service
Management, Salesforce, ServiceNow, etc.) the daily volume for the last
90 days. Compute or read off:

- **P50 (median day):** {{P50_TICKETS_PER_DAY}}
- **P90 (peak-band day):** {{P90_TICKETS_PER_DAY}}
- **P99 (annual peak day):** {{P99_TICKETS_PER_DAY}}

> If you only have averages, this plan is built on sand. Pull the
> distribution. (Anti-pattern #5: size-to-P50-only.)

- **Average handle time (AHT, minutes):** {{AHT_MINUTES}}
- **SLA target (minutes to first response or resolution):** {{SLA_MINUTES}}
- **Channels in scope:** _(voice / email / chat / async / multi)_
- **Multi-channel premium expected:** [yes / no — if multi, add 15-25%]

## Section 3 — People Realities (5 minutes)

- **Shrinkage % (paid time NOT productive):** {{SHRINKAGE_PCT}}
  _(default if unknown: support 30, cx 32, bizops 25, finance-ops 22, it-ops 28)_
- **Ramp time for new hire (weeks to full productivity):** {{RAMP_WEEKS}}
  _(default: support 8, cx 10, bizops 12, finance-ops 14, it-ops 10)_
- **Annual attrition observed last 12 months:** {{ATTRITION_PCT}}
  _(default: support 30, cx 28, bizops 18, finance-ops 15, it-ops 20)_
- **Max hires per quarter (recruiting + onboarding constraint):**
  {{MAX_HIRES_PER_QUARTER}}
- **Current managers and span of control:** _(list manager names + their
  direct-report counts)_

## Section 4 — Strategic Constraints (5 minutes)

- **QoQ demand growth assumption:** {{GROWTH_QOQ_PCT}}
- **Bottleneck identified upstream (via process-mapper or similar):**
  _(if you don't know your bottleneck, run process-mapper FIRST — sizing
  around the wrong constraint is wasted hires)_
- **Service trade-off accepted:** _(per Frances Frei — pick which
  attributes to win: speed / empathy / breadth / cost)_
- **Surge plan for P99 events:** _(overflow tier? BPO? on-call?
  documented degradation?)_

---

## Tool Inputs

### Input JSON for `capacity_modeler.py`

```json
{
  "team_name": "{{TEAM_NAME}}",
  "demand": {
    "tickets_per_day_p50": {{P50_TICKETS_PER_DAY}},
    "tickets_per_day_p90": {{P90_TICKETS_PER_DAY}},
    "tickets_per_day_p99": {{P99_TICKETS_PER_DAY}}
  },
  "sla_target_minutes": {{SLA_MINUTES}},
  "current_fte": {{CURRENT_FTE}},
  "avg_handle_time_minutes": {{AHT_MINUTES}},
  "shrinkage_pct": {{SHRINKAGE_PCT}},
  "working_hours_per_day": {{WORKING_HOURS_PER_DAY}}
}
```

Run:

```bash
python3 scripts/capacity_modeler.py --input my_brief.json --profile support
```

### Input JSON for `utilization_analyzer.py`

```json
{
  "team_members": [
    {
      "name": "<name>",
      "role": "<role>",
      "utilization_pct": <0-100>,
      "handles_count": <int>,
      "hours_billable": <float>,
      "hours_capacity": <float>
    }
  ]
}
```

Run:

```bash
python3 scripts/utilization_analyzer.py --input team_util.json
```

### Input JSON for `hiring_sequencer.py`

```json
{
  "team_name": "{{TEAM_NAME}}",
  "current_fte": {{CURRENT_FTE}},
  "target_fte_end_of_year": {{TARGET_EOY_FTE}},
  "ramp_time_weeks": {{RAMP_WEEKS}},
  "attrition_rate_annual_pct": {{ATTRITION_PCT}},
  "growth_assumption_qoq_pct": {{GROWTH_QOQ_PCT}},
  "hiring_constraints": {
    "max_hires_per_quarter": {{MAX_HIRES_PER_QUARTER}}
  }
}
```

Run:

```bash
python3 scripts/hiring_sequencer.py --input my_brief.json --profile support
```

---

## Output Checklist

After running all three tools, you should have:

- [ ] **Erlang-C sizing**: required FTE at 70/80/90% utilization (size to 80%)
- [ ] **Headroom %**: extra demand tolerable before SLA breaks (target >20%)
- [ ] **Risk band**: SAFE / WATCH / AT_RISK / CRITICAL
- [ ] **Team health verdict**: HEALTHY / SQUEEZED / OVERLOADED / UNBALANCED
- [ ] **Quarterly hiring plan**: ICs + managers + expected attrition per quarter
- [ ] **Manager-trigger callouts**: which quarter you add a manager
- [ ] **Warnings**: any quarter where hiring constraint blocks your plan
- [ ] **Forcing-question answers**: documented decisions on bottleneck,
  service trade-offs, surge plan, P99 strategy (see SKILL.md
  *Forcing-question library*)

## Sign-off

- **Prepared by:** ______________
- **Reviewed by (finance + HR + CS leader):** ______________
- **Decision and date:** ______________
- **Re-test trigger:** _(quarterly review date or demand-level threshold
  that forces re-run)_
