# Error budget policy — `<service-name>`

This policy says what changes when error budget is burned. Without it, the SLO is theater.

## Scope

Applies to: `<list of SLO IDs covered by this policy>`
Owner: `<team-name>`
Review cadence: quarterly
Last reviewed: `<YYYY-MM-DD>`

## States and actions

### State: HEALTHY (>50% budget remaining)

- Normal operation
- Ship features without extra friction
- Run chaos experiments per the standard cadence
- Roll out feature flags per standard plan

### State: CAUTION (25-50% budget remaining)

- Risky changes get extra review (architect or staff sign-off)
- No new chaos experiments outside dedicated windows
- Postpone non-essential migrations
- Daily team check on budget direction

### State: CRITICAL (<25% budget remaining)

- **Deploy freeze** for the affected service: only SLO-improving fixes ship
- All releases require **explicit owner sign-off**
- **Chaos experiments paused**
- **Feature flag rollouts paused** (existing flags continue at current percent)
- Daily standup includes budget status

### State: VIOLATED (budget exhausted, SLO target missed)

- Same-day: stop the bleeding (rollback, kill switch, scale up)
- Within 48 hours: blameless postmortem published
- Within 14 days: at least one follow-up action shipped
- Within 30 days: review whether SLO target/window are still right

## Recovery

After exiting VIOLATED, the service stays in CRITICAL until:
- Burn rate is sustained at <1× over 7 consecutive days, AND
- All postmortem follow-ups are shipped

## Roles

| Role | Responsibility |
|---|---|
| Service owner | Triggers state transitions; communicates to stakeholders |
| On-call | Receives burn-rate alerts; initial triage |
| Engineering manager | Approves deploys during CRITICAL/VIOLATED |
| SRE | Reviews SLO target appropriateness quarterly |

## Exceptions

The deploy freeze can be lifted by:
- Service owner + engineering manager joint approval
- Reason documented (security fix, customer escalation, regulatory)
- Logged for postmortem review

## Reviewing this policy

This policy is reviewed every quarter. Questions to ask:
1. Did we follow the policy when budget burned?
2. Are the thresholds (50% / 25%) right?
3. Are the actions (freeze, sign-off) actually happening?
4. Did the SLO target need to change?

Answers feed into the next quarter's revision.

## Composition references

- `references/composition.md` — how this policy interacts with feature-flags-architect, chaos-engineering, kubernetes-operator
- `references/error_budget.md` — the math behind the thresholds
- `references/slo_principles.md` — Google SRE Workbook canon
