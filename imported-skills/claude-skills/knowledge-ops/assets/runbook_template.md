# Runbook Template — fill out before running `runbook_validator.py`

Use this template to capture runbook steps before invoking the validator.
Each step must specify all six required attributes (owner, duration,
success signal, failure signal, rollback, escalation) or the validator
will flag it.

Feed the JSON into:

```
python3 scripts/runbook_validator.py --input my-runbook.json
python3 scripts/runbook_validator.py --input my-runbook.md   # markdown also accepted
```

A runbook scoring < 60 is NOT-SAFE for production use. Aim for ≥ 80
(SAFE-TO-USE) before putting the runbook into rotation.

---

## Runbook metadata

- **Runbook name:** _(e.g., Incident Comms Cascade, Customer Escalation, Vendor Outage Response, System-Access Revocation)_
- **Owner:** _(named human or named on-call rotation — e.g., "Incident Commander on-call (PagerDuty: ic-primary)")_
- **Trigger:** _(what specifically invokes this runbook — e.g., "PagerDuty Sev-1 incident triggered" or "Customer escalation flagged in Salesforce")_
- **Expected total duration:** _(P50 + P90 wall-clock from trigger to completion)_
- **Linked SOP:** _(if this runbook implements an SOP, link the canonical SOP page)_

---

## Step table

| # | Step title | Owner | Duration | Success signal (observable) | Failure signal (observable) | Rollback | Escalation |
|---|------------|-------|----------|------------------------------|------------------------------|----------|------------|
| 1 | _e.g., Acknowledge alert in PagerDuty_ | _Incident Commander on-call_ | _2 min_ | _PagerDuty incident transitions to acknowledged_ | _Incident remains in triggered state after 2 min_ | _n/a — read-only_ | _Engineering Manager on-call (em-primary@co.com)_ |
| 2 | _e.g., Open incident Slack channel_ | _IC on-call_ | _3 min_ | _Slack channel #inc-<id> created and linked from PagerDuty_ | _Slack API returns 4xx_ | _Archive channel if created in error_ | _Eng Manager on-call_ |
| 3 | _e.g., Notify execs via paging tree_ | _Comms Lead (comms-lead@co.com)_ | _5 min_ | _SES API returns 200 for all exec recipients_ | _SES API returns 5xx OR delivery=bounced_ | _Send retraction email with subject prefix 'RETRACTION:'_ | _VP Communications_ |

---

## JSON skeleton

```json
{
  "runbook_name": "Incident Comms Cascade",
  "steps": [
    {
      "title": "Acknowledge alert in PagerDuty",
      "owner": "Incident Commander on-call (PagerDuty: ic-primary)",
      "duration_str": "2 minutes",
      "duration_minutes": 2,
      "success_signal": "PagerDuty incident transitions to acknowledged",
      "failure_signal": "Incident remains in triggered state after 2 minutes",
      "rollback": "n/a — acknowledgement is non-mutating, read-only operation",
      "escalation": "Engineering Manager on-call (em-primary@company.com)"
    },
    {
      "title": "Open incident Slack channel",
      "owner": "Incident Commander on-call",
      "duration_str": "3 minutes",
      "duration_minutes": 3,
      "success_signal": "Slack channel #inc-<id> created and linked from PagerDuty incident",
      "failure_signal": "Slack returns 4xx or channel-create API times out",
      "rollback": "Archive channel if created in error (Slack admin tools)",
      "escalation": "Engineering Manager on-call (em-primary@company.com)"
    },
    {
      "title": "Notify execs via paging tree",
      "owner": "Communications Lead (comms-lead@company.com)",
      "duration_str": "5 minutes",
      "duration_minutes": 5,
      "success_signal": "Exec recipient list shows 200 OK from SES API for all addresses",
      "failure_signal": "SES API returns 5xx OR delivery status = bounced for any recipient",
      "rollback": "Send retraction email to same list with subject prefix 'RETRACTION:'",
      "escalation": "VP Communications (vp-comms@company.com)"
    }
  ]
}
```

---

## Markdown form (alternative — runbook_validator.py heuristic parser)

If you prefer authoring in markdown directly, follow this exact structure (the parser keys off `## Step N:` headings and bullet attributes):

```markdown
# Runbook: Incident Comms Cascade

## Step 1: Acknowledge alert in PagerDuty

- **Owner:** Incident Commander on-call (PagerDuty: ic-primary)
- **Duration:** 2 minutes
- **Success:** PagerDuty incident transitions to acknowledged
- **Failure:** Incident remains in triggered state after 2 minutes
- **Rollback:** n/a — non-mutating, read-only
- **Escalation:** Engineering Manager on-call (em-primary@company.com)

## Step 2: Open incident Slack channel

- **Owner:** ...
```

---

## Authoring discipline checklist

Before submitting the runbook to the validator:

- [ ] **Every step has a named owner**, not "the team" or "ops" — required by SRE Workbook Ch. 8.
- [ ] **Every step has a concrete duration** (number + unit). "Quick" is not a duration.
- [ ] **Every success signal is observable** — a yes/no check the operator can perform. "HTTP 200 from /healthz", not "service is up".
- [ ] **Every failure signal is observable** — what tells you the step did NOT work.
- [ ] **Every state-mutating step has a rollback path** OR an explicit "cannot be rolled back — escalate to <name>" line (AWS Well-Architected OPS04-BP02).
- [ ] **Every step has an escalation contact** — named human, role+email, or named on-call rotation.
- [ ] **Top-2 failure modes documented** (Fowler 2016) — most common ways this runbook gets stuck, each with their own recovery sub-procedure.
- [ ] **Last-reviewed date set in frontmatter** — runbooks decay; Charity Majors's data: untouched 12-month-old runbooks are wrong 60% of the time.

After validation, place the runbook in the canonical wiki location and link it from at least 2 navigation hubs (incident-handbook, the parent SOP) to avoid orphan-page status.
