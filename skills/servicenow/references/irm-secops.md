# IRM, GRC, and SecOps

## Scope

Use this reference for Integrated Risk Management (IRM/GRC), policy and compliance workflows, vendor risk, Security Incident Response, Vulnerability Response, and exception handling.

## Plugin and Role Assumptions

Clarify which product families are active:

- IRM / Policy and Compliance
- Vendor Risk Management
- Vulnerability Response
- Security Incident Response
- exception workflows tied to risks or custom waiver tables

Also call out whether the instance routes governance through Flow Designer, classic workflow, decision tables, or product-native lifecycles.

## Core Tables

| Area | Table |
|------|-------|
| Risk | `sn_risk_risk` |
| Control | `sn_compliance_control` |
| Policy | `sn_compliance_policy` |
| Compliance Task | `sn_compliance_task` |
| Vendor Risk Assessment | `sn_vdr_risk_assessment` |
| Security Incident | `sn_si_incident` |
| Vulnerable Item | `sn_vul_vulnerable_item` |
| Vulnerability Group | `sn_vul_group` |

## Risk and Compliance Pattern

```javascript
// Example: create follow-up compliance task when control fails
var task = new GlideRecord('sn_compliance_task');
task.initialize();
task.setValue('short_description', 'Control remediation required');
task.setValue('assigned_to', ownerSysId);
task.setValue('state', '1');
task.insert();
```

Use controls, risks, and issues as distinct records. Do not collapse them into one custom table unless there is a very strong product reason.

## Control Failure Routing Pattern

Use a transparent owner lookup and due-date rule rather than hardcoded branching.

```javascript
var control = new GlideRecord('sn_compliance_control');
if (control.get(controlSysId)) {
    var dueDate = new GlideDateTime();
    dueDate.addDaysLocalTime(14);

    var task = new GlideRecord('sn_compliance_task');
    task.initialize();
    task.setValue('short_description', 'Remediate failed control: ' + control.getDisplayValue());
    task.setValue('assigned_to', control.getValue('owner'));
    task.setValue('due_date', dueDate);
    task.insert();
}
```

## Policy Exception Workflow

Suggested flow:

1. intake request for exception
2. link the affected policy, control, or risk
3. require compensating control evidence
4. route to risk or security approvers
5. set expiry date and review cadence
6. track renewal or closure

## Vulnerability Response Pattern

```javascript
var gr = new GlideRecord('sn_vul_vulnerable_item');
gr.addQuery('state', 'open');
gr.addQuery('assignment_group', assignmentGroupSysId);
gr.setLimit(50);
gr.query();

while (gr.next()) {
    gs.info(gr.getValue('number') + ' ' + gr.getValue('risk_rating'));
}
```

When automating vulnerability triage, call out:

- source scanner
- CI mapping confidence
- exception process
- remediation SLA
- ownership model

## Security Incident Response

Typical lifecycle:

1. Detection
2. Triage
3. Containment
4. Eradication
5. Recovery
6. Lessons learned / closure

```javascript
// Before update on sn_si_incident
(function executeRule(current, previous) {
    if (current.state.changesTo('containment') && gs.nil(current.getValue('assignment_group'))) {
        gs.addErrorMessage('Security incidents entering containment must have an assignment group.');
        current.setAbortAction(true);
    }
})(current, previous);
```

## Vendor Risk

Key patterns:

- assess vendors periodically and on major changes
- track inheritable controls and evidence separately
- keep scoring logic explicit and reviewable
- store approval history for audit

## Workflow Example: Exception Review Board

For mature governance programs:

1. a request references a policy, vulnerable item, or risk record
2. the requester provides rationale, business impact, compensating controls, and expiry date
3. Flow Designer routes to the right risk, compliance, or security approver
4. approved exceptions create review reminders before expiry
5. rejected exceptions return to the requester with required remediation actions
6. all approvals and renewals stay linked to the original record for audit

## Exception and Waiver Guidance

Never hardcode approval routes or risk thresholds in source code when they vary by environment. Prefer:

- properties
- decision tables
- flow inputs
- reference-data tables

## Reporting KPIs

- open high risks by domain
- failed controls by framework
- overdue remediation tasks
- vulnerabilities past SLA
- security incidents by severity and mean time to contain
- exception inventory with expiry dates

## Troubleshooting

Common failure modes:

- remediation tasks route to nobody because control ownership is incomplete
- exceptions appear approved but have no expiry or review cadence
- vulnerability items cannot be actioned because CI ownership is missing or scanner connectors are stale
- vendor risk scores drift because scoring logic lives in undocumented scripts instead of controlled rules
- security incidents move phases without notes, evidence, or clear actor attribution

## Testing Guidance

Validate at least these scenarios:

- fail a control and confirm the right remediation task is created with an owner and due date
- submit an exception request with and without compensating controls
- route a vulnerable item with missing CI ownership and confirm the fallback path
- test security incident phase transitions that should block on missing assignment or notes
- verify auditability for approvals, renewals, closures, and rejected requests

## Best Practices

1. Keep auditability first-class: approvals, expiries, rationale, and evidence should all be retrievable.
2. Prefer table relationships over duplicating policy or control data into task records.
3. Use Flow Designer or decision tables for governance-heavy routing where admins need visibility.
4. For Vulnerability Response, distinguish exceptions, accepted risk, and false positives clearly.
5. Security automations should always document plugin assumptions and required roles.
