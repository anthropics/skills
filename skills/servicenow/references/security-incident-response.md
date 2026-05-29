# Security Incident Response

## Scope

Use this reference for Security Incident Response workflows, security incident states, containment and eradication orchestration, response tasks, forensic handoff, and SOC-driven automation.

## Plugin and Role Assumptions

Clarify whether the environment uses:

- Security Incident Response only or broader SecOps orchestration
- SIEM, EDR, SOAR, threat intel, or case-management integrations
- product-native response tasks or custom task extensions
- forensic evidence workflows or external evidence stores
- manual approval gates before destructive containment actions

Typical stakeholders include SOC analysts, incident commanders, infrastructure responders, IAM teams, and legal or compliance stakeholders for severe events.

## Core Tables

| Area | Table |
|------|-------|
| Security Incident | `sn_si_incident` |
| Security Incident Task / Response Task | environment-specific task extensions depending on implementation |
| Related Risk / Exception / Evidence | depends on IRM and SecOps configuration |
| Indicator / Artifact / Observable | implementation-specific, often tied to integrations and response records |

## Lifecycle Model

Suggested phases:

1. Detection
2. Triage
3. Containment
4. Eradication
5. Recovery
6. Lessons learned / closure

If the customer already has a phase model, preserve it rather than forcing a custom one.

## Phase Transition Guard

```javascript
// Before update on sn_si_incident
(function executeRule(current, previous) {
    if (current.state.changesTo('containment') && gs.nil(current.getValue('assignment_group'))) {
        gs.addErrorMessage('Containment requires an assignment group.');
        current.setAbortAction(true);
        return;
    }

    if (current.state.changesTo('eradication') && gs.nil(current.getValue('work_notes'))) {
        gs.addErrorMessage('Add eradication notes before moving to eradication.');
        current.setAbortAction(true);
    }
})(current, previous);
```

## Containment Workflow Pattern

Typical containment actions:

- isolate endpoint or CI
- disable account or credential
- block IOC at control point
- notify business owners
- create evidence-preservation tasks

Model these as separate actions or response tasks so the incident record remains auditable.

## Response Task Creation

```javascript
var task = new GlideRecord('task');
task.initialize();
task.setValue('parent', securityIncidentSysId);
task.setValue('short_description', 'Collect volatile evidence');
task.setValue('assignment_group', assignmentGroupSysId);
task.insert();
```

## Severity Routing Pattern

Make severity-based ownership transparent.

```javascript
// Before insert on sn_si_incident
(function executeRule(current, previous) {
    if (current.getValue('priority') == '1' && gs.nil(current.getValue('assignment_group'))) {
        current.setValue('assignment_group', highSeverityGroupSysId);
    }
})(current, previous);
```

Document the fallback order if routing changes by geography, service owner, or incident type.

## Forensic Handoff

Capture:

- time of acquisition
- custodian or owner
- system or artifact source
- chain-of-custody notes
- approval or legal hold requirements

## Workflow Example: Destructive Containment Approval

For actions like disabling accounts or isolating endpoints:

1. triage confirms the incident is active and severe enough to justify containment
2. a response task captures the proposed action, target, and rollback path
3. a human approver or incident commander authorizes the action
4. the integration executes the action and records upstream identifiers
5. the incident and task capture notes, actor attribution, and timestamps
6. recovery includes validation that the action can be safely reversed

## Integration Guidance

When integrating with EDR, SIEM, SOAR, or case tools:

1. define source of truth for status
2. preserve external IDs
3. make retries idempotent
4. map severity and priority explicitly
5. separate detection events from response actions

## Metrics

- mean time to triage
- mean time to contain
- mean time to recover
- incidents by severity and vector
- open incidents without owner
- response tasks past due

## Troubleshooting

Common failure modes:

- incidents move into containment without an owner because routing depends on incomplete severity mappings
- response tasks are created but not linked cleanly to the parent incident or external action
- destructive integrations run without clear approval or rollback evidence
- recovery is marked complete while related tasks or evidence collection remain open
- SIEM or SOAR connectors overwrite local notes, actor attribution, or severity without governance

## Testing Guidance

Validate at least these scenarios:

- block a transition to containment when assignment is missing
- block a transition to eradication when required notes are missing
- create a high-severity incident and confirm routing sends it to the correct group
- simulate a destructive containment action and verify approval, execution, and rollback evidence
- test duplicate inbound detection events and confirm idempotent linking rather than duplicate cases

## Best Practices

1. Phase ownership should be explicit. Containment, eradication, and recovery often belong to different teams.
2. Use tasks or flows for operational work; keep the parent incident focused on governance and case state.
3. Preserve evidence and approval trails for high-severity incidents.
4. Avoid silent state transitions from integrations without notes, actor attribution, and external ID traceability.
5. If proposing automation, explain the rollback and human-approval gates for destructive containment actions.
