# Field Service Management (FSM)

## Scope

Use this reference for work orders, work order tasks, dispatching, territories, schedules, mobile technician workflows, skills, and parts logistics.

## Plugin and Role Assumptions

Clarify whether the environment uses:

- core FSM work orders only
- schedule optimization or external scheduling tools
- mobile inventory and stockroom extensions
- appointment booking and customer notifications
- offline mobile technician workflows

Typical stakeholders are dispatchers, field technicians, stockroom managers, service coordinators, and platform admins.

## Core Tables

| Area | Table |
|------|-------|
| Work Order | `wm_order` |
| Work Order Task | `wm_task` |
| Dispatch Group | `wm_dispatch_group` |
| Territory | `wm_territory` |
| Agent Schedule | `cmn_schedule` |
| Agent | `sys_user` |
| Skills | `cmn_skill` |
| Required Skill Mapping | `wm_task_required_skill` |

## Work Order Lifecycle

Typical stages:

1. New
2. Ready for dispatch
3. Dispatched
4. Accepted
5. On site / work in progress
6. Completed
7. Closed / cancelled

## Auto-Dispatch Pattern

Inputs commonly used:

- territory
- work type
- required skills
- SLA or appointment window
- technician availability

```javascript
// Before insert/update on wm_task
(function executeRule(current, previous) {
    if (gs.nil(current.getValue('assignment_group')) && !gs.nil(current.getValue('territory'))) {
        var dispatchGroup = new GlideRecord('wm_dispatch_group');
        dispatchGroup.addQuery('territory', current.getValue('territory'));
        dispatchGroup.addActiveQuery();
        dispatchGroup.setLimit(1);
        dispatchGroup.query();
        if (dispatchGroup.next()) {
            current.setValue('assignment_group', dispatchGroup.getUniqueValue());
        }
    }
})(current, previous);
```

## Technician Skill Match

```javascript
var skillGr = new GlideRecord('wm_task_required_skill');
skillGr.addQuery('task', taskSysId);
skillGr.query();

var requiredSkills = [];
while (skillGr.next()) {
    requiredSkills.push(skillGr.getValue('skill'));
}
```

Use those skills together with schedule availability rather than assigning purely by group membership.

## Candidate Dispatch Pattern

When the instance needs a simple fallback selector, start with territory and availability before adding route optimization.

```javascript
var member = new GlideRecord('sys_user_grmember');
member.addQuery('group', dispatchGroupSysId);
member.setLimit(25);
member.query();

while (member.next()) {
    gs.info('Dispatch candidate: ' + member.user.getDisplayValue());
}
```

Use this as a starting point only. Mature dispatch logic usually adds schedule, skill, appointment window, and part readiness checks outside a single Business Rule.

## Scheduling Guidance

When recommending dispatch logic, consider:

- travel time
- customer SLA window
- territory boundaries
- technician schedule and shifts
- required certifications
- parts availability

## Parts and Inventory

Patterns:

1. Reserve parts before dispatch if the job is part-dependent.
2. Link parts consumption to work order tasks, not just the parent order.
3. Keep stockroom and mobile inventory movements auditable.

## Mobile Technician Workflows

Common mobile requirements:

- offline-friendly forms
- required photo capture
- required signatures
- geolocation check-in
- completion checklist

```javascript
// Example completion guard on wm_task
(function executeRule(current, previous) {
    if (current.state.changesTo('3') && gs.nil(current.getValue('close_notes'))) {
        gs.addErrorMessage('Technicians must add completion notes before closing the task.');
        current.setAbortAction(true);
    }
})(current, previous);
```

## Flow Pattern: Dispatch and Notify

1. Trigger on `wm_task` insert or readiness state.
2. Resolve territory and required skills.
3. Look up available technicians.
4. Assign best candidate.
5. Notify technician and customer.
6. Update appointment / ETA.

## Workflow Example: Emergency Dispatch Escalation

For urgent work:

1. Detect a priority work order task with a near-term SLA breach.
2. Verify required parts are available locally or at a nearby stockroom.
3. Check whether any technician in the territory holds the required skills.
4. Escalate to a broader dispatch group if no qualified local technician exists.
5. Notify dispatch and customer when ETA changes.
6. Keep a clear audit trail of manual overrides.

## KPIs

- first-time fix rate
- mean time to dispatch
- mean travel time
- technician utilization
- appointment adherence
- parts-driven reschedules

## Troubleshooting

Common failure modes:

- tasks stay unassigned because territory data is incomplete or dispatch groups are inactive
- technicians receive work they cannot complete because required skills are not maintained
- mobile completion fails due to required notes, photos, or signatures not being captured
- parts-dependent work is dispatched before reservation or transfer is confirmed
- schedule integrations overwrite local assignment changes without dispatcher visibility

## Testing Guidance

Validate at least these scenarios:

- create a task with a territory and confirm the assignment group resolves correctly
- create a task without a territory and verify the fallback path is intentional
- test completion with and without close notes on mobile and desktop
- simulate a missing part and verify dispatch is delayed or rerouted
- test after-hours or overloaded technician schedules to confirm escalation logic

## Best Practices

1. Keep dispatch logic data-driven: territory, skills, and schedule should all be explicit records.
2. Separate parent work order orchestration from task-level execution.
3. Validate mobile completion data before allowing closure.
4. Do not overfit assignment to a single field; use multi-factor selection.
5. When integrating with external scheduling or GPS tools, keep outbound auth in REST Message records and properties.
