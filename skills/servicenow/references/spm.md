# Strategic Portfolio Management (SPM / PPM)

## Scope

Use this reference for demand management, project and portfolio management, resource plans, investment governance, roadmaps, and Agile 2.0 portfolio patterns.

## Plugin and Role Assumptions

Clarify whether the environment uses:

- classic PPM only
- Strategic Portfolio Management with investment funding and benefit tracking
- Agile 2.0 or hybrid delivery
- Resource Management with named or role-based plans
- custom PMO approval boards or stage-gate governance

The main stakeholders are PMO analysts, portfolio managers, project managers, resource managers, and finance partners.

## Core Tables

| Area | Table |
|------|-------|
| Demand | `dmn_demand` |
| Project | `pm_project` |
| Project Task | `pm_project_task` |
| Portfolio | `pm_portfolio` |
| Program | `pm_program` |
| Resource Plan | `resource_plan` |
| Benefit Plan | `pm_project_benefit` |
| Investment Funding | `fm_funding_allocation` |

## Demand to Project Lifecycle

Common path:

1. Demand intake
2. Qualification
3. Prioritization
4. Approval
5. Project creation
6. Resource planning
7. Execution and benefit tracking

## Project Creation Pattern

```javascript
// Convert approved demand into a project
var demand = new GlideRecord('dmn_demand');
if (demand.get(demandSysId) && demand.getValue('state') == 'approved') {
    var project = new GlideRecord('pm_project');
    project.initialize();
    project.setValue('short_description', demand.getValue('short_description'));
    project.setValue('description', demand.getValue('description'));
    project.setValue('portfolio', demand.getValue('portfolio'));
    project.setValue('business_case', demand.getUniqueValue());
    project.insert();
}
```

## Approval Guard Pattern

If approval requires a portfolio and an owner, block promotion before the demand leaves intake.

```javascript
// Before update on dmn_demand
(function executeRule(current, previous) {
    if (current.state.changesTo('approved')) {
        if (gs.nil(current.getValue('portfolio')) || gs.nil(current.getValue('owner'))) {
            gs.addErrorMessage('Approved demands must have a portfolio and owner.');
            current.setAbortAction(true);
        }
    }
})(current, previous);
```

## Resource Planning

Track:

- requested role or named resource
- start and end dates
- capacity
- allocation percent or hours
- portfolio/program alignment

```javascript
var plan = new GlideRecord('resource_plan');
plan.initialize();
plan.setValue('task', projectSysId);
plan.setValue('resource_type', 'role');
plan.setValue('planned_hours', '80');
plan.setValue('start_date', startDate);
plan.setValue('end_date', endDate);
plan.insert();
```

## Portfolio Governance

Useful approval inputs:

- strategic alignment
- expected benefit
- delivery risk
- compliance or regulatory pressure
- available capacity
- funding status

Decision tables work well for consistent scoring and routing.

## Workflow Example: Demand Review Board

1. a new demand enters intake with a sponsor, portfolio, and business value statement
2. qualification checks confirm completeness, dependencies, and rough order of magnitude
3. a governance board scores the demand using strategic alignment, urgency, and risk inputs
4. approved work creates a project, program entry, or agile epic path depending on delivery model
5. resource plans and funding allocations are created before execution starts
6. benefits are reviewed after go-live instead of stopping at delivery closeout

## Benefit Tracking

Do not stop at project closure. Strong SPM guidance includes:

- expected vs actual benefit review
- funding variance
- schedule variance
- milestone health
- portfolio-level rollups

## Agile 2.0 / Hybrid Delivery Notes

SPM often spans project and agile data. When designing solutions:

- keep portfolio and product planning aligned
- clarify source of truth for delivery state
- avoid duplicate milestone tracking
- define when work stays in agile records vs project tasks

## Reporting KPIs

- demand throughput
- approval lead time
- projects by health
- budget variance
- benefit realization
- resource over-allocation
- portfolio risk exposure

## Troubleshooting

Common failure modes:

- approved demands create projects with missing portfolio or owner data
- resource plans do not reflect actual execution dates because plan creation is disconnected from governance milestones
- benefit reporting stops at project closure and never compares expected vs actual value
- hybrid delivery models duplicate progress across agile work and project tasks
- funding approvals live outside SPM and leave the record state out of sync with actual governance

## Testing Guidance

Validate at least these scenarios:

- approve a complete demand and confirm project creation includes the right portfolio and business-case linkage
- attempt approval without a portfolio or owner and verify the transition is blocked
- create resource plans for role-based and named-resource models
- test a rejected demand, a deferred demand, and a multi-stage approval path
- verify benefit review reminders still trigger after project closure

## Best Practices

1. Separate intake, governance, and execution records clearly.
2. Use reference relationships between demand, project, portfolio, and funding data rather than copying values blindly.
3. Resource planning logic should be transparent and reviewable by PMO stakeholders.
4. When generating automations, specify which approvals happen in Flow Designer vs native SPM workflow.
5. Include reporting and audit expectations whenever a solution changes demand or project state automatically.
