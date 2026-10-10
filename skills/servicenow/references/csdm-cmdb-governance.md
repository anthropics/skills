# CSDM and CMDB Governance

## Scope

Use this reference for Common Service Data Model (CSDM), CMDB governance, service taxonomy, ownership, relationships, health, and lifecycle validation.

## Plugin and Role Assumptions

Clarify whether the environment uses:

- Discovery, Service Mapping, or manual CMDB stewardship only
- greenfield CSDM adoption or remediation of a legacy CMDB
- class manager or attestation processes
- service portfolio governance outside or inside ServiceNow
- custom CI classes that must be rationalized over time

Typical stakeholders are CMDB managers, service owners, application owners, discovery teams, and architecture governance boards.

## Core Concepts

CSDM separates concepts that organizations often blur together:

- business application
- application service
- business service
- service offering
- technical service
- supporting CI classes

Preserve those distinctions when designing data models or migrations.

## Key Tables

| Concept | Table |
|---------|-------|
| Base CI | `cmdb_ci` |
| Business Application | `cmdb_ci_business_app` |
| Business Service | `cmdb_ci_service` |
| Application Service | `cmdb_ci_service_auto` |
| Service Offering | `service_offering` |
| Relationship | `cmdb_rel_ci` |

## Ownership and Accountability

Minimum governance fields usually include:

- owned_by
- support_group
- assignment_group
- business_owner
- technical_owner
- operational status or install status

## Relationship Query Pattern

```javascript
var rel = new GlideRecord('cmdb_rel_ci');
rel.addQuery('parent', parentSysId);
rel.query();

while (rel.next()) {
    gs.info(rel.getValue('parent') + ' -> ' + rel.getValue('child') + ' [' + rel.getValue('type') + ']');
}
```

## Missing Ownership Check

```javascript
var gr = new GlideRecord('cmdb_ci_service');
gr.addQuery('owned_by', '');
gr.setLimit(100);
gr.query();

while (gr.next()) {
    gs.info('Missing owner: ' + gr.getValue('name'));
}
```

## Service Offering Integrity Check

Service offerings should not exist without the service context they represent.

```javascript
var offering = new GlideRecord('service_offering');
offering.addNullQuery('parent');
offering.setLimit(100);
offering.query();

while (offering.next()) {
    gs.info('Service offering missing parent service: ' + offering.getDisplayValue());
}
```

## Governance Patterns

Strong CMDB governance usually includes:

1. class-specific required fields
2. ownership controls
3. relationship minimums
4. stale CI review
5. duplicate detection
6. intake rules for new services

## Guided Intake Workflow

For new business services or application services:

1. requestor submits purpose, owner, support group, and dependency context
2. validation checks confirm the right CI class and required fields
3. approval confirms the record fits the service taxonomy
4. follow-up tasks enforce relationship creation and data stewardship
5. ongoing health checks flag missing owners, stale services, and broken relationships

## CSDM Mapping Guidance

When helping users map data:

- map portfolio or product concepts carefully to business applications, not directly to every service layer
- use business services for customer-facing or business-consumable capabilities
- use application services for deployable or runtime service endpoints
- use service offerings when a service has distinct consumer-facing variants

## Health Metrics

- completeness
- compliance
- correctness
- relationship health
- staleness
- orphaned services without owners or supporting CIs

## Troubleshooting

Common failure modes:

- services are modeled at the wrong layer because application services and business services are treated as synonyms
- ownership fields exist but are not populated consistently across classes
- service offerings are created without a parent service or clear consumer meaning
- discovery populates infrastructure CIs but service relationships remain manual and incomplete
- duplicate services survive because intake and remediation rules are advisory instead of enforced

## Testing Guidance

Validate at least these scenarios:

- create a service record through guided intake and confirm required fields are enforced
- query for missing owners and confirm the exception list is actionable
- create a service offering with and without a parent service and verify the health check catches the bad case
- test relationship validation for a business service, application service, and supporting CI chain
- run stewardship checks against stale services and duplicate candidates

## Best Practices

1. Do not create custom CI classes or relationships when an out-of-box CSDM pattern already fits.
2. Keep ownership explicit and queryable.
3. Treat service taxonomy as governance, not just naming.
4. Call out whether the customer is doing greenfield modeling or remediation of an existing CMDB.
5. For automation, prefer validations and guided intake over free-form CI creation.
