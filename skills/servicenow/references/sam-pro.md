# SAM Pro

## Scope

Use this reference for Software Asset Management Professional workflows: normalization, software models, publishers, entitlements, installations, reclamation candidates, and license compliance analysis.

## Plugin and Role Assumptions

Clarify whether the environment uses:

- SAM Professional normalization and reconciliation
- usage metering for reclaim decisions
- publisher packs or custom normalization rules
- device, user, subscription, or core-based metrics
- procurement and contract integrations for entitlement sourcing

Typical stakeholders are SAM analysts, procurement teams, software owners, and platform admins supporting discovery quality.

## Core Tables

| Area | Table |
|------|-------|
| Software Entitlement | `alm_license` |
| Software Installation | `cmdb_sam_sw_install` |
| Software Model | `cmdb_software_product_model` |
| Discovery Model / Normalization Links | implementation-specific SAM tables |
| User Subscription / Allocation | depends on license metric and integration model |

## Core Concepts

Important distinctions:

- install data is not entitlement data
- normalized software is not the same as raw discovery strings
- publishers, products, versions, and editions matter
- reclaimable software depends on usage, allocation model, and business policy

## Installation Aggregation

```javascript
var ga = new GlideAggregate('cmdb_sam_sw_install');
ga.addQuery('active', true);
ga.groupBy('display_name');
ga.addAggregate('COUNT');
ga.query();

while (ga.next()) {
    gs.info(ga.getValue('display_name') + ': ' + ga.getAggregate('COUNT'));
}
```

## Entitlement Lookup Pattern

```javascript
var ent = new GlideRecord('alm_license');
ent.addQuery('active', true);
ent.addQuery('software_model', softwareModelSysId);
ent.query();

while (ent.next()) {
    gs.info(ent.getValue('number') + ' metric=' + ent.getValue('license_metric'));
}
```

## Effective License Position Check

Keep compliance math reviewable and model-specific.

```javascript
var installs = new GlideAggregate('cmdb_sam_sw_install');
installs.addQuery('active', true);
installs.addQuery('software_model', softwareModelSysId);
installs.addAggregate('COUNT');
installs.query();

if (installs.next()) {
    gs.info('Install count for model ' + softwareModelSysId + ': ' + installs.getAggregate('COUNT'));
}
```

Use the output only as one input. Actual license position still depends on metric, rights, bundles, downgrade rules, and allocation model.

## Reclamation Candidate Pattern

Use reclamation only when the organization has a clear policy for inactivity windows and approval.

```javascript
var install = new GlideRecord('cmdb_sam_sw_install');
install.addQuery('last_used', '<', gs.daysAgoStart(90));
install.addQuery('active', true);
install.setLimit(100);
install.query();

while (install.next()) {
    gs.info('Potential reclaim candidate: ' + install.getValue('display_name'));
}
```

## Normalization Guidance

Before giving compliance recommendations, call out:

- whether software discovery is normalized
- whether the publisher, product, and version mappings are trusted
- whether the customer uses device, user, core, or subscription metrics

If normalization confidence is poor, fix that first instead of pretending the compliance result is definitive.

## Workflow Example: Publisher Review Cycle

1. ingest discovery and usage data
2. normalize raw installs to software models
3. compare installed footprint to entitlement coverage
4. identify reclaim candidates and true deficits separately
5. route deficits to procurement and reclaims to software owners
6. confirm reclaimed installs or new purchases before updating compliance posture

## Practical Workflow

1. ingest discovery and usage data
2. normalize to software models
3. map installations to entitlements
4. identify surplus, deficit, and reclaim candidates
5. route actions to owners or procurement
6. verify remediation or reclaim completion

## Metrics

- effective license position by publisher
- reclaim candidates by inactivity window
- unnormalized software backlog
- top publishers by spend exposure
- installs without mapped entitlements

## Troubleshooting

Common failure modes:

- compliance numbers shift unexpectedly because normalization rules or publisher mappings changed
- reclaim candidates are invalid because usage signals are stale or not collected consistently
- license deficits are overstated because bundles, downgrade rights, or alternative entitlements are ignored
- discovery shows installs that should be retired because device or user decommission processes lag
- procurement records exist but are not linked cleanly to entitlement records

## Testing Guidance

Validate at least these scenarios:

- aggregate installs for a normalized software model and confirm counts match known sample data
- look up entitlements for a model with more than one license metric
- test reclamation windows for 30, 60, and 90 day inactivity rules
- simulate incomplete normalization and confirm the workflow flags the data-quality blocker
- verify purchase-linked entitlement records appear in the expected compliance workflow

## Best Practices

1. Never infer compliance from raw install counts alone.
2. Explain the license metric whenever recommending entitlement math.
3. Keep reclamation decisions reviewable and reversible.
4. Use software models and normalized data as the operating layer for automation.
5. Call out data-quality blockers, especially around publishers, versions, and inactive install signals.
