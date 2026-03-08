# ITAM (IT Asset Management)

## Scope

Use this reference for Hardware Asset Management (HAM), Software Asset Management (SAM), stockrooms, consumables, models, contracts, reclaim workflows, and lifecycle automation.

## Plugin and Role Assumptions

Call out whether the customer is using:

- core Asset Management only
- HAM Professional workflows
- SAM Professional reconciliation and optimization
- procurement / contract integrations
- HR-driven offboarding triggers

Common implementation roles include asset admins, stockroom managers, procurement analysts, and SAM managers. Do not assume every environment exposes the same lifecycle choices or entitlement tables.

## Core Tables

| Area | Table |
|------|-------|
| Asset | `alm_asset` |
| Hardware Asset | `alm_hardware` |
| Consumable | `alm_consumable` |
| Software Entitlement | `alm_license` |
| Software Installation | `cmdb_sam_sw_install` |
| Stockroom | `alm_stockroom` |
| Model | `cmdb_model` |
| Contract | `ast_contract` |

## Asset Lifecycle Pattern

Typical hardware lifecycle:

1. Ordered
2. Received
3. In stock
4. Reserved
5. In use
6. In maintenance
7. Retired
8. Disposed

Recommended fields to keep aligned:

- `install_status`
- `substatus`
- `assigned_to`
- `location`
- `stockroom`
- `department`

## Hardware Asset Automation

```javascript
// Business Rule: before update on alm_hardware
(function executeRule(current, previous) {
    if (current.install_status.changesTo('6')) { // In use
        current.setValue('substatus', 'in_service');
    }

    if (current.assigned_to.changes() && !gs.nil(current.getValue('assigned_to'))) {
        current.setValue('stockroom', '');
    }
})(current, previous);
```

## Reclamation Flow Pattern

Use when employees terminate or transfer.

1. Trigger from HR lifecycle event or user deactivation.
2. Look up active `alm_hardware` records for the user.
3. Create reclaim tasks or work orders.
4. Set asset to reserved or pending return.
5. When received, move asset to stockroom and clear assignment.
6. Run post-return checks and retirement logic if needed.

```javascript
// Reclaim assets for a departing employee
var gr = new GlideRecord('alm_hardware');
gr.addQuery('assigned_to', userSysId);
gr.addQuery('install_status', '6'); // In use
gr.query();

while (gr.next()) {
    gr.setValue('substatus', 'pending_return');
    gr.update();
}
```

## Workflow Example: Employee Offboarding

Strong reclaim designs usually include:

1. HR event identifies a transfer or termination date.
2. Flow Designer looks up assigned `alm_hardware`, `alm_consumable`, and recoverable software allocations.
3. Hardware tasks route to stockroom, workplace, or FSM fulfillment.
4. Software reclamation requests route to SAM or app owners.
5. Asset state changes are delayed until equipment is actually returned or verified unavailable.
6. Exceptions are documented when equipment is lost, damaged, or executive-approved for retention.

## Stockroom Transfer Pattern

```javascript
var asset = new GlideRecord('alm_hardware');
if (asset.get(assetSysId)) {
    asset.setValue('assigned_to', '');
    asset.setValue('location', targetLocation);
    asset.setValue('stockroom', targetStockroom);
    asset.setValue('install_status', '2'); // In stock
    asset.update();
}
```

## CMDB and Asset Alignment Pattern

When the asset is linked to a CI, keep the ownership story explicit.

```javascript
var asset = new GlideRecord('alm_hardware');
if (asset.get(assetSysId) && !gs.nil(asset.getValue('ci'))) {
    var ci = new GlideRecord('cmdb_ci');
    if (ci.get(asset.getValue('ci'))) {
        if (!gs.nil(asset.getValue('assigned_to'))) {
            ci.setValue('assigned_to', asset.getValue('assigned_to'));
        }
        if (!gs.nil(asset.getValue('location'))) {
            ci.setValue('location', asset.getValue('location'));
        }
        ci.update();
    }
}
```

Use this only when the customer has agreed that the asset record is an ownership source for the related CI.

## SAM / License Reconciliation

Use SAM data to compare:

- entitlements purchased
- installations discovered
- normalized software models
- publisher/product/version mappings

```javascript
var ga = new GlideAggregate('cmdb_sam_sw_install');
ga.addQuery('discovery_source', 'ServiceNow Discovery');
ga.groupBy('display_name');
ga.addAggregate('COUNT');
ga.query();
while (ga.next()) {
    gs.info(ga.getValue('display_name') + ': ' + ga.getAggregate('COUNT'));
}
```

## Contract and Warranty Checks

```javascript
var asset = new GlideRecord('alm_hardware');
if (asset.get(assetSysId)) {
    var contract = asset.getValue('contract');
    if (!gs.nil(contract)) {
        gs.info('Asset has contract: ' + contract);
    }
}
```

## Reporting Patterns

Useful KPIs:

- assets in use by department
- assets pending return
- warranty expirations in next 30/60/90 days
- unlicensed installs vs. entitlements
- stockroom aging and dead stock

## Troubleshooting

Common failure modes:

- assets move to retired without a corresponding reclaim or disposal step
- stockroom remains populated even after assignment, which usually indicates incomplete lifecycle automation
- the linked CI still shows an old owner because asset and CMDB updates are not synchronized
- software compliance numbers are misleading because discovery is not normalized or installations are stale
- contract or warranty reporting is incomplete because asset records are missing vendor or model relationships

## Testing Guidance

Validate at least these scenarios:

- assign a hardware asset to a user and verify stockroom is cleared
- reclaim an in-use asset and confirm substatus changes without skipping return verification
- transfer an asset to a stockroom and verify assignment, location, and install status remain aligned
- run a SAM aggregation against representative install data and confirm normalized model coverage
- test edge cases for shared devices, lost devices, and executive exceptions

## Best Practices

1. Keep `alm_*` asset records aligned with related CMDB records, but do not assume they are interchangeable.
2. Use lifecycle state transitions consistently; avoid free-form status changes.
3. Drive reclaim and refresh processes from HR, procurement, or contract events.
4. Prefer sys_id-based lookups for stockrooms, models, and users.
5. For SAM, rely on normalization and entitlement models before building custom compliance logic.
