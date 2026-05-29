# ServiceNow Scripting Patterns

## Business Rules

### When to Use Which Type

| Type | Fires | Use For |
|------|-------|---------|
| **Before** | Before DB write | Validation, field defaults, calculated fields, abort with `current.setAbortAction(true)` |
| **After** | After DB write | Creating related records, notifications, events, anything needing sys_id |
| **Async** | After, in background | Heavy processing, integrations, anything slow. Does NOT block user. |
| **Display** | Before form loads | Populating `g_scratchpad` for client scripts |

### Before Business Rule — Set defaults, validate
```javascript
// Name: Set Priority from Impact/Urgency
// Table: incident | When: before | Insert: true | Update: true
// Condition: current.impact.changes() || current.urgency.changes()

(function executeRule(current, previous) {
    var impact = parseInt(current.getValue('impact'));
    var urgency = parseInt(current.getValue('urgency'));
    
    // Priority matrix
    var priorityMap = {
        '1-1': '1', '1-2': '2', '1-3': '3',
        '2-1': '2', '2-2': '3', '2-3': '4',
        '3-1': '3', '3-2': '4', '3-3': '5'
    };
    
    var key = impact + '-' + urgency;
    current.setValue('priority', priorityMap[key] || '4');
})(current, previous);
```

### Before Business Rule — Validation with abort
```javascript
// Name: Validate Resolution
// Table: incident | When: before | Update: true
// Condition: current.state.changesTo('6')

(function executeRule(current, previous) {
    if (gs.nil(current.getValue('close_code'))) {
        current.setAbortAction(true);
        gs.addErrorMessage('Close code is required when resolving an incident.');
        return;
    }
    if (gs.nil(current.getValue('close_notes'))) {
        current.setAbortAction(true);
        gs.addErrorMessage('Close notes are required when resolving an incident.');
    }
})(current, previous);
```

### After Business Rule — Create related record
```javascript
// Name: Create Problem from Major Incident
// Table: incident | When: after | Update: true
// Condition: current.priority == '1' && current.state.changesTo('6') && !current.problem_id

(function executeRule(current, previous) {
    var prob = new GlideRecord('problem');
    prob.initialize();
    prob.setValue('short_description', 'Problem from ' + current.getValue('number'));
    prob.setValue('description', current.getValue('description'));
    prob.setValue('category', current.getValue('category'));
    prob.setValue('assignment_group', current.getValue('assignment_group'));
    var probId = prob.insert();
    
    // Link back — use workflow false to avoid recursion
    current.setValue('problem_id', probId);
    current.setWorkflow(false);
    current.update();
})(current, previous);
```

### Async Business Rule — Heavy processing
```javascript
// Name: Sync to External System
// Table: incident | When: async | Insert: true | Update: true
// Condition: current.assignment_group.name == 'External Team'

(function executeRule(current, previous) {
    try {
        var rm = new sn_ws.RESTMessageV2('External System', 'POST');
        rm.setStringParameterNoEscape('incident_number', current.getValue('number'));
        rm.setStringParameterNoEscape('description', current.getValue('short_description'));
        var response = rm.execute();
        var statusCode = response.getStatusCode();
        
        if (statusCode != 200 && statusCode != 201) {
            gs.error('External sync failed for ' + current.getValue('number') + ': ' + statusCode);
        }
    } catch(e) {
        gs.error('External sync exception: ' + e.message);
    }
})(current, previous);
```

### Display Business Rule — Pass data to client
```javascript
// Name: Pass User Info to Client
// Table: incident | When: display

(function executeRule(current, previous) {
    g_scratchpad.isVIP = false;
    if (!current.isNewRecord() && !gs.nil(current.getValue('caller_id'))) {
        var caller = new GlideRecord('sys_user');
        if (caller.get(current.getValue('caller_id'))) {
            g_scratchpad.isVIP = caller.getValue('vip') == 'true';
            g_scratchpad.callerLocation = caller.getDisplayValue('location');
        }
    }
})(current, previous);
```

### current vs previous
```javascript
// previous is only available in Update rules (before/after)
if (current.state.changes()) {
    gs.info('State changed from ' + previous.state + ' to ' + current.state);
}
// previous is READ-ONLY — never modify it
// previous is NOT available in async rules after a short delay (data may change)
```

## Script Includes

### Standard Pattern (Class Prototype)
```javascript
var IncidentUtils = Class.create();
IncidentUtils.prototype = {
    initialize: function() {
        // constructor
    },
    
    getActiveCount: function(assignmentGroup) {
        var ga = new GlideAggregate('incident');
        ga.addActiveQuery();
        ga.addQuery('assignment_group', assignmentGroup);
        ga.addAggregate('COUNT');
        ga.query();
        if (ga.next()) return parseInt(ga.getAggregate('COUNT'));
        return 0;
    },
    
    reassignIncident: function(incidentId, newAssignee) {
        var gr = new GlideRecord('incident');
        if (gr.get(incidentId)) {
            gr.setValue('assigned_to', newAssignee);
            return gr.update();
        }
        return null;
    },
    
    type: 'IncidentUtils'
};

// Usage:
var util = new IncidentUtils();
var count = util.getActiveCount(groupSysId);
```

### Client-Callable Script Include (for GlideAjax)
```javascript
// Check "Client callable" checkbox in Script Include form
var ClientUtils = Class.create();
ClientUtils.prototype = Object.extendsObject(AbstractAjaxProcessor, {
    
    // Each method accessible via GlideAjax sysparm_name
    validateEmail: function() {
        var email = this.getParameter('sysparm_email');
        var gr = new GlideRecord('sys_user');
        gr.addQuery('email', email);
        gr.setLimit(1);
        gr.query();
        return gr.hasNext().toString(); // must return string
    },
    
    getUserGroups: function() {
        var userId = this.getParameter('sysparm_user_id');
        var groups = [];
        var gr = new GlideRecord('sys_user_grmember');
        gr.addQuery('user', userId);
        gr.query();
        while (gr.next()) {
            groups.push({
                sys_id: gr.getValue('group'),
                name: gr.getDisplayValue('group')
            });
        }
        return JSON.stringify(groups);
    },
    
    type: 'ClientUtils'
});
```

### Extending Base Classes
```javascript
var CustomApprovalUtils = Class.create();
CustomApprovalUtils.prototype = Object.extendsObject(ApprovalUtils, {
    
    initialize: function() {
        ApprovalUtils.prototype.initialize.call(this);
        this.customConfig = gs.getProperty('my_app.approval_config');
    },
    
    getApproversByAmount: function(amount) {
        // Custom logic on top of base class
        if (amount > 10000) return this._getVPApprovers();
        return this._getManagerApprovers();
    },
    
    _getVPApprovers: function() {
        // private method by convention (underscore prefix)
        var approvers = [];
        // ... logic
        return approvers;
    },
    
    type: 'CustomApprovalUtils'
});
```

## Client Scripts

### onChange
```javascript
// Type: onChange | Table: incident | Field: category
function onChange(control, oldValue, newValue, isLoading, isTemplate) {
    if (isLoading || newValue == '') return;
    
    // Clear subcategory when category changes
    g_form.setValue('subcategory', '');
    
    // Make certain fields mandatory based on category
    if (newValue == 'network') {
        g_form.setMandatory('cmdb_ci', true);
        g_form.setVisible('u_network_segment', true);
    } else {
        g_form.setMandatory('cmdb_ci', false);
        g_form.setVisible('u_network_segment', false);
    }
}
```

### onLoad
```javascript
// Type: onLoad | Table: incident
function onLoad() {
    // Access Display BR data via g_scratchpad
    if (g_scratchpad.isVIP) {
        g_form.showFieldMsg('caller_id', 'This is a VIP caller!', 'info');
        g_form.setMandatory('priority', true);
    }
    
    // New record defaults
    if (g_form.isNewRecord()) {
        g_form.setValue('contact_type', 'self-service');
    }
}
```

### onSubmit
```javascript
// Type: onSubmit | Table: incident
function onSubmit() {
    var desc = g_form.getValue('short_description');
    if (desc.length < 10) {
        g_form.addErrorMessage('Short description must be at least 10 characters.');
        return false; // prevent submission
    }
    
    // Confirm before submission
    if (g_form.getValue('state') == '7') { // Closed
        return confirm('Are you sure you want to close this incident?');
    }
    
    return true; // allow submission
}
```

### onCellEdit (list editing)
```javascript
// Type: onCellEdit | Table: incident
function onCellEdit(sysIDs, table, oldValues, newValue, callback) {
    // sysIDs is array of selected record sys_ids
    // Prevent bulk priority change to Critical
    if (newValue == '1' && sysIDs.length > 1) {
        callback({
            status: 'error',
            error_message: 'Cannot bulk-change priority to Critical'
        });
        return false;
    }
    callback({ status: 'success' });
    return true;
}
```

## UI Policies

### Script-based UI Policy
```javascript
// Run script: true
// Execute on: onLoad, onChange
// Applies to field: short_description

function onCondition() {
    // Dynamic condition beyond simple field checks
    var priority = g_form.getValue('priority');
    var category = g_form.getValue('category');
    return (priority == '1' && category == 'network');
}

function onTrue() {
    g_form.setMandatory('cmdb_ci', true);
    g_form.setVisible('u_network_impact', true);
}

function onFalse() {
    g_form.setMandatory('cmdb_ci', false);
    g_form.setVisible('u_network_impact', false);
}
```

## UI Actions

### Form Button — Client + Server
```javascript
// Name: Escalate to Major
// Table: incident | Form button: true | List button: false
// Condition: current.priority != '1' && gs.hasRole('itil')

// Client Script (runs first):
function escalateToMajor() {
    if (!confirm('Escalate this incident to Major Incident?')) return;
    
    // Set fields before server script runs
    g_form.setValue('priority', '1');
    gsftSubmit(null, g_form.getFormElement(), 'escalate_major');
}

// Server Script (runs after client):
if (typeof RP != 'undefined' && RP.isDialog()) {
    // Handle dialog context
}
current.setValue('priority', '1');
current.setValue('state', '2'); // In Progress
gs.eventQueue('incident.escalated', current, gs.getUserID(), current.getValue('number'));
gs.addInfoMessage('Incident escalated to Major Incident');
current.update();
action.setRedirectURL(current);
```

### List Context UI Action
```javascript
// Name: Assign to Me (List)
// Table: incident | Form button: false | List button: true | List choice: true

// Server Script:
var selected = RP.getParameterValue('sysparm_checked_items');
if (!gs.nil(selected)) {
    var ids = selected.split(',');
    for (var i = 0; i < ids.length; i++) {
        var sysId = ids[i].split('.').pop(); // format: table.sys_id
        var gr = new GlideRecord('incident');
        if (gr.get(sysId)) {
            gr.setValue('assigned_to', gs.getUserID());
            gr.update();
        }
    }
    gs.addInfoMessage(ids.length + ' incident(s) assigned to you');
}
action.setRedirectURL(current);
```

## Scheduled Jobs

```javascript
// Script field of Scheduled Job record
// Runs on schedule — no current/previous object

var cutoffDate = gs.daysAgoStart(30);
var gr = new GlideRecord('incident');
gr.addQuery('state', '6'); // Resolved
gr.addQuery('resolved_at', '<', cutoffDate);
gr.query();

var count = 0;
while (gr.next()) {
    gr.setValue('state', '7'); // Closed
    gr.setValue('close_notes', 'Auto-closed after 30 days in resolved state.');
    gr.update();
    count++;
}
gs.info('Auto-close job: closed ' + count + ' incidents');
```

## Fix Scripts (one-time data fixes)

```javascript
// Name: Migrate Category Values
// ALWAYS test in sub-prod first!

var gr = new GlideRecord('incident');
gr.addQuery('category', 'old_category');
gr.query();

var count = 0;
var batchSize = 500;

while (gr.next()) {
    gr.setValue('category', 'new_category');
    gr.setWorkflow(false);     // don't trigger business rules
    gr.autoSysFields(false);   // don't update sys_updated_on
    gr.update();
    count++;
    
    // Log progress for long-running scripts
    if (count % batchSize === 0) {
        gs.info('Migrated ' + count + ' records...');
    }
}
gs.info('Migration complete: ' + count + ' records updated');
```

## Event-Driven Architecture

### Register Event (sys_event_register)
```
Event name: incident.escalated
Table: incident
Fired by: Business Rule / Script
```

### Script Action (fires on event)
```javascript
// Table: incident
// Event: incident.escalated
// Script:

var incident = event.GlideRecord;
var escalatedBy = event.parm1;  // gs.getUserID() from eventQueue
var incNumber = event.parm2;    // incident number from eventQueue

// Notify on-call manager
var mgr = new OnCallManager();
mgr.notifyManager(incident.getValue('assignment_group'), 
    'Major incident escalation: ' + incNumber);

// Create communication task
var task = new GlideRecord('sn_major_inc_comm_task');
task.initialize();
task.setValue('incident', incident.getUniqueValue());
task.setValue('short_description', 'Stakeholder communication for ' + incNumber);
task.insert();
```

### Firing Events
```javascript
// In Business Rule or Script Include:
gs.eventQueue('incident.escalated', current, gs.getUserID(), current.getValue('number'));

// Delayed event (fires after 60 seconds)
gs.eventQueueScheduled('incident.followup', current, '', '', 
    new GlideDateTime(gs.minutesAgo(-1)));
```
