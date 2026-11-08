# Glide API Quick Reference

## GlideRecord

### Basic Query
```javascript
var gr = new GlideRecord('incident');
gr.addQuery('active', true);
gr.addQuery('priority', '1');
gr.orderByDesc('sys_created_on');
gr.setLimit(50);
gr.query();
while (gr.next()) {
    gs.info(gr.getValue('number') + ': ' + gr.getValue('short_description'));
}
```

### Encoded Query (preferred for complex filters)
```javascript
var gr = new GlideRecord('incident');
gr.addEncodedQuery('active=true^priority=1^assigned_toISNOTEMPTY^sys_created_on>=javascript:gs.beginningOfLastMonth()');
gr.query();
```

### Get Single Record
```javascript
var gr = new GlideRecord('incident');
if (gr.get('number', 'INC0010001')) {  // query by field
    gs.info(gr.getValue('short_description'));
}

// By sys_id (most common)
if (gr.get('a1b2c3d4...')) {  // returns boolean in scoped apps!
    gs.info(gr.getValue('number'));
}
```

### Insert
```javascript
var gr = new GlideRecord('incident');
gr.initialize();
gr.setValue('short_description', 'New incident from script');
gr.setValue('caller_id', gs.getUserID());
gr.setValue('category', 'software');
gr.setValue('impact', '2');
gr.setValue('urgency', '2');
var sys_id = gr.insert(); // returns sys_id or null
```

### Update
```javascript
var gr = new GlideRecord('incident');
gr.addQuery('number', 'INC0010001');
gr.query();
if (gr.next()) {
    gr.setValue('state', '6'); // Resolved
    gr.setValue('close_code', 'Solved (Permanently)');
    gr.setValue('close_notes', 'Fixed by applying patch.');
    gr.update();
}
```

### Delete
```javascript
var gr = new GlideRecord('incident');
gr.addQuery('active', false);
gr.addQuery('sys_created_on', '<', gs.daysAgoStart(365));
gr.setLimit(1000); // batch delete
gr.query();
while (gr.next()) {
    gr.deleteRecord();
}
```

### Update Multiple (no Business Rules fired)
```javascript
var gr = new GlideRecord('incident');
gr.addQuery('assignment_group', oldGroupId);
gr.setValue('assignment_group', newGroupId);
gr.updateMultiple(); // WARNING: skips Business Rules
```

### Delete Multiple
```javascript
var gr = new GlideRecord('incident');
gr.addQuery('active', false);
gr.addQuery('sys_created_on', '<', gs.daysAgoStart(365));
gr.deleteMultiple(); // WARNING: skips Business Rules
```

### addJoinQuery (find records with related data)
```javascript
// Find incidents that have attachments
var gr = new GlideRecord('incident');
gr.addJoinQuery('sys_attachment', 'sys_id', 'table_sys_id');
gr.query();

// Find users in a specific group
var gr = new GlideRecord('sys_user');
var joinQuery = gr.addJoinQuery('sys_user_grmember', 'sys_id', 'user');
joinQuery.addCondition('group.name', 'Network');
gr.query();
```

### addNotNullQuery / addNullQuery
```javascript
gr.addNotNullQuery('assigned_to');
gr.addNullQuery('resolved_at');
```

### OR Queries
```javascript
var gr = new GlideRecord('incident');
var qc = gr.addQuery('priority', '1');
qc.addOrCondition('priority', '2');
gr.query();

// Better: encoded query
gr.addEncodedQuery('priority=1^ORpriority=2');
```

### Dot-walking (reference fields)
```javascript
var gr = new GlideRecord('incident');
if (gr.get('some_sys_id')) {
    // Dot-walk only for reads
    var email = gr.getValue('caller_id.email'); // not for writes
    var callerName = gr.getDisplayValue('caller_id');
}

// For setting references, use sys_id
gr.setValue('assigned_to', userSysId);
```

### chooseWindow (pagination)
```javascript
var gr = new GlideRecord('incident');
gr.addActiveQuery();
gr.orderByDesc('sys_created_on');
gr.chooseWindow(0, 20); // first 20 records (offset, limit)
gr.query();
```

### setWorkflow / autoSysFields
```javascript
var gr = new GlideRecord('incident');
if (gr.get(sys_id)) {
    gr.setWorkflow(false);   // skip Business Rules
    gr.autoSysFields(false);  // don't update sys_updated_on/by
    gr.setValue('state', '7');
    gr.update();
}
```

## GlideAggregate

```javascript
// Count active incidents by priority
var ga = new GlideAggregate('incident');
ga.addActiveQuery();
ga.addAggregate('COUNT');
ga.groupBy('priority');
ga.query();
while (ga.next()) {
    gs.info('Priority ' + ga.getValue('priority') + ': ' + ga.getAggregate('COUNT'));
}

// Sum, AVG, MIN, MAX
var ga = new GlideAggregate('incident');
ga.addAggregate('AVG', 'reassignment_count');
ga.addAggregate('MAX', 'reassignment_count');
ga.query();
if (ga.next()) {
    gs.info('Avg reassignments: ' + ga.getAggregate('AVG', 'reassignment_count'));
    gs.info('Max reassignments: ' + ga.getAggregate('MAX', 'reassignment_count'));
}

// Count with having clause
var ga = new GlideAggregate('incident');
ga.addActiveQuery();
ga.addAggregate('COUNT');
ga.groupBy('assigned_to');
ga.addHaving('COUNT', '>', 10);
ga.query();
```

## GlideSystem (gs)

```javascript
// User info
gs.getUserID();           // sys_id of current user
gs.getUserName();         // username
gs.getUserDisplayName();  // full name
gs.getUser().getRecord(); // GlideRecord of sys_user

// Roles
gs.hasRole('admin');
gs.hasRole('itil');

// Properties
gs.getProperty('glide.servlet.uri');  // instance URL
gs.getProperty('my_app.custom_prop', 'default_value');

// Logging
gs.info('Info message: {0}', paramValue);
gs.warn('Warning: {0}', paramValue);
gs.error('Error: {0}', paramValue);
gs.debug('Debug: {0}', paramValue);  // only shows if debug enabled

// Events
gs.eventQueue('my_app.event_name', current, param1, param2);

// Date/Time helpers
gs.now();                    // current date/time
gs.nowDateTime();            // current date/time string
gs.daysAgo(7);              // date/time 7 days ago
gs.daysAgoStart(7);         // start of day 7 days ago
gs.daysAgoEnd(7);           // end of day 7 days ago
gs.beginningOfLastMonth();
gs.endOfLastMonth();
gs.beginningOfThisQuarter();

// Misc
gs.nil(value);              // true if null, undefined, or empty string
gs.tableExists('my_table');
gs.sleep(1000);             // pause 1 second (server-side only, use sparingly!)
gs.getSession();            // current session object
gs.setRedirect('incident.do?sys_id=' + sys_id);
gs.addInfoMessage('Record saved successfully');
gs.addErrorMessage('Something went wrong');
```

## GlideAjax (Client → Server)

### Client Script (caller)
```javascript
// ASYNC (preferred) — uses callback
var ga = new GlideAjax('MyAjaxUtil');
ga.addParam('sysparm_name', 'getIncidentInfo');
ga.addParam('sysparm_incident_id', g_form.getValue('sys_id'));
ga.getXMLAnswer(function(answer) {
    var result = JSON.parse(answer);
    g_form.setValue('description', result.description);
});

// NEVER use getXMLWait() — blocks the UI thread
```

### Script Include (server-side handler)
```javascript
var MyAjaxUtil = Class.create();
MyAjaxUtil.prototype = Object.extendsObject(AbstractAjaxProcessor, {
    
    getIncidentInfo: function() {
        var incId = this.getParameter('sysparm_incident_id');
        var gr = new GlideRecord('incident');
        if (gr.get(incId)) {
            var result = {
                description: gr.getValue('short_description'),
                state: gr.getValue('state'),
                priority: gr.getValue('priority')
            };
            return JSON.stringify(result);
        }
        return JSON.stringify({ error: 'Not found' });
    },
    
    // Return multiple values using XML (legacy pattern)
    getUserDetails: function() {
        var userId = this.getParameter('sysparm_user_id');
        var gr = new GlideRecord('sys_user');
        if (gr.get(userId)) {
            this.setAnswer(gr.getValue('name'));
            // Additional values via newItem
            var item = this.newItem('email');
            item.setAttribute('value', gr.getValue('email'));
        }
    },
    
    type: 'MyAjaxUtil'
});
```

## GlideForm (g_form) — Client-Side Only

```javascript
// Get/Set values
g_form.getValue('field_name');          // internal value
g_form.getDisplayValue('field_name');   // display value
g_form.setValue('field_name', 'value'); // set value
g_form.setValue('field_name', sys_id, displayValue); // reference field with display
g_form.clearValue('field_name');

// Visibility & Read-only
g_form.setVisible('field_name', true);
g_form.setReadOnly('field_name', true);
g_form.setMandatory('field_name', true);
g_form.setDisabled('field_name', true);

// Labels & Styles
g_form.setLabelOf('field_name', 'New Label');
g_form.showFieldMsg('field_name', 'Warning message', 'error'); // 'info', 'error'
g_form.hideFieldMsg('field_name');

// Options (choice fields)
g_form.addOption('priority', '6', 'Planning');
g_form.removeOption('priority', '5');
g_form.clearOptions('priority');

// Sections
g_form.setSectionDisplay('section_name', false); // hide section

// Form-level
g_form.save();      // save without redirect
g_form.submit();    // save and redirect
g_form.isNewRecord();
g_form.addInfoMessage('Saved!');
g_form.addErrorMessage('Failed!');
g_form.flash('field_name', '#FFFACD', 0); // flash field

// Related lists
g_form.showRelatedList('incident.problem_id');
g_form.hideRelatedList('incident.problem_id');
```

## GlideUser (server-side)

```javascript
var user = gs.getUser();
user.getID();              // sys_id
user.getName();            // username
user.getDisplayName();     // full name
user.getEmail();           // email
user.getDomainID();        // domain sys_id
user.hasRole('itil');
user.isMemberOf('Database');  // group name
user.getMyGroups();        // comma-separated sys_ids

// From GlideRecord
var gr = new GlideRecord('sys_user');
gr.get(gs.getUserID());
gr.getValue('department');
```

## GlideDateTime & GlideDuration

```javascript
// GlideDateTime
var gdt = new GlideDateTime();  // now
gdt.getValue();                  // internal format: 2024-01-15 14:30:00
gdt.getDisplayValue();           // user's timezone format
gdt.getNumericValue();           // epoch milliseconds

var gdt = new GlideDateTime('2024-01-15 14:30:00');
gdt.addDaysUTC(7);
gdt.addSeconds(3600);

// Compare
var gdt1 = new GlideDateTime('2024-01-15');
var gdt2 = new GlideDateTime('2024-01-20');
gs.info(gdt1.before(gdt2)); // true
gs.info(gdt1.after(gdt2));  // false

// Calculate duration between dates
var start = new GlideDateTime(gr.getValue('opened_at'));
var end = new GlideDateTime(gr.getValue('resolved_at'));
var dur = GlideDateTime.subtract(start, end);
gs.info(dur.getDurationValue()); // "3 00:15:30" (days HH:MM:SS)

// GlideDuration
var dur = new GlideDuration('3 00:00:00'); // 3 days
dur.add(new GlideDuration('0 12:00:00')); // add 12 hours
gs.info(dur.getDurationValue());
```

## GlideSPScriptable (Service Portal)

```javascript
// In a Service Portal widget server script
(function() {
    var sp = new GlideSPScriptable();
    
    // Get portal record
    var portalGR = sp.getPortalRecord();
    
    // Get current user
    data.user = sp.getUserRecord().getDisplayValue('name');
    
    // Get KB article
    var kb = sp.getKBRecord('KB0010001');
    
    // Check catalog item visibility
    var canView = sp.canReadRecord('sc_cat_item', itemSysId);
    
    // Get widget parameters
    data.title = options.title || 'Default Title';
})();
```

## Scoped vs Global Differences

| Feature | Global | Scoped |
|---------|--------|--------|
| `gr.field_name` | Returns value (string coercion) | Returns GlideElement |
| `gr.get()` return | GlideRecord or null | boolean |
| `gs.include()` | Available | NOT available — use Script Includes |
| `GlideSecureRandomUtil` | Global namespace | Scoped namespace |
| `current.update()` | Works (but avoid in BR) | Works (but avoid in BR) |
| Cross-scope access | Unrestricted | Requires access rules |
| `GlideEvaluator` | Available | Available (own scope) |
| `gs.log()` | Available | Use `gs.info()` instead |

### Scoped App Best Practice
```javascript
// Always use getValue/setValue in scoped apps
var value = gr.getValue('field'); // ✅ returns string
var value = gr.field;             // ❌ returns GlideElement object

// Check get() result
var gr = new GlideRecord('incident');
if (gr.get(sysId)) {  // boolean in scoped
    // record found
}
```
